// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#[cfg(virtio)]
use crate::devices::net::virtio_net_device::net_dev_exist;
#[cfg(virtio)]
use crate::net::link::virtio::VirtioLink;
use crate::{
    allocator,
    config::MAX_THREAD_PRIORITY,
    net::{
        connection::Connection,
        iface::{
            control::{InterfaceFlags, NetIfaceControl, NetIfaceError, NetIfaceResult},
            NetIface,
        },
        link::{loopback::LoopbackLink, LinkKind, LinkLayer, LINK_REGISTRY},
        protocol::{iana, PROTOCOL_REGISTRY},
        socket::PosixSocket,
        SocketDomain, SocketFd, SocketProtocol, SocketType,
    },
    scheduler,
    support::Storage,
    thread::{self, Builder as ThreadBuilder, Entry, Stack, SystemThreadStorage, ThreadNode},
    time as sysclk,
    time::Tick,
};
use alloc::{
    boxed::Box,
    collections::btree_map::BTreeMap,
    rc::Rc,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};
use blueos_kconfig::CONFIG_NETWORK_STACK_SIZE as NETWORK_STACK_SIZE;
use core::{cell::RefCell, mem::MaybeUninit, time};
use smoltcp::{
    time::{Duration, Instant},
    wire::{IpAddress, IpEndpoint},
};
use spin;

const DEFAULT_DELAY_TIME_IN_MILLIS: u64 = 100;

pub struct NetworkManager {
    net_ifaces: Vec<Rc<NetIface>>,
    socket_maps: BTreeMap<SocketFd, Rc<RefCell<dyn PosixSocket>>>,
    default_net_iface: Option<Rc<NetIface>>,
}

impl NetworkManager {
    // Using Rc<RefCell<T>> while `static T` need T to impl Sync in rust
    pub fn init() -> Rc<RefCell<NetworkManager>> {
        let manager = NetworkManager::new();
        Rc::new(RefCell::new(manager))
    }

    // It will only access by a standalone tcp/ip stack thread, so no need for Critical Section .
    fn new() -> Self {
        let mut net_ifaces = Vec::new();
        let socket_maps = BTreeMap::new();
        let mut default_net_iface = None;

        // Add Loopback interface which always exist
        let link_rwlock =
            Arc::new(spin::RwLock::new(LoopbackLink::new())) as Arc<spin::RwLock<dyn LinkLayer>>;
        let lo_iface = Rc::new(NetIface::new("lo".into(), link_rwlock, 0));
        net_ifaces.push(lo_iface.clone());
        default_net_iface.replace(lo_iface);
        log::debug!("Add NetIface(Lo)");

        // Add other interfaces which may not exist
        #[cfg(virtio)]
        if net_dev_exist() {
            // Create NetIface for virtio-net
            let virtio_iface = Rc::new(NetIface::new(
                "virtio-net".into(),
                Arc::new(spin::RwLock::new(VirtioLink::new(0))) as Arc<spin::RwLock<dyn LinkLayer>>,
                1,
            ));
            net_ifaces.push(virtio_iface.clone());
            default_net_iface.replace(virtio_iface);
            log::debug!("Add NetIface(Virtio)");
        }

        Self {
            net_ifaces,
            socket_maps,
            default_net_iface,
        }
    }

    #[allow(dead_code)]
    /// Create an Arc<RwLock<dyn LinkLayer>> from a LinkLayer trait object.
    /// Returns a fresh concrete instance matching the link kind.
    fn create_link_from_registry(link: &dyn LinkLayer) -> Option<Arc<spin::RwLock<dyn LinkLayer>>> {
        match link.kind() {
            LinkKind::Loopback => {
                let concrete = LoopbackLink::new();
                Some(Arc::new(spin::RwLock::new(concrete)))
            }
            LinkKind::Virtio => {
                #[cfg(virtio)]
                {
                    let concrete = VirtioLink::new(0);
                    Some(Arc::new(spin::RwLock::new(concrete)))
                }
                #[cfg(not(virtio))]
                {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn create_posix_socket(
        &mut self,
        socket_fd: SocketFd,
        network_manager: Rc<RefCell<NetworkManager>>,
        socket_domain: SocketDomain,
        socket_type: SocketType,
        socket_protocol: SocketProtocol,
    ) -> SocketFd {
        // ProtocolRegistry dispatch: delegate to Protocol::create_socket()
        //
        // FIXME: IANA=0 (IPPROTO_IP) or 41 (IPPROTO_IPV6) means "default protocol"
        // — resolve based on socket_type: SOCK_STREAM → TCP (6), SOCK_DGRAM → UDP (17),
        // SOCK_RAW → ICMP (1).
        // This is a workaround for callers that pass IPPROTO_IP/IPPROTO_IPV6 instead of
        // the actual protocol number. A proper fix would enforce the correct protocol
        // at the socket() syscall level.
        let iana_proto = match socket_protocol.iana() {
            0 | 41 => match socket_type {
                SocketType::SockStream => iana::TCP,
                SocketType::SockDgram => iana::UDP,
                SocketType::SockRaw => iana::ICMP,
                _ => {
                    log::error!("No default protocol for socket_type={}", socket_type);
                    return -1;
                }
            },
            n => n,
        };
        if let Some(protocol) = PROTOCOL_REGISTRY.get_by_key(socket_type, iana_proto) {
            match protocol.create_socket(socket_fd, socket_domain, network_manager.clone()) {
                Ok(socket) => {
                    self.socket_maps.insert(socket_fd, socket);
                    return socket_fd;
                }
                Err(e) => {
                    log::error!(
                        "[NetManager] Protocol {} create_socket failed: {:?}",
                        protocol.name(),
                        e
                    );
                    return -1;
                }
            }
        }

        log::error!(
            "No registered protocol for socket_type={}, protocol={:#?} (iana={})",
            socket_type,
            socket_protocol,
            iana_proto,
        );
        -1
    }

    pub fn get_posix_socket(
        &self,
        socket_fd: SocketFd,
    ) -> Option<Rc<RefCell<dyn PosixSocket + 'static>>> {
        self.socket_maps.get(&socket_fd).cloned()
    }

    pub fn bind_defualt_smoltcp_interface(&self, socket_fd: SocketFd) {
        if let Some(socket) = self.socket_maps.get(&socket_fd) {
            // Use default net interface when we find no subnet match with remote_addr
            if let Some(interface) = self.default_net_iface.clone() {
                let mut socket = socket.borrow_mut();
                socket.bind_interface(interface.clone());
                log::debug!("Socket Fd={} binding to {}", socket_fd, interface);
            } else {
                log::error!("Socket Fd={} binding fail, find no interface", socket_fd);
            }
        }
    }

    pub fn bind_smoltcp_interface(&self, socket_fd: SocketFd, binding_addr: IpAddress) {
        if let Some(socket) = self.socket_maps.get(&socket_fd) {
            self.net_ifaces
                .iter()
                .find(|iface| iface.contains_addr(binding_addr))
                .map_or_else(
                    || {
                        // Use default net interface when we find no subnet match with remote_addr
                        if let Some(interface) = self.default_net_iface.clone() {
                            let mut socket = socket.borrow_mut();
                            socket.bind_interface(interface.clone());
                            log::debug!("Socket Fd={} binding to {}", socket_fd, interface);
                        } else {
                            log::error!("Socket Fd={} binding fail, find no interface", socket_fd);
                        }
                    },
                    |iface| {
                        // Otherwise choose the match net interface
                        let mut socket = socket.borrow_mut();
                        socket.bind_interface(iface.clone());
                        log::debug!("Socket Fd={} binding to {}", socket_fd, iface);
                    },
                )
        }
    }

    /// Handle a type-safe network control command.
    ///
    /// Bridges the POSIX ioctl path (via `Operation::NetControl`) to the
    /// new `NetIface::control()` method. Uses the first available link
    /// device from `LINK_REGISTRY`.
    ///
    /// Phase 0: this creates a transient `NetIface` wrapping the link.
    /// In a later phase `NetIface` instances will be persistent in
    /// `NetworkManager`.
    pub fn handle_net_control(
        &self,
        cmd: NetIfaceControl,
    ) -> Result<NetIfaceResult, NetIfaceError> {
        let link_arc = LINK_REGISTRY.get(0).ok_or(NetIfaceError::DeviceNotFound)?;

        // Phase 0: for now, only handle simple queries that don't require
        // a full NetIface. The NetIface construction with RwLock<dyn LinkLayer>
        // requires concrete type ownership which we don't have from the Arc.
        // Full NetIface dispatch will be wired in Step 8.
        match cmd {
            NetIfaceControl::GetFlags => Ok(NetIfaceResult::Flags(InterfaceFlags {
                up: link_arc.can_send() || link_arc.can_recv(),
                running: true,
                promiscuous: false,
            })),
            NetIfaceControl::GetMacAddress => {
                let hw = link_arc
                    .hw_addr()
                    .and_then(|h| h.as_ethernet())
                    .unwrap_or([0u8; 6]);
                Ok(NetIfaceResult::MacAddress(hw))
            }
            NetIfaceControl::GetMtu => Ok(NetIfaceResult::Mtu(link_arc.mtu())),
            NetIfaceControl::GetLinkKind => Ok(NetIfaceResult::LinkKind(link_arc.kind())),
            _ => Err(NetIfaceError::NotSupported),
        }
    }

    pub fn loop_within_single_thread<F>(
        network_manager: Rc<RefCell<NetworkManager>>,
        timeout_millis: usize,
        mut f: F,
    ) where
        F: FnMut(Rc<RefCell<NetworkManager>>) -> bool,
    {
        let is_forever = timeout_millis == 0;
        let timeout = sysclk::now().as_millis() as usize + timeout_millis;
        log::trace!(
            "[NetworkManager] start with timeout_millis={} timeout={}",
            timeout_millis,
            timeout
        );

        let net_manager = network_manager.clone();

        // Loop for request finish
        while is_forever || (sysclk::now().as_millis() as usize) < timeout {
            // Step1 : poll smoltcp network stack
            {
                let network_manager = network_manager.borrow();

                // Phase 2a: poll NetIface instances (they bridge to NetInterface
                // via bridge_iface, so the underlying smoltcp state is shared).
                // Replaces the old net_interfaces direct poll.
                if let Ok(millis_i64) = i64::try_from(sysclk::now().as_millis()) {
                    for iface in network_manager.net_ifaces.iter() {
                        iface.poll(Instant::from_millis(millis_i64));
                    }
                }
            }

            // Step 2 : handle msg from event queue
            if !f(net_manager.clone()) {
                log::warn!("[NetworkManager]: looper exit");
                break;
            }

            // Step3 : get next poll time from smoltcp network stack
            {
                let network_manager = network_manager.borrow();
                let sleep_time = network_manager
                    .net_ifaces
                    .iter()
                    .map(|iface| {
                        let Ok(millis_i64) = i64::try_from(sysclk::now().as_millis()) else {
                            return DEFAULT_DELAY_TIME_IN_MILLIS;
                        };
                        match iface.poll_delay(Instant::from_millis(millis_i64)) {
                            Some(smoltcp::time::Duration::ZERO) => 0,
                            Some(delay) => delay.millis() as u64,
                            None => DEFAULT_DELAY_TIME_IN_MILLIS,
                        }
                    })
                    .min()
                    .unwrap_or(DEFAULT_DELAY_TIME_IN_MILLIS);

                // Warning!!! Need to yield or sleep for a while , or other threads may have no chance to insert msg to NETSTACK_QUEUE
                if sleep_time == 0 {
                    scheduler::suspend_me_for::<()>(Tick(1), None);
                } else {
                    scheduler::suspend_me_for::<()>(
                        Tick::from_millis(sleep_time.min(DEFAULT_DELAY_TIME_IN_MILLIS) as u64),
                        None,
                    );
                }
            }
        }
    }
}

extern "C" fn net_stack_main_loop() {
    log::debug!("[NetworkManager] enter");
    let network_manager = NetworkManager::init();

    NetworkManager::loop_within_single_thread(
        network_manager.clone(),
        0,
        |network_manager: Rc<RefCell<NetworkManager>>| -> bool {
            // msg loop , one msg at a time
            Connection::handle_socket_msg(network_manager)
        },
    );

    log::debug!("[NetworkManager] exit");
}

#[repr(align(16))]
#[derive(Copy, Clone, Debug)]
pub(crate) struct NetworkStack {
    pub(crate) rep: [u8; NETWORK_STACK_SIZE as usize],
}

static mut NETWORK_STACK: NetworkStack = NetworkStack {
    rep: [0u8; NETWORK_STACK_SIZE as usize],
};

pub(crate) fn init() {
    let Some(stack) = Stack::from_raw(unsafe { NETWORK_STACK.rep.as_mut_ptr() }, unsafe {
        NETWORK_STACK.rep.len()
    }) else {
        panic!("Invalid stack");
    };
    let t = ThreadBuilder::new(Entry::C(net_stack_main_loop))
        .set_stack(stack)
        .start();
}
