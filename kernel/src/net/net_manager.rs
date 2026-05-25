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
        iface::control::{InterfaceFlags, NetIfaceControl, NetIfaceError, NetIfaceResult},
        iface::NetIface,
        iface::SmoltcpDevice,
        link::loopback::LoopbackLink,
        link::LinkKind,
        link::LinkLayer,
        link::LINK_REGISTRY,
        net_interface::NetInterface,
        protocol::{iana, PROTOCOL_REGISTRY},
        socket::{icmp::IcmpSocket, tcp::TcpSocket, udp::UdpSocket, PosixSocket},
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

pub struct NetworkManager<'a> {
    net_interfaces: Vec<Rc<RefCell<NetInterface<'a>>>>,
    net_ifaces: Vec<NetIface>,
    socket_maps: BTreeMap<SocketFd, Rc<RefCell<dyn PosixSocket>>>,
    default_interface: Option<Rc<RefCell<NetInterface<'a>>>>,
}

impl<'a> NetworkManager<'a>
where
    'a: 'static,
{
    // Using Rc<RefCell<T>> while `static T` need T to impl Sync in rust
    pub fn init() -> Rc<RefCell<NetworkManager<'a>>> {
        let manager = NetworkManager::new();
        Rc::new(RefCell::new(manager))
    }

    // It will only access by a standalone tcp/ip stack thread, so no need for Critical Section .
    fn new() -> Self {
        let mut net_interfaces = Vec::new();
        let mut net_ifaces = Vec::new();
        let socket_maps = BTreeMap::new();
        let mut default_interface = None;

        // Add Loopback interface which always exist
        let dev = NetInterface::create_loopback_interface();
        let rc = Rc::new(RefCell::new(dev));
        log::debug!("Add NetDevice : Loopback");

        net_interfaces.push(rc.clone());
        // Set loopback as default net interface
        default_interface.replace(rc);

        // Add other interfaces which may not exist
        #[cfg(virtio)]
        if net_dev_exist() {
            let dev = NetInterface::create_virtio_device();
            let rc = Rc::new(RefCell::new(dev));
            net_interfaces.push(rc.clone());

            // Using net interface other than loopback as default interface, later we need to setup default interface by net dev api
            default_interface.replace(rc);
            log::debug!("Add NetDevice : virtio-net");
        }

        // Phase 1: create persistent NetIface instances from LINK_REGISTRY
        for (idx, link_arc) in LINK_REGISTRY.iter().into_iter().enumerate() {
            let (link_for_iface, smoltcp_dev) = Self::create_link_and_device_from_registry(&*link_arc);
            if let Some((link, mut dev)) = link_for_iface.zip(smoltcp_dev) {
                let smoltcp_result = dev.create_smoltcp_iface_and_sockets();
                let iface = NetIface::new(link_arc.name(), link, dev, idx);
                if let Some((smoltcp_iface, smoltcp_sockets)) = smoltcp_result {
                    iface.set_smoltcp(smoltcp_iface, smoltcp_sockets);
                }
                net_ifaces.push(iface);
            }
        }

        Self {
            net_interfaces,
            net_ifaces,
            socket_maps,
            default_interface,
        }
    }

    /// Create an Arc<RwLock<dyn LinkLayer>> and SmoltcpDevice from a LinkLayer trait object.
    /// Both are fresh concrete instances matching the link kind.
    fn create_link_and_device_from_registry(link: &dyn LinkLayer) -> (Option<Arc<spin::RwLock<dyn LinkLayer>>>, Option<SmoltcpDevice>) {
        match link.kind() {
            LinkKind::Loopback => {
                let concrete = LoopbackLink::new();
                let link: Arc<spin::RwLock<dyn LinkLayer>> = Arc::new(spin::RwLock::new(concrete));
                (Some(link), Some(SmoltcpDevice::Loopback(LoopbackLink::new())))
            }
            LinkKind::Virtio => {
                #[cfg(virtio)]
                {
                    let concrete = VirtioLink::new(0);
                    let link: Arc<spin::RwLock<dyn LinkLayer>> = Arc::new(spin::RwLock::new(concrete));
                    (Some(link), Some(SmoltcpDevice::Virtio(VirtioLink::new(0))))
                }
                #[cfg(not(virtio))]
                {
                    (None, None)
                }
            }
            _ => (None, None),
        }
    }

    pub fn create_posix_socket(
        &mut self,
        socket_fd: SocketFd,
        network_manager: Rc<RefCell<NetworkManager<'a>>>,
        socket_domain: SocketDomain,
        socket_type: SocketType,
        socket_protocol: SocketProtocol,
    ) -> SocketFd {
        // Phase 1: try ProtocolRegistry dispatch first
        let iana_proto = socket_protocol.iana();
        if PROTOCOL_REGISTRY.contains_key(socket_type, iana_proto) {
            let socket: Rc<RefCell<dyn PosixSocket>> = match iana_proto {
                iana::TCP => {
                    Rc::new(RefCell::new(TcpSocket::new(
                        network_manager.clone(), socket_fd, socket_domain,
                    )))
                }
                iana::UDP => {
                    Rc::new(RefCell::new(UdpSocket::new(
                        network_manager.clone(), socket_fd, socket_domain,
                    )))
                }
                iana::ICMP | iana::ICMPV6 => {
                    Rc::new(RefCell::new(IcmpSocket::new(
                        network_manager.clone(), socket_fd,
                    )))
                }
                _ => return -1,
            };
            self.socket_maps.insert(socket_fd, socket);
            log::debug!("[NetManager] socket {} created via ProtocolRegistry dispatch (proto={})",
                socket_fd, iana_proto);
            return socket_fd;
        }

        // Fallback: old hardcoded path
        let socket: Rc<RefCell<dyn PosixSocket>> = match (socket_type, socket_protocol) {
            (SocketType::SockStream, _) => {
                let tcp_socket = TcpSocket::new(network_manager, socket_fd, socket_domain);
                Rc::new(RefCell::new(tcp_socket))
            }
            (SocketType::SockDgram, _) => {
                let udp_socket = UdpSocket::new(network_manager, socket_fd, socket_domain);
                Rc::new(RefCell::new(udp_socket))
            }
            (SocketType::SockRaw, SocketProtocol::Icmp)
            | (SocketType::SockRaw, SocketProtocol::Icmpv6) => {
                let icmp_socket = IcmpSocket::new(network_manager, socket_fd);
                Rc::new(RefCell::new(icmp_socket))
            }
            _ => {
                log::error!(
                    "No support socket type={}, protocol={:#?}",
                    socket_type,
                    socket_protocol
                );
                return -1;
            }
        };

        self.socket_maps.insert(socket_fd, socket);
        socket_fd
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
            if let Some(interface) = self.default_interface.clone() {
                let mut socket = socket.borrow_mut();
                socket.bind_interface(interface.clone());
                log::debug!("Socket Fd={} binding to {}", socket_fd, interface.borrow());
            } else {
                log::error!("Socket Fd={} binding fail, find no interface", socket_fd);
            }
        }
    }

    pub fn bind_smoltcp_interface(&self, socket_fd: SocketFd, binding_addr: IpAddress) {
        if let Some(socket) = self.socket_maps.get(&socket_fd) {
            self.net_interfaces
                .iter()
                .find(|dev| dev.borrow().contains_addr(binding_addr))
                .map_or_else(
                    || {
                        // Use default net interface when we find no subnet match with remote_addr
                        if let Some(interface) = self.default_interface.clone() {
                            let mut socket = socket.borrow_mut();
                            socket.bind_interface(interface.clone());
                            log::debug!(
                                "Socket Fd={} binding to {}",
                                socket_fd,
                                interface.borrow()
                            );
                        } else {
                            log::error!("Socket Fd={} binding fail, find no interface", socket_fd);
                        }
                    },
                    |dev| {
                        // Otherwise choose the match net interface
                        let mut socket = socket.borrow_mut();
                        socket.bind_interface(dev.clone());
                        log::debug!("Socket Fd={} binding to {}", socket_fd, dev.borrow());
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
    pub fn handle_net_control(&self, cmd: NetIfaceControl) -> Result<NetIfaceResult, NetIfaceError> {
        let link_arc = LINK_REGISTRY
            .get(0)
            .ok_or(NetIfaceError::DeviceNotFound)?;

        // Phase 0: for now, only handle simple queries that don't require
        // a full NetIface. The NetIface construction with RwLock<dyn LinkLayer>
        // requires concrete type ownership which we don't have from the Arc.
        // Full NetIface dispatch will be wired in Step 8.
        match cmd {
            NetIfaceControl::GetFlags => {
                Ok(NetIfaceResult::Flags(InterfaceFlags {
                    up: link_arc.can_send() || link_arc.can_recv(),
                    running: true,
                    promiscuous: false,
                }))
            }
            NetIfaceControl::GetMacAddress => {
                let hw = link_arc.hw_addr().and_then(|h| h.as_ethernet()).unwrap_or([0u8; 6]);
                Ok(NetIfaceResult::MacAddress(hw))
            }
            NetIfaceControl::GetMtu => {
                Ok(NetIfaceResult::Mtu(link_arc.mtu()))
            }
            NetIfaceControl::GetLinkKind => {
                Ok(NetIfaceResult::LinkKind(link_arc.kind()))
            }
            _ => Err(NetIfaceError::NotSupported),
        }
    }

    pub fn loop_within_single_thread<F>(
        network_manager: Rc<RefCell<NetworkManager<'static>>>,
        timeout_millis: usize,
        mut f: F,
    ) where
        F: FnMut(Rc<RefCell<NetworkManager<'a>>>) -> bool,
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

                // Old path: poll NetInterfaces (unchanged)
                if let Err(e) = network_manager.net_interfaces.iter().try_for_each(
                    |interface| -> Result<(), String> {
                        let millis_i64 =
                            i64::try_from(sysclk::now().as_millis()).map_err(|e| e.to_string())?;
                        interface
                            .borrow_mut()
                            .poll(Instant::from_millis(millis_i64));
                        Ok(())
                    },
                ) {
                    log::error!("[NetworkManager]: looper exit with poll error {}", e);
                    break;
                }

                // Phase 1: poll NetIface instances alongside old path
                // This runs in parallel with the old NetInterface poll above,
                // enabling the dual-path architecture for migration.
                if let Ok(millis_i64) = i64::try_from(sysclk::now().as_millis()) {
                    for net_iface in network_manager.net_ifaces.iter() {
                        net_iface.poll(Instant::from_millis(millis_i64));
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
                    .net_interfaces
                    .iter()
                    .map(|interface| {
                        let Ok(millis_i64) = i64::try_from(sysclk::now().as_millis()) else {
                            log::error!("[NetworkManager]: Interface poll_delay get ms fail");
                            return DEFAULT_DELAY_TIME_IN_MILLIS;
                        };

                        match interface
                            .borrow_mut()
                            .poll_delay(Instant::from_millis(millis_i64))
                        {
                            Some(Duration::ZERO) => {
                                log::debug!("[NetworkManager]: Interface resuming");
                                // Do next poll immediately
                                0
                            }
                            Some(delay) => {
                                log::debug!("[NetworkManager]: Interface poll delay for {}", delay);
                                // Do next poll after delay.millis()
                                delay.millis()
                            }
                            None => {
                                // Wait until there is a task before the next poll
                                // TODO add trigger when enqueue task
                                DEFAULT_DELAY_TIME_IN_MILLIS
                            }
                        }
                    })
                    // Phase 1: also compute delays from NetIface instances
                    .chain(
                        network_manager.net_ifaces.iter().map(|iface| {
                            let Ok(millis_i64) = i64::try_from(sysclk::now().as_millis()) else {
                                return DEFAULT_DELAY_TIME_IN_MILLIS;
                            };
                            match iface.poll_delay(Instant::from_millis(millis_i64)) {
                                Some(smoltcp::time::Duration::ZERO) => 0,
                                Some(delay) => delay.millis() as u64,
                                None => DEFAULT_DELAY_TIME_IN_MILLIS,
                            }
                        }),
                    )
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
        |network_manager: Rc<RefCell<NetworkManager<'static>>>| -> bool {
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
