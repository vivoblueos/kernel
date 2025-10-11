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
use crate::{
    allocator,
    config::MAX_THREAD_PRIORITY,
    net::{
        connection::Connection,
        net_interface::NetInterface,
        socket::{icmp::IcmpSocket, tcp::TcpSocket, udp::UdpSocket, PosixSocket},
        SocketDomain, SocketFd, SocketProtocol, SocketType,
    },
    scheduler,
    thread::{self, Builder as ThreadBuilder, Entry, Stack, SystemThreadStorage, ThreadNode},
    time::{tick_from_millisecond, tick_get_millisecond},
};
use alloc::{
    boxed::Box,
    collections::btree_map::BTreeMap,
    rc::Rc,
    string::{String, ToString},
    vec::Vec,
};
use blueos_kconfig::NETWORK_STACK_SIZE;
use core::{cell::RefCell, mem::MaybeUninit, time};
use smoltcp::{
    time::{Duration, Instant},
    wire::{IpAddress, IpEndpoint},
};

const DEFAULT_DELAY_TIME_IN_MILLIS: u64 = 100;

pub struct NetworkManager<'a> {
    net_interfaces: Vec<Rc<RefCell<NetInterface<'a>>>>,
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

        Self {
            net_interfaces,
            socket_maps,
            default_interface,
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

    pub fn loop_within_single_thread<F>(
        network_manager: Rc<RefCell<NetworkManager<'static>>>,
        timeout_millis: usize,
        mut f: F,
    ) where
        F: FnMut(Rc<RefCell<NetworkManager<'a>>>) -> bool,
    {
        let is_forever = timeout_millis == 0;
        let timeout = tick_get_millisecond() + timeout_millis;
        log::trace!(
            "[NetworkManager] start with timeout_millis={} timeout={}",
            timeout_millis,
            timeout
        );

        let net_manager = network_manager.clone();

        // Loop for request finish
        while is_forever || tick_get_millisecond() < timeout {
            // Step1 : poll smoltcp network stack
            {
                let network_manager = network_manager.borrow();

                if let Err(e) = network_manager.net_interfaces.iter().try_for_each(
                    |interface| -> Result<(), String> {
                        let millis_i64 =
                            i64::try_from(tick_get_millisecond()).map_err(|e| e.to_string())?;
                        interface
                            .borrow_mut()
                            .poll(Instant::from_millis(millis_i64));
                        Ok(())
                    },
                ) {
                    log::error!("[NetworkManager]: looper exit with poll error {}", e);
                    break;
                } else {
                    // Do nothing and just continue when poll success
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
                        let Ok(millis_i64) = i64::try_from(tick_get_millisecond()) else {
                            log::error!("[NetworkManager]: Interface poll_delay get ms fail");
                            return DEFAULT_DELAY_TIME_IN_MILLIS;
                        };

                        match interface
                            .borrow_mut()
                            .poll_delay(Instant::from_millis(millis_i64))
                        {
                            Some(Duration::ZERO) => {
                                log::debug!("[NetworkManager]: Inteface resuming");
                                // Do next poll immediately
                                0
                            }
                            Some(delay) => {
                                log::debug!("[NetworkManager]: Inteface poll delay for {}", delay);
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
                    .min()
                    .unwrap_or(DEFAULT_DELAY_TIME_IN_MILLIS);

                // Warning!!! Need to yield or sleep for a while , or other threads may have no change to insert msg to NETSTACK_QUEUE
                if sleep_time == 0 {
                    scheduler::yield_me();
                } else {
                    scheduler::suspend_me_for(tick_from_millisecond(
                        sleep_time.min(DEFAULT_DELAY_TIME_IN_MILLIS) as usize,
                    ));
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
    pub(crate) rep: [u8; NETWORK_STACK_SIZE],
}

static mut NETWORK_STACK: NetworkStack = NetworkStack {
    rep: [0u8; NETWORK_STACK_SIZE],
};

pub(crate) fn init() {
    let t = ThreadBuilder::new(Entry::C(net_stack_main_loop))
        .set_stack(Stack::from_raw(
            NETWORK_STACK.rep.as_mut_ptr(),
            NETWORK_STACK_SIZE,
        ))
        .start();
}
