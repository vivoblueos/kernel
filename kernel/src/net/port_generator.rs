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

//! port_generator.rs
//! A port generator , manage dynamic ports
use alloc::collections::BTreeSet;
use core::sync::atomic::{AtomicU16, Ordering};
use spin::Mutex;

use crate::net::{connection_err::ConnectionError, SocketType};

const SYSTEM_PORT_MIN: u16 = 0;
const SYSTEM_PORT_MAX: u16 = 1023;
const USER_PORT_MIN: u16 = 1024;
const USER_PORT_MAX: u16 = 49151;
const EPHEMERAL_PORT_MIN: u16 = 49152;
const EPHEMERAL_PORT_MAX: u16 = 65535;

// A simple local port generator with port allocation and release
// Port Number Ranges
// ref to https://datatracker.ietf.org/doc/html/rfc6335#page-11
// 1. the System Ports, also known as the Well Known Ports, from 0-1023 (assigned by IANA)
// 2. the User Ports, also known as the Registered Ports, from 1024-49151 (assigned by IANA)
// 3. the Dynamic Ports, also known as the Private or Ephemeral Ports, from 49152-65535 (never assigned)
// Dynamic port range as defined in RFC6335
pub struct PortGenerator {
    ephemeral_counter: AtomicU16,
    allocated_ports: Mutex<BTreeSet<(u16, SocketType)>>,
}

/// Initialize the global port generator
pub static PORT_GENERATOR: PortGenerator = PortGenerator::new();

impl PortGenerator {
    pub const fn new() -> Self {
        PortGenerator {
            ephemeral_counter: AtomicU16::new(EPHEMERAL_PORT_MIN),
            allocated_ports: Mutex::new(BTreeSet::new()),
        }
    }

    /// Acquires port for the specified protocol
    pub fn acquire_port(
        &self,
        socket_type: SocketType,
        requested_port: u16,
    ) -> Result<u16, ConnectionError> {
        if requested_port == 0 {
            // allocate from dynamic port range
            self.allocate_ephemeral_port(socket_type)
        } else {
            self.allocate_specific_port(socket_type, requested_port)
        }
    }

    // Try to assign a specific port for a protocol
    fn allocate_specific_port(
        &self,
        socket_type: SocketType,
        requested_port: u16,
    ) -> Result<u16, ConnectionError> {
        if (SYSTEM_PORT_MIN..=SYSTEM_PORT_MAX).contains(&requested_port) {
            log::warn!("Warning: acquiring a system port");
        }

        // Allow system & user port range
        if !(SYSTEM_PORT_MIN..=SYSTEM_PORT_MAX).contains(&requested_port)
            && !(USER_PORT_MIN..=USER_PORT_MAX).contains(&requested_port)
        {
            return Err(ConnectionError::PortOutOfRange(
                requested_port,
                "out of range".into(),
            ));
        }

        let mut ports = self.allocated_ports.lock();
        if ports.insert((requested_port, socket_type)) {
            Ok(requested_port)
        } else {
            Err(ConnectionError::PortInUse(requested_port))
        }
    }

    // Allocates an ephemeral port using RFC6335 dynamic port range
    fn allocate_ephemeral_port(&self, socket_type: SocketType) -> Result<u16, ConnectionError> {
        let mut ports = self.allocated_ports.lock();

        // Linear scan through ephemeral range (RFC6335 section 4.2)
        for _ in EPHEMERAL_PORT_MIN..=EPHEMERAL_PORT_MAX {
            let candidate = self
                .ephemeral_counter
                .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |prev| {
                    Some(next_ephemeral(prev))
                })
                .expect("Atomic port counter should never fail");

            if !ports.contains(&(candidate, socket_type)) {
                ports.insert((candidate, socket_type));
                return Ok(candidate);
            }
        }

        Err(ConnectionError::NoAvailableDynamicPort)
    }

    pub fn release_port(&self, socket_type: SocketType, port: u16) -> bool {
        let mut ports = self.allocated_ports.lock();
        ports.remove(&(port, socket_type))
    }
}

// Circular increment within ephemeral port range
fn next_ephemeral(current: u16) -> u16 {
    if current == EPHEMERAL_PORT_MAX {
        EPHEMERAL_PORT_MIN
    } else {
        current + 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;
    #[test]
    fn test_port_generator() {
        let port_gen = PortGenerator::new();
        let port = port_gen.acquire_port(SocketType::SockStream, 0).unwrap();
        assert!((EPHEMERAL_PORT_MIN..=EPHEMERAL_PORT_MAX).contains(&port));
        assert!(port_gen.release_port(SocketType::SockStream, port));
        assert!(port_gen.acquire_port(SocketType::SockStream, port).is_err());
        let specific_port = 8080;
        let acquired_port = port_gen
            .acquire_port(SocketType::SockStream, specific_port)
            .unwrap();
        assert_eq!(acquired_port, specific_port);
        assert!(port_gen.release_port(SocketType::SockStream, specific_port));
        assert!(port_gen
            .acquire_port(SocketType::SockStream, specific_port)
            .is_ok());
    }
}
