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

extern crate esp_radio_sys;
use librs::syscall::Syscall;
use std::{
    io::{Read, Write},
    net::{Ipv4Addr, SocketAddrV4, TcpStream},
};

const SCAN_POLL_ATTEMPTS: usize = 25;
const SCAN_POLL_INTERVAL_MS: u32 = 200;
const WIFI_CONNECT_WAIT_MS: u32 = 15000;
const WIFI_SSID: &[u8] = blueos_kconfig::CONFIG_WLAN_SSID;
const WIFI_PASSWORD: &[u8] = blueos_kconfig::CONFIG_WLAN_PASSWORD;
const PHONE_TCP_SERVER_PORT: u16 = 34228;
const TCP_TEST_PAYLOAD: &[u8] = b"blueos-wifi-tcp-link-test";
const TCP_RECV_EXPECTED_MESSAGES: usize = 2;
const TCP_RECV_BUF_SIZE: usize = 512;

extern crate librs;
extern crate rsrt;

fn security_name(sec: u8) -> &'static str {
    match sec {
        0 => "Open",
        1 => "WEP",
        2 => "WPA",
        3 => "WPA2",
        4 => "WPA3",
        _ => "Unknown",
    }
}

fn wlan0_name() -> [libc::c_char; 16] {
    let mut name = [0 as libc::c_char; 16];
    let bytes = b"wlan0\0";
    let mut i = 0;
    while i < bytes.len() && i < name.len() {
        name[i] = bytes[i] as libc::c_char;
        i += 1;
    }
    name
}

fn parse_router_ip() -> std::io::Result<Ipv4Addr> {
    let ip_bytes = blueos_kconfig::CONFIG_NET_ROUTER_IP;
    let len = ip_bytes
        .iter()
        .position(|&byte| byte == b'\0')
        .unwrap_or(ip_bytes.len());
    let ip = core::str::from_utf8(&ip_bytes[..len])
        .map_err(|_| std::io::Error::from_raw_os_error(libc::EINVAL))?;
    let mut parts = ip.split('.');

    let a = parts
        .next()
        .and_then(|part| part.parse::<u8>().ok())
        .ok_or_else(|| std::io::Error::from_raw_os_error(libc::EINVAL))?;
    let b = parts
        .next()
        .and_then(|part| part.parse::<u8>().ok())
        .ok_or_else(|| std::io::Error::from_raw_os_error(libc::EINVAL))?;
    let c = parts
        .next()
        .and_then(|part| part.parse::<u8>().ok())
        .ok_or_else(|| std::io::Error::from_raw_os_error(libc::EINVAL))?;
    let d = parts
        .next()
        .and_then(|part| part.parse::<u8>().ok())
        .ok_or_else(|| std::io::Error::from_raw_os_error(libc::EINVAL))?;

    if parts.next().is_some() {
        return Err(std::io::Error::from_raw_os_error(libc::EINVAL));
    }

    Ok(Ipv4Addr::new(a, b, c, d))
}

fn run_phone_tcp_check() -> std::io::Result<()> {
    let phone_tcp_server = SocketAddrV4::new(parse_router_ip()?, PHONE_TCP_SERVER_PORT);
    println!("TCP link check: connecting to {}", phone_tcp_server);
    let mut stream = TcpStream::connect(phone_tcp_server)?;
    stream.write_all(TCP_TEST_PAYLOAD)?;
    println!(
        "WiFi phone TCP TX OK: sent {} bytes to {}: {:?}",
        TCP_TEST_PAYLOAD.len(),
        phone_tcp_server,
        TCP_TEST_PAYLOAD
    );

    println!(
        "TCP link check: waiting for response from {}",
        phone_tcp_server
    );
    let mut rx_buf = [0u8; TCP_RECV_BUF_SIZE];
    for message_index in 0..TCP_RECV_EXPECTED_MESSAGES {
        let size = stream.read(&mut rx_buf)?;
        if size == 0 {
            println!(
                "WiFi phone TCP RX closed after {} message(s)",
                message_index
            );
            return Ok(());
        }

        println!(
            "WiFi phone TCP RX OK: message {}/{} received {} bytes from {}: {:?}",
            message_index + 1,
            TCP_RECV_EXPECTED_MESSAGES,
            size,
            phone_tcp_server,
            &rx_buf[..size]
        );
        if let Ok(text) = core::str::from_utf8(&rx_buf[..size]) {
            println!("WiFi phone TCP RX text: {}", text);
        }
    }

    println!(
        "WiFi phone TCP RX check done: received {} message(s)",
        TCP_RECV_EXPECTED_MESSAGES
    );
    Ok(())
}

fn main() -> std::io::Result<()> {
    let _d = librs::time::msleep(1000);

    println!("Wifi example");
    let fd = librs::net::socket::socket(libc::AF_INET, libc::SOCK_DGRAM | libc::SOCK_CLOEXEC, 0);
    if fd < 0 {
        eprintln!(
            "Failed to create socket: {}",
            std::io::Error::last_os_error()
        );
        return Err(std::io::Error::last_os_error());
    }

    println!("Scanning for WiFi networks...");

    // SIOCSIWSCAN: trigger scan on wlan0 with struct iw_scan_req
    let scan_req = libc::iw_scan_req {
        scan_type: libc::IW_SCAN_TYPE_ACTIVE as u8,
        essid_len: 0,
        num_channels: 0,
        flags: 0,
        bssid: unsafe { core::mem::zeroed() },
        essid: [0u8; libc::IW_ESSID_MAX_SIZE],
        min_channel_time: 0,
        max_channel_time: 0,
        channel_list: [libc::iw_freq {
            m: 0,
            e: 0,
            i: 0,
            flags: 0,
        }; libc::IW_MAX_FREQUENCIES],
    };
    let mut iwreq = libc::iwreq {
        ifr_ifrn: libc::__c_anonymous_iwreq {
            ifrn_name: wlan0_name(),
        },
        u: libc::iwreq_data {
            essid: libc::iw_point {
                pointer: &scan_req as *const libc::iw_scan_req as *mut libc::c_void,
                length: core::mem::size_of::<libc::iw_scan_req>() as u16,
                flags: 0,
            },
        },
    };
    let ret = unsafe {
        librs::syscall::sys::Sys::ioctl(
            fd,
            libc::SIOCSIWSCAN,
            &mut iwreq as *mut _ as *mut libc::c_void,
        )
    };
    if let Err(librs::errno::Errno(errno)) = ret {
        eprintln!("SIOCSIWSCAN failed: errno={}", errno);
        return Err(std::io::Error::from_raw_os_error(errno));
    }
    println!("Scan triggered.");

    // SIOCGIWSCAN: retrieve results into a 4 KiB buffer
    let mut buf = [0u8; 4096];
    let data = libc::iw_point {
        pointer: buf.as_mut_ptr() as *mut libc::c_void,
        length: buf.len() as u16,
        flags: 0,
    };
    let mut iwreq = libc::iwreq {
        ifr_ifrn: libc::__c_anonymous_iwreq {
            ifrn_name: wlan0_name(),
        },
        u: libc::iwreq_data { data },
    };
    let mut total = None;
    for attempt in 0..SCAN_POLL_ATTEMPTS {
        let ret = unsafe {
            librs::syscall::sys::Sys::ioctl(
                fd,
                libc::SIOCGIWSCAN,
                &mut iwreq as *mut _ as *mut libc::c_void,
            )
        };
        match ret {
            Ok(n) if n >= 0 => {
                total = Some(n as usize);
                break;
            }
            Err(librs::errno::Errno(errno)) if attempt + 1 < SCAN_POLL_ATTEMPTS => {
                if errno != libc::EAGAIN {
                    eprintln!("SIOCGIWSCAN failed: errno={}", errno);
                    return Err(std::io::Error::from_raw_os_error(errno));
                }
                let _ = librs::time::msleep(SCAN_POLL_INTERVAL_MS);
            }
            Err(librs::errno::Errno(errno)) => {
                eprintln!(
                    "SIOCGIWSCAN failed or scan results are not ready: errno={}",
                    errno
                );
                return Err(std::io::Error::from_raw_os_error(errno));
            }
            _ => {
                eprintln!("SIOCGIWSCAN returned an invalid success value");
                return Err(std::io::Error::from_raw_os_error(libc::EINVAL));
            }
        }
    }
    let total = total.unwrap_or(0);

    // Decode: [u32 count][entry]*
    if total < 4 {
        println!("No scan results ({} bytes returned)", total);
        return Ok(());
    }
    let count = u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]);
    println!("Found {} networks:\n", count);

    let mut off = 4usize;
    for i in 0..count {
        if off + 4 > total {
            break;
        }
        let ssid_len = u32::from_le_bytes([buf[off], buf[off + 1], buf[off + 2], buf[off + 3]]);
        off += 4;

        if off + ssid_len as usize > total {
            break;
        }
        let ssid =
            core::str::from_utf8(&buf[off..off + ssid_len as usize]).unwrap_or("<invalid utf8>");
        off += ssid_len as usize;

        if off + 6 > total {
            break;
        }
        let bssid = &buf[off..off + 6];
        off += 6;

        if off + 1 > total {
            break;
        }
        let signal = buf[off] as i8;
        off += 1;

        if off + 2 > total {
            break;
        }
        let channel = u16::from_le_bytes([buf[off], buf[off + 1]]);
        off += 2;

        if off + 1 > total {
            break;
        }
        let security = buf[off];
        off += 1;

        println!("  {}. SSID: {}", i + 1, ssid);
        println!(
            "     BSSID: {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}",
            bssid[0], bssid[1], bssid[2], bssid[3], bssid[4], bssid[5]
        );
        println!("     Signal: {} dBm", signal);
        println!("     Channel: {}", channel);
        println!("     Security: {}", security_name(security));
        println!();
    }

    println!("Connecting to WiFi SSID: test_esp (WPA2)...");

    // SIOCSIWENCODE — cache passphrase for WPA2 network
    let mut iwreq = libc::iwreq {
        ifr_ifrn: libc::__c_anonymous_iwreq {
            ifrn_name: wlan0_name(),
        },
        u: libc::iwreq_data {
            encoding: libc::iw_point {
                pointer: WIFI_PASSWORD.as_ptr() as *mut libc::c_void,
                length: WIFI_PASSWORD.len() as u16,
                flags: 0,
            },
        },
    };
    let ret = unsafe {
        librs::syscall::sys::Sys::ioctl(
            fd,
            libc::SIOCSIWENCODE,
            &mut iwreq as *mut _ as *mut libc::c_void,
        )
    };
    if let Err(librs::errno::Errno(errno)) = ret {
        eprintln!("SIOCSIWENCODE failed: errno={}", errno);
    }

    // SIOCSIWESSID — trigger connect
    let mut iwreq = libc::iwreq {
        ifr_ifrn: libc::__c_anonymous_iwreq {
            ifrn_name: wlan0_name(),
        },
        u: libc::iwreq_data {
            essid: libc::iw_point {
                pointer: WIFI_SSID.as_ptr() as *mut libc::c_void,
                // The length should not include the null terminator, so we subtract 1.
                length: (WIFI_SSID.len() - 1) as u16,
                flags: 1,
            },
        },
    };
    let ret = unsafe {
        librs::syscall::sys::Sys::ioctl(
            fd,
            libc::SIOCSIWESSID,
            &mut iwreq as *mut _ as *mut libc::c_void,
        )
    };
    if let Err(librs::errno::Errno(errno)) = ret {
        eprintln!("SIOCSIWESSID failed: errno={}", errno);
        return Err(std::io::Error::from_raw_os_error(errno));
    }

    println!("WiFi connect triggered, waiting for station connection...");
    let _ = librs::time::msleep(WIFI_CONNECT_WAIT_MS);
    run_phone_tcp_check();
    Ok(())
}
