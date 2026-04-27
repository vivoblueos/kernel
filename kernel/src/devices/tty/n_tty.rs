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

use crate::{
    devices::{
        tty::termios::{CcIndex, Cflags, Iflags, Oflags, Termios},
        Device, DeviceClass, DeviceId, DeviceRequest,
    },
    drivers::serial::Serial,
};
use alloc::{collections::VecDeque, string::String, sync::Arc, vec::Vec};
use blueos_driver::uart::{DataBits, UartConfig};
use core::sync::atomic::{AtomicUsize, Ordering};
use embedded_io::ErrorKind;
use libc::{c_int, TCFLSH, TCGETS, TCIFLUSH, TCSBRK, TCSETS, TCSETSF, TCSETSW, TCXONC};
use spin::Mutex;

enum SpecKey {
    Up,
    Down,
}

pub struct Tty {
    dev: &'static crate::drivers::serial::Serial,
    termios: Mutex<Termios>,
    line_buf: Mutex<[u8; 512]>,
    cursor: AtomicUsize,
    history: Mutex<VecDeque<String>>,
    history_cursor: AtomicUsize,
    spec_key: Mutex<Option<SpecKey>>,
}

impl Tty {
    pub fn init(dev: &'static crate::drivers::serial::Serial, termios: Termios) -> Arc<Tty> {
        Arc::new(Self {
            dev,
            termios: Mutex::new(termios),
            line_buf: Mutex::new([0u8; 512]),
            cursor: AtomicUsize::new(0),
            history: Mutex::new(VecDeque::with_capacity(5)),
            history_cursor: AtomicUsize::new(0),
            spec_key: Mutex::new(None),
        })
    }

    fn add_history(&self, command: &str) {
        let mut history = self.history.lock();
        if history.front().map(|s| s.as_str()) != Some(command) {
            if history.len() == 5 {
                history.pop_back();
            }
            history.push_front(String::from(command));
        }
        self.history_cursor.store(0, Ordering::Relaxed);
    }

    fn get_history(&self, index: usize) -> Option<String> {
        self.history.lock().get(index).cloned()
    }

    fn clear_line(&self, pos: u64, is_blocking: bool) -> Result<(), ErrorKind> {
        self.dev.send_bytes(b"\r", !is_blocking)?;
        self.dev.send_bytes(b"\x1b[2K", !is_blocking)?;
        Ok(())
    }

    fn try_drain_committed_line(&self, line_buf: &mut [u8], out_buf: &mut [u8]) -> Option<usize> {
        let pending_len = self.cursor.load(Ordering::Relaxed);
        if pending_len == 0 || pending_len > line_buf.len() || line_buf[pending_len - 1] != b'\n' {
            return None;
        }

        let copy_len = core::cmp::min(pending_len, out_buf.len());
        out_buf[..copy_len].copy_from_slice(&line_buf[..copy_len]);

        if copy_len < pending_len {
            line_buf.copy_within(copy_len..pending_len, 0);
            line_buf[pending_len - copy_len..pending_len].fill(0);
            self.cursor
                .store(pending_len - copy_len, Ordering::Relaxed);
        } else {
            line_buf.fill(0);
            self.cursor.store(0, Ordering::Relaxed);
        }

        Some(copy_len)
    }

    fn apply_termios_atomically(&self, termios: Termios) -> Result<(), ErrorKind> {
        let uart_config = convert_termios_to_uart_config(&termios);
        let mut termios_guard = self.termios.lock();
        // Keep software termios and hardware UART update in one critical section so
        // concurrent ioctl readers/writers don't observe an intermediate state.
        self.dev.reconfigure(uart_config)?;
        *termios_guard = termios;
        Ok(())
    }
}

unsafe fn load_user_termios(ptr: *const Termios) -> Result<Termios, ErrorKind> {
    if ptr.is_null() {
        return Err(ErrorKind::InvalidInput);
    }
    Ok(*ptr)
}

unsafe fn store_user_termios(ptr: *mut Termios, termios: &Termios) -> Result<(), ErrorKind> {
    if ptr.is_null() {
        return Err(ErrorKind::InvalidInput);
    }
    *ptr = *termios;
    Ok(())
}

fn convert_termios_to_uart_config(termios: &Termios) -> UartConfig {
    UartConfig {
        baudrate: termios.getospeed(),
        data_bits: if termios.cflag.contains(Cflags::CSIZE_8) {
            DataBits::DataBits8
        } else if termios.cflag.contains(Cflags::CSIZE_7) {
            DataBits::DataBits7
        } else if termios.cflag.contains(Cflags::CSIZE_6) {
            DataBits::DataBits6
        } else {
            DataBits::DataBits5
        },
        parity: if !termios.cflag.contains(Cflags::PARENB) {
            blueos_driver::uart::Parity::None
        } else if termios.cflag.contains(Cflags::PARODD) {
            blueos_driver::uart::Parity::Odd
        } else {
            blueos_driver::uart::Parity::Even
        },
        stop_bits: if termios.cflag.contains(Cflags::CSTOPB) {
            blueos_driver::uart::StopBits::DataBits2
        } else {
            blueos_driver::uart::StopBits::DataBits1
        },
        flow_ctrl: blueos_driver::uart::FlowCtrl::None,
    }
}

impl Device for Tty {
    fn name(&self) -> String {
        String::from("n_tty")
    }

    fn class(&self) -> DeviceClass {
        DeviceClass::Char
    }

    fn id(&self) -> DeviceId {
        DeviceId::new(5, 0)
    }

    fn open(&self) -> Result<(), ErrorKind> {
        let termios = *self.termios.lock();
        let uart_config = convert_termios_to_uart_config(&termios);
        self.dev.open(uart_config)
    }

    fn close(&self) -> Result<(), ErrorKind> {
        self.dev.close()
    }

    fn read(&self, _pos: u64, buf: &mut [u8], is_blocking: bool) -> Result<usize, ErrorKind> {
        if buf.is_empty() {
            return Ok(0);
        }

        let mut line_buf = self.line_buf.lock();
        let termios = *self.termios.lock();
        let map_crlf = termios.iflag.contains(Iflags::ICRNL);
        // Reserve one byte for '\n' on line commit in canonical input path.
        let line_capacity = line_buf.len().saturating_sub(1);
        let erase_char = termios.cc[CcIndex::Verase as usize];
        let kill_char = termios.cc[CcIndex::Vkill as usize];

        if let Some(drained) = self.try_drain_committed_line(&mut line_buf[..], buf) {
            return Ok(drained);
        }

        // handle special characters
        if let Some(key) = &*self.spec_key.lock() {
            let history_cursor = self.history_cursor.load(Ordering::Relaxed);
            match key {
                SpecKey::Up => {
                    if history_cursor < self.history.lock().len() {
                        if let Some(hist_cmd) = self.get_history(history_cursor) {
                            line_buf[..hist_cmd.len()].copy_from_slice(hist_cmd.as_bytes());
                            self.cursor.store(hist_cmd.len(), Ordering::Relaxed);
                            self.dev.send_bytes(hist_cmd.as_bytes(), false)?;
                            self.history_cursor
                                .store(history_cursor + 1, Ordering::Relaxed);
                        }
                    }
                }
                SpecKey::Down => {
                    if history_cursor != 0 {
                        if let Some(hist_cmd) = self.get_history(history_cursor - 1) {
                            line_buf[..hist_cmd.len()].copy_from_slice(hist_cmd.as_bytes());
                            self.cursor.store(hist_cmd.len(), Ordering::Relaxed);
                            self.dev.send_bytes(hist_cmd.as_bytes(), false)?;
                        }
                        self.history_cursor
                            .store(history_cursor - 1, Ordering::Relaxed);
                    } else {
                        line_buf.fill(0);
                        self.cursor.store(0, Ordering::Relaxed);
                        self.history_cursor.store(0, Ordering::Relaxed);
                    }
                }
            }
        }
        *self.spec_key.lock() = None;
        // normal character
        loop {
            let mut temp_buf = [0u8; 512];
            let nbytes = self.dev.read_bytes(&mut temp_buf, !is_blocking)?;
            let mut i = 0;
            while i < nbytes {
                let ch = temp_buf[i];
                let cursor = self.cursor.load(Ordering::Relaxed);
                if map_crlf && ch == b'\r' {
                    self.dev.send_bytes(b"\r\n", false)?;
                    line_buf[cursor] = b'\n';
                    let command = String::from_utf8_lossy(&line_buf[..cursor]).into_owned();
                    if !command.is_empty() {
                        self.add_history(&command);
                    }
                    self.cursor.store(cursor + 1, Ordering::Relaxed);
                    if let Some(drained) = self.try_drain_committed_line(&mut line_buf[..], buf) {
                        return Ok(drained);
                    }
                    return Ok(0);
                }
                if erase_char == ch {
                    if cursor > 0 {
                        let backspace_seq = [8u8, b' ', 8u8];
                        self.dev.send_bytes(&backspace_seq, false)?;
                        let _ = self.cursor.fetch_sub(1, Ordering::Relaxed);
                        line_buf[cursor - 1] = 0;
                    }
                    i += 1;
                    continue;
                }

                if kill_char == ch {
                    line_buf.fill(0);
                    self.cursor.store(0, Ordering::Relaxed);
                    i += 1;
                    continue;
                }

                // get commandline history
                // up key  : 0x1b 0x5b 0x41
                // down key: 0x1b 0x5b 0x42
                if ch == 0x1b && i <= temp_buf.len() - 3 && temp_buf[i + 1] == 0x5b {
                    match temp_buf[i + 2] {
                        0x41 => {
                            *self.spec_key.lock() = Some(SpecKey::Up);
                            self.clear_line(_pos, false)?;
                            buf[0] = b'\n';
                            return Ok(1);
                        }
                        0x42 => {
                            *self.spec_key.lock() = Some(SpecKey::Down);
                            self.clear_line(_pos, false)?;
                            buf[0] = b'\n';
                            return Ok(1);
                        }
                        _ => {
                            i += 3;
                            continue;
                        }
                    }
                }
                i += 1;
                if cursor >= line_capacity {
                    // Drop extra input when line buffer is full to avoid OOB write.
                    continue;
                }
                line_buf[cursor] = ch;
                let _ = self.cursor.fetch_add(1, Ordering::Relaxed);
                self.dev.send_bytes(&[ch], false);
            }
        }
    }

    fn write(&self, _pos: u64, buf: &[u8], is_blocking: bool) -> Result<usize, ErrorKind> {
        let termios = *self.termios.lock();
        if termios.oflag.contains(Oflags::OPOST) {
            let mut processed_buf = Vec::new();

            for &byte in buf {
                if byte == b'\n' && termios.oflag.contains(Oflags::ONLCR) {
                    // Convert LF to CRLF
                    processed_buf.push(b'\r');
                    processed_buf.push(b'\n');
                } else if byte == b'\r' && termios.oflag.contains(Oflags::OCRNL) {
                    // Convert CR to LF
                    processed_buf.push(b'\n');
                } else {
                    processed_buf.push(byte);
                }
            }

            self.dev.send_bytes(&processed_buf, !is_blocking)?;
            Ok(buf.len())
        } else {
            self.dev.send_bytes(buf, !is_blocking)
        }
    }

    fn ioctl(&self, request: u32, arg: usize) -> Result<(), ErrorKind> {
        match request {
            TCGETS => {
                let termios = *self.termios.lock();
                unsafe { store_user_termios(arg as *mut Termios, &termios) }
            }
            TCSETS => {
                let termios = unsafe { load_user_termios(arg as *const Termios)? };
                self.apply_termios_atomically(termios)
            }
            TCSETSW => {
                let termios = unsafe { load_user_termios(arg as *const Termios)? };
                self.dev.wait_for_tx_drain_complete()?;
                self.apply_termios_atomically(termios)
            }
            TCSETSF => {
                let termios = unsafe { load_user_termios(arg as *const Termios)? };
                self.dev.wait_for_tx_drain_complete()?;
                self.dev.handle_tcflsh(TCIFLUSH)?;
                self.apply_termios_atomically(termios)
            }
            TCFLSH => self.dev.handle_tcflsh(arg as c_int),
            TCXONC => {
                let cc = &self.termios.lock().cc;
                self.dev.handle_tcxonc(arg as c_int, cc)
            }
            TCSBRK => self.dev.handle_tcsbrk(arg as c_int),
            req => match DeviceRequest::from(req) {
                DeviceRequest::Config => Ok(()),
                DeviceRequest::Close => Ok(()),
                _ => Err(ErrorKind::InvalidData),
            },
        }
    }
}
