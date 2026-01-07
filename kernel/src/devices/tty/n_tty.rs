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

use crate::devices::{
    tty::{
        serial,
        termios::{CcIndex, Iflags, Oflags, Termios},
    },
    Device, DeviceClass, DeviceId,
};
use alloc::{collections::VecDeque, string::String, sync::Arc, vec::Vec};
use core::sync::atomic::{AtomicUsize, Ordering};
use embedded_io::ErrorKind;
use libc::{c_int, TCFLSH, TCGETS, TCIFLUSH, TCSBRK, TCSETS, TCSETSF, TCSETSW, TCXONC};
use serial::Serial;
use spin::{Mutex, Once};

static TTY: Once<Arc<Tty>> = Once::new();

enum SpecKey {
    Up,
    Down,
}

pub struct Tty {
    serial: Arc<Serial>,
    line_buf: Mutex<[u8; 512]>,
    cursor: AtomicUsize,
    history: Mutex<VecDeque<String>>,
    history_cursor: AtomicUsize,
    spec_key: Mutex<Option<SpecKey>>,
}

impl Tty {
    pub fn init(serial: Arc<Serial>) -> &'static Arc<Tty> {
        TTY.call_once(|| {
            Arc::new(Self {
                serial,
                line_buf: Mutex::new([0u8; 512]),
                cursor: AtomicUsize::new(0),
                history: Mutex::new(VecDeque::with_capacity(5)),
                history_cursor: AtomicUsize::new(0),
                spec_key: Mutex::new(None),
            })
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
        self.serial.write(pos, b"\r", is_blocking)?;
        self.serial.write(pos, b"\x1b[2K", is_blocking)?;
        Ok(())
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
        self.serial.open()
    }

    fn close(&self) -> Result<(), ErrorKind> {
        self.serial.close()
    }

    fn read(&self, _pos: u64, buf: &mut [u8], is_blocking: bool) -> Result<usize, ErrorKind> {
        let mut line_buf = self.line_buf.lock();
        let termios = self.serial.termios_snapshot();
        let map_crlf = termios.iflag.contains(Iflags::ICRNL);
        let erase_char = termios.cc[CcIndex::Verase as usize];
        let kill_char = termios.cc[CcIndex::Vkill as usize];
        // handle special characters
        if let Some(key) = &*self.spec_key.lock() {
            let history_cursor = self.history_cursor.load(Ordering::Relaxed);
            match key {
                SpecKey::Up => {
                    if history_cursor < self.history.lock().len() {
                        if let Some(hist_cmd) = self.get_history(history_cursor) {
                            line_buf[..hist_cmd.len()].copy_from_slice(hist_cmd.as_bytes());
                            self.cursor.store(hist_cmd.len(), Ordering::Relaxed);
                            self.serial.write(_pos, hist_cmd.as_bytes(), false)?;
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
                            self.serial.write(_pos, hist_cmd.as_bytes(), false)?;
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
            let nbytes = self.serial.read(_pos, &mut temp_buf, is_blocking).unwrap();
            let mut i = 0;
            while i < nbytes {
                let ch = temp_buf[i];
                let cursor = self.cursor.load(Ordering::Relaxed);
                if map_crlf && ch == b'\r' {
                    let _ = self.serial.write(_pos, b"\r\n", false);
                    line_buf[cursor] = b'\n';
                    buf[..cursor + 1].copy_from_slice(&line_buf[..cursor + 1]);
                    let command = String::from_utf8_lossy(&line_buf[..cursor]).into_owned();
                    if !command.is_empty() {
                        self.add_history(&command);
                    }
                    line_buf.fill(0);
                    self.cursor.store(0, Ordering::Relaxed);
                    return Ok(cursor + 1);
                }
                if erase_char == ch {
                    if cursor > 0 {
                        let backspace_seq = [8u8, b' ', 8u8];
                        let _ = self.serial.write(_pos, &backspace_seq, false);
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
                line_buf[cursor] = ch;
                let _ = self.cursor.fetch_add(1, Ordering::Relaxed);
                let _ = self.serial.write(_pos, &[ch], false);
            }
        }
    }

    fn write(&self, _pos: u64, buf: &[u8], is_blocking: bool) -> Result<usize, ErrorKind> {
        let termios = self.serial.termios_snapshot();
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

            self.serial.write(_pos, &processed_buf, is_blocking)?;
            Ok(buf.len())
        } else {
            self.serial.write(_pos, buf, is_blocking)
        }
    }

    fn ioctl(&self, request: u32, arg: usize) -> Result<(), ErrorKind> {
        match request {
            TCGETS => {
                let termios = self.serial.termios_snapshot();
                unsafe { Serial::store_user_termios(arg as *mut Termios, &termios) }
            }
            TCSETS => {
                let termios = unsafe { Serial::load_user_termios(arg as *const Termios)? };
                self.serial.apply_termios(termios)
            }
            TCSETSW => {
                let termios = unsafe { Serial::load_user_termios(arg as *const Termios)? };
                self.serial.wait_for_tx_empty()?;
                self.serial.apply_termios(termios)
            }
            TCSETSF => {
                let termios = unsafe { Serial::load_user_termios(arg as *const Termios)? };
                self.serial.wait_for_tx_empty()?;
                self.serial.handle_tcflsh(TCIFLUSH)?;
                self.serial.apply_termios(termios)
            }
            TCFLSH => self.serial.handle_tcflsh(arg as c_int),
            TCXONC => self.serial.handle_tcxonc(arg as c_int),
            TCSBRK => self.serial.handle_tcsbrk(arg as c_int),
            _ => self.serial.ioctl(request, arg),
        }
    }
}
