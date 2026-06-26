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
    error::{code, Error},
    net::{
        connection::Connection,
        iface::control::{NetIfaceControl, NetIfaceError},
    },
    vfs::{
        fd_manager::get_fd_manager,
        file::{FileAttr, FileOps, OpenFlags},
        inode::InodeOps,
        inode_mode::InodeMode,
        path,
        utils::SeekFrom,
    },
};
use alloc::{boxed::Box, sync::Arc};
use core::sync::atomic::{AtomicI32, Ordering};
use log::{debug, warn};
use spin::Mutex;

pub struct SocketFile {
    inode: Arc<dyn InodeOps>,
    socket: Mutex<Option<Arc<Connection>>>,
    open_flags: AtomicI32,
}

impl SocketFile {
    pub fn new(inode: Arc<dyn InodeOps>, flags: OpenFlags) -> Self {
        Self {
            inode,
            socket: Mutex::new(None),
            open_flags: AtomicI32::new(flags.bits()),
        }
    }

    pub fn inode(&self) -> &Arc<dyn InodeOps> {
        &self.inode
    }

    pub fn socket(&self) -> Option<Arc<Connection>> {
        let guard = self.socket.lock();
        guard.as_ref().cloned()
    }

    pub fn set_socket(&self, socket: Arc<Connection>) {
        let mut guard = self.socket.lock();
        *guard = Some(socket);
    }

    pub fn is_nonblock(&self) -> bool {
        self.flags().contains(OpenFlags::O_NONBLOCK)
    }

    fn update_blocking_state(&self, old_flags: OpenFlags, new_flags: OpenFlags) {
        let non_block_changed =
            old_flags.contains(OpenFlags::O_NONBLOCK) != new_flags.contains(OpenFlags::O_NONBLOCK);

        if !non_block_changed {
            return;
        }

        let is_non_block = new_flags.contains(OpenFlags::O_NONBLOCK);
        debug!("Socket non-blocking state changed to: {}", is_non_block);

        self.update_connection_blocking(is_non_block);
    }

    fn update_connection_blocking(&self, is_non_block: bool) {
        if let Some(socket) = self.socket() {
            socket.set_is_nonblocking(is_non_block);
        } else {
            warn!("SocketFile: No socket to update blocking state");
        }
    }
}

impl FileOps for SocketFile {
    fn read(&self, buf: &mut [u8]) -> Result<usize, Error> {
        let Some(socket) = self.socket() else {
            warn!("SocketFile: No socket for read operation.");
            return Err(code::EINVAL);
        };
        let user_buf_addr = buf.as_mut_ptr() as usize;
        let user_buf_len = buf.len();
        let f = move |net_buffer: &mut [u8]| -> (usize, usize) {
            let copy_len = net_buffer.len().min(user_buf_len);
            unsafe {
                let user_buf_ptr = user_buf_addr as *mut u8;
                core::ptr::copy_nonoverlapping(net_buffer.as_ptr(), user_buf_ptr, copy_len);
            }
            (copy_len, copy_len)
        };

        match socket.recv(Box::new(f)) {
            Ok(recv_size) => Ok(recv_size),
            Err(e) => {
                warn!("SocketFile read: connection.recv {}", e);
                Err(code::ERROR)
            }
        }
    }

    fn write(&self, buf: &[u8]) -> Result<usize, Error> {
        let Some(socket) = self.socket() else {
            warn!("SocketFile: No socket for write operation.");
            return Err(code::EINVAL);
        };
        let user_buf_ptr = buf.as_ptr() as usize;
        let user_buf_len = buf.len();
        let flags = if self.is_nonblock() {
            libc::MSG_DONTWAIT
        } else {
            0
        };
        let f = Box::new(move |net_buffer: &mut [u8]| -> (usize, usize) {
            let copy_len = net_buffer.len().min(user_buf_len);
            let user_buf_ptr = user_buf_ptr as *const u8;
            let user_buf = unsafe { core::slice::from_raw_parts(user_buf_ptr, user_buf_len) };
            net_buffer[..copy_len].copy_from_slice(&user_buf[..copy_len]);
            (copy_len, copy_len)
        });

        match socket.send(f, flags) {
            Ok(sent) => Ok(sent),
            Err(e) => {
                warn!("SocketFile write: connection.send {}", e);
                Err(code::ERROR)
            }
        }
    }

    fn seek(&self, seek_from: SeekFrom) -> Result<usize, Error> {
        warn!("Illegal seek on socket, seek is not implemented");
        Err(code::ESPIPE)
    }

    fn ioctl(&self, cmd: u32, arg: usize) -> Result<i32, Error> {
        // Convert raw POSIX ioctl (cmd, arg) into a type-safe NetIfaceControl,
        // then dispatch through the IPC queue to the network stack thread.
        let control = unsafe { NetIfaceControl::from_raw_ioctl(cmd, arg) }.map_err(|err| {
            debug!("SocketFile ioctl: cmd=0x{:x} error {:?}", cmd, err);
            match err {
                NetIfaceError::InvalidParam => code::EINVAL,
                _ => code::ENOTTY,
            }
        })?;

        let Some(socket) = self.socket() else {
            warn!("SocketFile: No socket for ioctl operation.");
            return Err(code::EINVAL);
        };

        match socket.control(control) {
            Ok(_) => Ok(0),
            Err(e) => {
                debug!("SocketFile ioctl: control error {:?}", e);
                Err(code::ENOTTY)
            }
        }
    }

    fn flush(&self) -> Result<(), Error> {
        self.inode.flush()
    }

    fn close(&self) -> Result<(), Error> {
        if let Some(socket) = self.socket() {
            match socket.shutdown() {
                Ok(_) => Ok(()),
                Err(e) => {
                    warn!("Failed to shutdown connection {}", e);
                    Err(code::ERROR)
                }
            }
        } else {
            warn!("SocketFile: No socket to close");
            Ok(())
        }
    }

    fn resize(&self, new_size: usize) -> Result<(), Error> {
        warn!("Illegal resize on socket, resize is not implemented");
        Err(code::EINVAL)
    }

    fn dup(&self, close_on_exec: bool) -> Result<Arc<dyn FileOps>, Error> {
        warn!("Illegal dup on socket, dup is not implemented");
        Err(code::EINVAL)
    }

    fn stat(&self) -> FileAttr {
        self.inode.file_attr()
    }

    fn flags(&self) -> OpenFlags {
        OpenFlags::from_bits_truncate(self.open_flags.load(Ordering::Relaxed))
    }

    fn set_flags(&self, flags: OpenFlags) {
        let old_flags = self.flags();
        self.open_flags.store(flags.bits(), Ordering::Relaxed);
        self.update_blocking_state(old_flags, flags);
    }
}

pub fn alloc_sock_fd(flags: i32) -> i32 {
    let socket_inode = match create_socket_inode() {
        Ok(inode) => inode,
        Err(e) => {
            warn!("Failed to create socket inode: {:?}", e);
            return -1;
        }
    };
    let socket_file = Arc::new(SocketFile::new(socket_inode, flags.into()));
    let mut fd_manager = get_fd_manager().lock();
    fd_manager.alloc_fd(socket_file)
}

pub fn free_sock_fd(fd: i32) -> Result<(), Error> {
    let mut fd_manager = get_fd_manager().lock();
    fd_manager.free_fd(fd)
}

pub fn sock_attach_to_fd(fd: i32, socket: Arc<Connection>) -> Result<i32, Error> {
    let file_ops = {
        let fd_manager = get_fd_manager().lock();
        fd_manager.get_file_ops(fd).ok_or(code::EBADF)?
    };
    let file_ops_ptr = Arc::as_ptr(&file_ops) as *const ();
    if let Some(socket_file) = unsafe { (file_ops_ptr as *const SocketFile).as_ref() } {
        socket_file.set_socket(socket);
        Ok(fd)
    } else {
        warn!("File descriptor {} is not a socket", fd);
        Err(code::ERROR)
    }
}

pub fn get_sock_by_fd(fd: i32) -> Result<Arc<Connection>, Error> {
    let file_ops = {
        let fd_manager = get_fd_manager().lock();
        fd_manager.get_file_ops(fd).ok_or(code::EBADF)?
    };
    try_get_socket(&file_ops).ok_or_else(|| {
        warn!("File descriptor {} is not a socket", fd);
        code::ERROR
    })
}

fn create_socket_inode() -> Result<Arc<dyn InodeOps>, Error> {
    let cwd = path::get_working_dir();
    let inode = cwd
        .inode()
        .create_socket(InodeMode::from_bits_truncate(0o600))?;
    Ok(inode)
}

fn try_get_socket(file_ops: &Arc<dyn FileOps>) -> Option<Arc<Connection>> {
    let file_ops_ptr = Arc::as_ptr(file_ops) as *const ();
    unsafe { (file_ops_ptr as *const SocketFile).as_ref() }
        .and_then(|socket_file| socket_file.socket())
}
