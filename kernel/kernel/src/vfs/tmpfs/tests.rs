// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

use super::*;
use crate::devices::DeviceId;
use blueos_test_macro::test;
use embedded_io::ErrorKind;

struct LockCheckingDevice {
    inode: RwLock<Weak<TmpInode>>,
    nonblock: bool,
    fail: bool,
}

impl LockCheckingDevice {
    fn check_call(&self, pos: u64, nonblock: bool) -> Arc<TmpInode> {
        assert_eq!(pos, 37);
        assert_eq!(nonblock, self.nonblock);
        let inode = self.inode.read().upgrade().unwrap();
        // Fail immediately on the old implementation instead of hanging on
        // a nested I/O operation. A write guard excludes both kinds of lock.
        assert!(
            inode.inner.try_write().is_some(),
            "tmpfs held its inode lock across a device callback"
        );
        inode
    }
}

impl Device for LockCheckingDevice {
    fn name(&self) -> String {
        String::from("tmpfs-lock-test")
    }

    fn class(&self) -> DeviceClass {
        DeviceClass::Char
    }

    fn id(&self) -> DeviceId {
        DeviceId::new(0, 0)
    }

    fn read(&self, pos: u64, buf: &mut [u8], nonblock: bool) -> Result<usize, ErrorKind> {
        let inode = self.check_call(pos, nonblock);
        if self.fail {
            return Err(ErrorKind::Interrupted);
        }
        // Exercise a write on the same inode before this read returns. This
        // models output progressing while input is pending, without relying
        // on thread scheduling or terminal input.
        assert_eq!(inode.write_at(pos as usize, b"out", nonblock), Ok(3));
        buf[..2].copy_from_slice(b"ok");
        Ok(2)
    }

    fn write(&self, pos: u64, buf: &[u8], nonblock: bool) -> Result<usize, ErrorKind> {
        let _inode = self.check_call(pos, nonblock);
        assert_eq!(buf, b"out");
        if self.fail {
            return Err(ErrorKind::Interrupted);
        }
        Ok(buf.len())
    }
}

fn device_inode(nonblock: bool, fail: bool) -> Arc<TmpInode> {
    let device = Arc::new(LockCheckingDevice {
        inode: RwLock::new(Weak::new()),
        nonblock,
        fail,
    });
    let inode = TmpInode::new_device(
        &Weak::new(),
        2,
        InodeMode::from(0o600),
        0,
        0,
        device.clone(),
    );
    *device.inode.write() = Arc::downgrade(&inode);
    inode
}

#[test]
fn tmpfs_device_read_allows_write_before_returning() {
    for nonblock in [false, true] {
        let inode = device_inode(nonblock, false);
        let mut buf = [0; 4];
        assert_eq!(inode.read_at(37, &mut buf, nonblock), Ok(2));
        assert_eq!(&buf, b"ok\0\0");
    }
}

#[test]
fn tmpfs_device_write_releases_inode_lock() {
    for nonblock in [false, true] {
        let inode = device_inode(nonblock, false);
        assert_eq!(inode.write_at(37, b"out", nonblock), Ok(3));
    }
}

#[test]
fn tmpfs_device_io_preserves_errors() {
    let inode = device_inode(true, true);
    assert_eq!(inode.read_at(37, &mut [0; 4], true), Err(code::EINTR));
    assert_eq!(inode.write_at(37, b"out", true), Err(code::EINTR));
}

#[test]
fn tmpfs_regular_file_read_write_and_growth() {
    let inode = TmpInode::new_file(&Weak::new(), 2, InodeMode::from(0o600), 0, 0);
    assert_eq!(inode.write_at(0, b"ab", false), Ok(2));
    assert_eq!(inode.write_at(4, b"cd", false), Ok(2));
    let mut buf = [0xff; 8];
    assert_eq!(inode.read_at(0, &mut buf, false), Ok(6));
    assert_eq!(&buf[..6], b"ab\0\0cd");
    assert_eq!(&buf[6..], &[0xff; 2]);
    assert_eq!(inode.read_at(6, &mut buf, false), Ok(0));
    assert_eq!(inode.inner.read().attr.size, 6);
}
