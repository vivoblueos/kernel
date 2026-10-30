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

use crate::devices::DeviceClass;
use bitflags::bitflags;

#[allow(non_camel_case_types)]
pub type mode_t = u32;

bitflags! {
    pub struct InodeMode: u32 {
        const S_ISUID = libc::S_ISUID;
        const S_ISGID = libc::S_ISGID;
        const S_ISVTX = libc::S_ISVTX;
        const S_IRUSR = libc::S_IRUSR;
        const S_IWUSR = libc::S_IWUSR;
        const S_IXUSR = libc::S_IXUSR;
        const S_IRGRP = libc::S_IRGRP;
        const S_IWGRP = libc::S_IWGRP;
        const S_IXGRP = libc::S_IXGRP;
        const S_IROTH = libc::S_IROTH;
        const S_IWOTH = libc::S_IWOTH;
        const S_IXOTH = libc::S_IXOTH;
    }
}

// UID and GID are not supported yet
impl InodeMode {
    pub fn is_readable(&self) -> bool {
        self.contains(Self::S_IRUSR)
    }

    pub fn is_writable(&self) -> bool {
        self.contains(Self::S_IWUSR)
    }

    pub fn is_executable(&self) -> bool {
        self.contains(Self::S_IXUSR)
    }
}

impl From<mode_t> for InodeMode {
    fn from(mode: mode_t) -> Self {
        InodeMode::from_bits_truncate(mode)
    }
}

#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum InodeFileType {
    Regular = libc::S_IFREG,
    Directory = libc::S_IFDIR,
    SymLink = libc::S_IFLNK,
    CharDevice = libc::S_IFCHR,
    BlockDevice = libc::S_IFBLK,
    Fifo = libc::S_IFIFO,
    Socket = libc::S_IFSOCK,
    Unknown = libc::S_IFMT,
}

impl InodeFileType {
    pub fn is_regular_file(&self) -> bool {
        self == &InodeFileType::Regular
    }

    pub fn is_directory(&self) -> bool {
        self == &InodeFileType::Directory
    }

    pub fn is_readable(&self) -> bool {
        matches!(
            self,
            InodeFileType::Regular
                | InodeFileType::CharDevice
                | InodeFileType::BlockDevice
                | InodeFileType::Socket
        )
    }

    pub fn is_writable(&self) -> bool {
        matches!(
            self,
            InodeFileType::Regular
                | InodeFileType::CharDevice
                | InodeFileType::BlockDevice
                | InodeFileType::Socket
        )
    }
}

impl From<mode_t> for InodeFileType {
    fn from(mode: mode_t) -> Self {
        match mode & libc::S_IFMT {
            libc::S_IFREG => InodeFileType::Regular,
            libc::S_IFDIR => InodeFileType::Directory,
            libc::S_IFLNK => InodeFileType::SymLink,
            libc::S_IFCHR => InodeFileType::CharDevice,
            libc::S_IFBLK => InodeFileType::BlockDevice,
            libc::S_IFIFO => InodeFileType::Fifo,
            libc::S_IFSOCK => InodeFileType::Socket,
            _ => InodeFileType::Unknown,
        }
    }
}

impl From<DeviceClass> for InodeFileType {
    fn from(class: DeviceClass) -> Self {
        match class {
            DeviceClass::Char => InodeFileType::CharDevice,
            DeviceClass::Block => InodeFileType::BlockDevice,
            DeviceClass::Misc => InodeFileType::CharDevice,
        }
    }
}
