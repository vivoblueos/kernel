// This Source Code Form is subject to the terms of the Mozilla Public License,
// v. 2.0. If a copy of the MPL was not distributed with this file, You can
// obtain one at https://mozilla.org/MPL/2.0/.

//! # `flat_device_tree`
//!
//! **NOTE** Friendly fork of [`fdt`](https://github.com/repnop/fdt).
//!
//! A pure-Rust `#![no_std]` crate for parsing Flattened Devicetrees, with the goal of having a
//! very ergonomic and idiomatic API.
//!
//! [![crates.io](https://img.shields.io/crates/v/flat_device_tree.svg)](https://crates.io/crates/flat_device_tree) [![Documentation](https://docs.rs/flat_device_tree/badge.svg)](https://docs.rs/flat_device_tree) [![Build](https://ci.codeberg.org/api/badges/13272/status.svg)](https://ci.codeberg.org/repos/13272)
//!
//! ## License
//!
//! This crate is licensed under the Mozilla Public License 2.0 (see the LICENSE file).
//!
//! ## Example
//!
//! ```rust,no_run
//! extern crate flat_device_tree as fdt;
//!
//! static MY_FDT: &[u8] = include_bytes!("../dtb/test.dtb");
//!
//! fn main() {
//!     let fdt = fdt::Fdt::new(MY_FDT).unwrap();
//!
//!     println!("This is a devicetree representation of a {}", fdt.root().unwrap().model());
//!     println!("...which is compatible with at least: {}", fdt.root().unwrap().compatible().first().unwrap());
//!     println!("...and has {} CPU(s)", fdt.cpus().count());
//!     println!(
//!         "...and has at least one memory location at: {:#X}\n",
//!         fdt.memory().unwrap().regions().next().unwrap().starting_address as usize
//!     );
//!
//!     let chosen = fdt.chosen().unwrap();
//!     if let Some(bootargs) = chosen.bootargs() {
//!         println!("The bootargs are: {:?}", bootargs);
//!     }
//!
//!     if let Some(stdout) = chosen.stdout() {
//!         println!("It would write stdout to: {}", stdout.node().name);
//!     }
//!
//!     let soc = fdt.find_node("/soc");
//!     println!("Does it have a `/soc` node? {}", if soc.is_some() { "yes" } else { "no" });
//!     if let Some(soc) = soc {
//!         println!("...and it has the following children:");
//!         for child in soc.children() {
//!             println!("    {}", child.name);
//!         }
//!     }
//! }
//! ```

#![no_std]

use core::ffi::CStr;

#[cfg(test)]
mod tests;

mod error;
pub mod node;
mod parsing;
pub mod standard_nodes;

#[cfg(feature = "pretty-printing")]
mod pretty_print;

pub use error::*;
use node::MemoryReservation;
use parsing::{BigEndianU32, FdtData};
use standard_nodes::{Aliases, Chosen, Cpu, Memory, Root};

/// A flattened devicetree located somewhere in memory
///
/// Note on `Debug` impl: by default the `Debug` impl of this struct will not
/// print any useful information, if you would like a best-effort tree print
/// which looks similar to `dtc`'s output, enable the `pretty-printing` feature
#[derive(Clone, Copy)]
pub struct Fdt<'a> {
    data: &'a [u8],
    header: FdtHeader,
}

impl core::fmt::Debug for Fdt<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        #[cfg(feature = "pretty-printing")]
        pretty_print::print_node(f, self.root()?.node, 0)?;

        #[cfg(not(feature = "pretty-printing"))]
        f.debug_struct("Fdt").finish_non_exhaustive()?;

        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
struct FdtHeader {
    /// FDT header magic
    magic: BigEndianU32,
    /// Total size in bytes of the FDT structure
    totalsize: BigEndianU32,
    /// Offset in bytes from the start of the header to the structure block
    off_dt_struct: BigEndianU32,
    /// Offset in bytes from the start of the header to the strings block
    off_dt_strings: BigEndianU32,
    /// Offset in bytes from the start of the header to the memory reservation
    /// block
    off_mem_rsvmap: BigEndianU32,
    /// FDT version
    version: BigEndianU32,
    /// Last compatible FDT version
    last_comp_version: BigEndianU32,
    /// System boot CPU ID
    boot_cpuid_phys: BigEndianU32,
    /// Length in bytes of the strings block
    size_dt_strings: BigEndianU32,
    /// Length in bytes of the struct block
    size_dt_struct: BigEndianU32,
}

impl FdtHeader {
    fn valid_magic(&self) -> bool {
        self.magic.get() == 0xd00dfeed
    }

    fn struct_range(&self) -> core::ops::Range<usize> {
        let start = self.off_dt_struct.get() as usize;
        let end = start + self.size_dt_struct.get() as usize;

        start..end
    }

    fn strings_range(&self) -> core::ops::Range<usize> {
        let start = self.off_dt_strings.get() as usize;
        let end = start + self.size_dt_strings.get() as usize;

        start..end
    }

    fn from_bytes(bytes: &mut FdtData<'_>) -> Option<Self> {
        Some(Self {
            magic: bytes.u32()?,
            totalsize: bytes.u32()?,
            off_dt_struct: bytes.u32()?,
            off_dt_strings: bytes.u32()?,
            off_mem_rsvmap: bytes.u32()?,
            version: bytes.u32()?,
            last_comp_version: bytes.u32()?,
            boot_cpuid_phys: bytes.u32()?,
            size_dt_strings: bytes.u32()?,
            size_dt_struct: bytes.u32()?,
        })
    }
}

impl<'a> Fdt<'a> {
    /// Construct a new `Fdt` from a byte buffer
    ///
    /// Note: this function does ***not*** require that the data be 4-byte
    /// aligned
    pub fn new(data: &'a [u8]) -> Result<Self> {
        let mut stream = FdtData::new(data);
        let header = FdtHeader::from_bytes(&mut stream).ok_or(Error::BufferTooSmall)?;

        if !header.valid_magic() {
            Err(Error::BadMagic)
        } else if data.len() < header.totalsize.get() as usize {
            Err(Error::BufferTooSmall)
        } else {
            Ok(Self { data, header })
        }
    }

    /// # Safety
    /// This function performs a read to verify the magic value. If the pointer
    /// is invalid this can result in undefined behavior.
    ///
    /// Note: this function does ***not*** require that the data be 4-byte
    /// aligned
    pub unsafe fn from_ptr(ptr: *const u8) -> Result<Self> {
        if ptr.is_null() {
            return Err(Error::BadPtr);
        }

        let tmp_header = core::slice::from_raw_parts(ptr, core::mem::size_of::<FdtHeader>());
        let real_size =
            FdtHeader::from_bytes(&mut FdtData::new(tmp_header)).unwrap().totalsize.get() as usize;

        Self::new(core::slice::from_raw_parts(ptr, real_size))
    }

    /// Return reference to raw data. This can be used to obtain the original pointer passed to
    /// [Fdt::from_ptr].
    ///
    /// # Example
    /// ```
    /// # extern crate flat_device_tree as fdt;
    /// # let fdt_ref: &[u8] = include_bytes!("../dtb/test.dtb");
    /// # let original_pointer = fdt_ref.as_ptr();
    /// let fdt = unsafe{fdt::Fdt::from_ptr(original_pointer)}.unwrap();
    /// assert_eq!(fdt.raw_data().as_ptr(), original_pointer);
    /// ```
    pub fn raw_data(&self) -> &'a [u8] {
        self.data
    }

    /// Return the `/aliases` node, if one exists
    pub fn aliases(&self) -> Option<Aliases<'_, 'a>> {
        Some(Aliases {
            node: node::find_node(&mut FdtData::new(self.structs_block()), "/aliases", self, None)?,
            header: self,
        })
    }

    /// Searches for the `/chosen` node, which is always available
    pub fn chosen(&self) -> Result<Chosen<'_, 'a>> {
        node::find_node(&mut FdtData::new(self.structs_block()), "/chosen", self, None)
            .map(|node| Chosen { node })
            .ok_or(Error::MissingChosen)
    }

    /// Return the `/cpus` node, which is always available
    pub fn cpus(&self) -> impl Iterator<Item = Cpu<'_, 'a>> {
        let mut cpus = self.find_node("/cpus").map(|parent| {
            parent.children().filter_map(move |c| {
                if c.name.split('@').next().unwrap() == "cpu" {
                    Some(Cpu { parent, node: c })
                } else {
                    None
                }
            })
        });

        core::iter::from_fn(move || match cpus.as_mut() {
            Some(cpu) => cpu.next(),
            None => None,
        })
    }

    /// Returns the memory node, which is always available
    pub fn memory(&self) -> Result<Memory<'_, 'a>> {
        Ok(Memory { node: self.find_node("/memory").ok_or(Error::MissingMemory)? })
    }

    /// Returns an iterator over the memory reservations
    pub fn memory_reservations(&self) -> impl Iterator<Item = MemoryReservation> + 'a {
        let mut stream = FdtData::new(&self.data[self.header.off_mem_rsvmap.get() as usize..]);
        let mut done = false;

        core::iter::from_fn(move || {
            if stream.is_empty() || done {
                return None;
            }

            let res = MemoryReservation::from_bytes(&mut stream)?;

            if res.address() as usize == 0 && res.size() == 0 {
                done = true;
                return None;
            }

            Some(res)
        })
    }

    /// Return the root (`/`) node, which is always available
    pub fn root(&self) -> Result<Root<'_, 'a>> {
        Ok(Root { node: self.find_node("/").ok_or(Error::MissingRoot)? })
    }

    /// Returns the first node that matches the node path, if you want all that
    /// match the path, use `find_all_nodes`. This will automatically attempt to
    /// resolve aliases if `path` is not found.
    ///
    /// Node paths must begin with a leading `/` and are ASCII only. Passing in
    /// an invalid node path or non-ASCII node name in the path will return
    /// `None`, as they will not be found within the devicetree structure.
    ///
    /// Note: if the address of a node name is left out, the search will find
    /// the first node that has a matching name, ignoring the address portion if
    /// it exists.
    pub fn find_node(&self, path: &str) -> Option<node::FdtNode<'_, 'a>> {
        let node = node::find_node(&mut FdtData::new(self.structs_block()), path, self, None);
        node.or_else(|| self.aliases()?.resolve_node(path))
    }

    /// Searches for a node which contains a `compatible` property and contains
    /// one of the strings inside of `with`
    pub fn find_compatible(&self, with: &[&str]) -> Option<node::FdtNode<'_, 'a>> {
        self.all_nodes().find(|n| {
            n.compatible().and_then(|compats| compats.all().find(|c| with.contains(c))).is_some()
        })
    }

    /// Searches for the given `phandle`
    pub fn find_phandle(&self, phandle: u32) -> Option<node::FdtNode<'_, 'a>> {
        self.all_nodes().find(|n| {
            n.properties()
                .find(|p| p.name == "phandle")
                .and_then(|p| Some(BigEndianU32::from_bytes(p.value)?.get() == phandle))
                .unwrap_or(false)
        })
    }

    /// Returns an iterator over all of the available nodes with the given path.
    /// This does **not** attempt to find any node with the same name as the
    /// provided path, if you're looking to do that, [`Fdt::all_nodes`] will
    /// allow you to iterate over each node's name and filter for the desired
    /// node(s).
    ///
    /// For example:
    /// ```rust
    /// # extern crate flat_device_tree as fdt;
    /// static MY_FDT: &[u8] = include_bytes!("../dtb/test.dtb");
    ///
    /// let fdt = fdt::Fdt::new(MY_FDT).unwrap();
    ///
    /// for node in fdt.find_all_nodes("/soc/virtio_mmio") {
    ///     println!("{}", node.name);
    /// }
    /// ```
    /// prints:
    /// ```notrust
    /// virtio_mmio@10008000
    /// virtio_mmio@10007000
    /// virtio_mmio@10006000
    /// virtio_mmio@10005000
    /// virtio_mmio@10004000
    /// virtio_mmio@10003000
    /// virtio_mmio@10002000
    /// virtio_mmio@10001000
    /// ```
    pub fn find_all_nodes(&self, path: &'a str) -> impl Iterator<Item = node::FdtNode<'_, 'a>> {
        let mut done = false;
        let only_root = path == "/";
        let valid_path = path.chars().fold(0, |acc, c| acc + if c == '/' { 1 } else { 0 }) >= 1;

        let mut path_split = path.rsplitn(2, '/');
        let child_name = path_split.next().unwrap();
        let parent = match path_split.next() {
            Some("") => self.root().ok().map(|root| root.node),
            Some(s) => node::find_node(&mut FdtData::new(self.structs_block()), s, self, None),
            None => None,
        };

        let (parent, bad_parent) = match parent {
            Some(parent) => (parent, false),
            None => (self.find_node("/").unwrap(), true),
        };

        let mut child_iter = parent.children();

        core::iter::from_fn(move || {
            if done || !valid_path || bad_parent {
                return None;
            }

            if only_root {
                done = true;
                return self.find_node("/");
            }

            let mut ret = None;

            #[allow(clippy::while_let_on_iterator)]
            while let Some(child) = child_iter.next() {
                if child.name.split('@').next()? == child_name {
                    ret = Some(child);
                    break;
                }
            }

            ret
        })
    }

    /// Returns an iterator over all of the nodes in the devicetree, depth-first
    pub fn all_nodes(&self) -> impl Iterator<Item = node::FdtNode<'_, 'a>> {
        node::all_nodes(self)
    }

    /// Returns an iterator over all of the strings inside of the strings block
    pub fn strings(&self) -> impl Iterator<Item = &'a str> {
        let mut blocks = core::str::from_utf8(self.strings_block())
            .ok()
            .map(|s| s.trim_end_matches('\0').split('\0'));

        core::iter::from_fn(move || match blocks.as_mut() {
            Some(block) => block.next(),
            None => None,
        })
    }

    /// Total size of the devicetree in bytes
    pub fn total_size(&self) -> usize {
        self.header.totalsize.get() as usize
    }

    fn cstr_at_offset(&self, offset: usize) -> &'a CStr {
        CStr::from_bytes_until_nul(self.strings_block().get(offset..).unwrap_or_default())
            .unwrap_or_default()
    }

    fn str_at_offset(&self, offset: usize) -> &'a str {
        self.cstr_at_offset(offset).to_str().unwrap_or_default()
    }

    fn strings_block(&self) -> &'a [u8] {
        self.data.get(self.header.strings_range()).unwrap_or_default()
    }

    fn structs_block(&self) -> &'a [u8] {
        self.data.get(self.header.struct_range()).unwrap_or_default()
    }
}
