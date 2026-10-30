// This Source Code Form is subject to the terms of the Mozilla Public License,
// v. 2.0. If a copy of the MPL was not distributed with this file, You can
// obtain one at https://mozilla.org/MPL/2.0/.

//! Device Tree node parsing and manipulation.

use core::ffi::CStr;

use crate::parsing::{BigEndianU32, BigEndianU64, FdtData};
use crate::standard_nodes::{Compatible, MemoryRange, MemoryRegion};
use crate::{Error, Fdt, Result};

mod cell_size;

pub use cell_size::*;

const FDT_BEGIN_NODE: u32 = 1;
const FDT_END_NODE: u32 = 2;
const FDT_PROP: u32 = 3;
pub(crate) const FDT_NOP: u32 = 4;
const FDT_END: u32 = 5;

#[derive(Debug, Clone, Copy)]
#[repr(C)]
struct FdtProperty {
    len: BigEndianU32,
    name_offset: BigEndianU32,
}

impl FdtProperty {
    fn from_bytes(bytes: &mut FdtData<'_>) -> Option<Self> {
        let len = bytes.u32()?;
        let name_offset = bytes.u32()?;

        Some(Self { len, name_offset })
    }
}

/// A devicetree node
#[derive(Debug, Clone, Copy)]
pub struct FdtNode<'b, 'a: 'b> {
    pub name: &'a str,
    pub(crate) header: &'b Fdt<'a>,
    props: &'a [u8],
    parent_props: Option<&'a [u8]>,
}

#[cfg(feature = "pretty-printing")]
impl core::fmt::Display for FdtNode<'_, '_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        crate::pretty_print::print_node(f, *self, 0)?;
        Ok(())
    }
}

impl<'b, 'a: 'b> FdtNode<'b, 'a> {
    fn new(
        name: &'a str,
        header: &'b Fdt<'a>,
        props: &'a [u8],
        parent_props: Option<&'a [u8]>,
    ) -> Self {
        Self { name, header, props, parent_props }
    }

    /// Returns an iterator over the available properties of the node
    pub fn properties(self) -> impl Iterator<Item = NodeProperty<'a>> + 'b {
        let mut stream = FdtData::new(self.props);
        let mut done = false;

        core::iter::from_fn(move || {
            if stream.is_empty() || done {
                return None;
            }

            while stream.peek_u32()?.get() == FDT_NOP {
                stream.skip(4);
            }

            if stream.peek_u32()?.get() == FDT_PROP {
                NodeProperty::parse(&mut stream, self.header).ok()
            } else {
                done = true;
                None
            }
        })
    }

    /// Attempts to find the a property by its name
    pub fn property(self, name: &str) -> Option<NodeProperty<'a>> {
        self.properties().find(|p| p.name == name)
    }

    /// Returns an iterator over the children of the current node
    pub fn children(self) -> impl Iterator<Item = FdtNode<'b, 'a>> {
        let mut stream = FdtData::new(self.props);

        while stream.peek_u32().unwrap_or_default().get() == FDT_NOP {
            stream.skip(4);
        }

        while stream.peek_u32().unwrap_or_default().get() == FDT_PROP {
            NodeProperty::parse(&mut stream, self.header).ok();
        }

        let mut done = false;

        core::iter::from_fn(move || {
            if stream.is_empty() || done {
                return None;
            }

            while stream.peek_u32()?.get() == FDT_NOP {
                stream.skip(4);
            }

            if stream.peek_u32()?.get() == FDT_BEGIN_NODE {
                let origin = stream.remaining();
                let ret = {
                    stream.skip(4);
                    let unit_name =
                        CStr::from_bytes_until_nul(stream.remaining()).ok()?.to_str().ok()?;
                    let full_name_len = unit_name.len() + 1;
                    stream.skip(full_name_len);

                    if full_name_len % 4 != 0 {
                        stream.skip(4 - (full_name_len % 4));
                    }

                    Some(Self::new(unit_name, self.header, stream.remaining(), Some(self.props)))
                };

                stream = FdtData::new(origin);

                skip_current_node(&mut stream, self.header);

                ret
            } else {
                done = true;
                None
            }
        })
    }

    /// `reg` property
    ///
    /// Important: this method assumes that the value(s) inside the `reg`
    /// property represent CPU-addressable addresses that are able to fit within
    /// the platform's pointer size (e.g. `#address-cells` and `#size-cells` are
    /// less than or equal to 2 for a 64-bit platform). If this is not the case
    /// or you're unsure of whether this applies to the node, it is recommended
    /// to use the [`FdtNode::property`] method to extract the raw value slice
    /// or use the provided [`FdtNode::raw_reg`] helper method to give you an
    /// iterator over the address and size slices. One example of where this
    /// would return `None` for a node is a `pci` child node which contains the
    /// PCI address information in the `reg` property, of which the address has
    /// an `#address-cells` value of 3.
    pub fn reg(self) -> impl Iterator<Item = MemoryRegion> + 'a {
        let sizes = self.parent_cell_sizes();

        let mut reg = self.properties().find(|p| p.name == "reg").map(|p| FdtData::new(p.value));

        core::iter::from_fn(move || match reg.as_mut() {
            Some(stream) => {
                let starting_address = match sizes.address_cells {
                    CellSize::One => Some(stream.u32()?.get() as usize),
                    CellSize::Two => Some(stream.u64()?.get() as usize),
                    _ => None,
                }? as *const u8;

                let size = match sizes.size_cells {
                    CellSize::None => Some(None),
                    CellSize::One => Some(Some(stream.u32()?.get() as usize)),
                    CellSize::Two => Some(Some(stream.u64()?.get() as usize)),
                    _ => None,
                }?;

                Some(MemoryRegion { starting_address, size })
            }
            None => None,
        })
    }

    /// Parses the `ranges` property as an iterator over [MemoryRange].
    pub fn ranges(self) -> impl Iterator<Item = MemoryRange> + 'a {
        let sizes = self.cell_sizes();
        let parent_sizes = self.parent_cell_sizes();

        let mut ranges =
            self.properties().find(|p| p.name == "ranges").map(|p| FdtData::new(p.value));

        core::iter::from_fn(move || match ranges.as_mut() {
            Some(stream) => {
                let (child_bus_address_hi, child_bus_address) = match sizes.address_cells {
                    CellSize::One => Some((0, stream.u32()?.get() as usize)),
                    CellSize::Two => Some((0, stream.u64()?.get() as usize)),
                    CellSize::Three => Some((stream.u32()?.get(), stream.u64()?.get() as usize)),
                    _ => None,
                }?;

                let parent_bus_address = match parent_sizes.address_cells {
                    CellSize::One => Some(stream.u32()?.get() as usize),
                    CellSize::Two => Some(stream.u64()?.get() as usize),
                    _ => None,
                }?;

                let size = match sizes.size_cells {
                    CellSize::One => Some(stream.u32()?.get() as usize),
                    CellSize::Two => Some(stream.u64()?.get() as usize),
                    _ => None,
                }?;

                Some(MemoryRange {
                    child_bus_address,
                    child_bus_address_hi,
                    parent_bus_address,
                    size,
                })
            }
            None => None,
        })
    }

    /// Convenience method that provides an iterator over the raw bytes for the
    /// address and size values inside of the `reg` property
    pub fn raw_reg(self) -> impl Iterator<Item = RawReg<'a>> + 'a {
        let sizes = self.parent_cell_sizes();

        let mut reg = self.property("reg").map(|p| FdtData::new(p.value));
        core::iter::from_fn(move || match reg.as_mut() {
            Some(stream) => Some(RawReg {
                address: stream.take(sizes.address_cells.to_usize() * 4)?,
                size: stream.take(sizes.size_cells.to_usize() * 4)?,
            }),
            None => None,
        })
    }

    /// `compatible` property
    pub fn compatible(self) -> Option<Compatible<'a>> {
        let mut s = None;
        for prop in self.properties() {
            if prop.name == "compatible" {
                s = Some(Compatible { data: prop.value });
            }
        }

        s
    }

    /// Cell sizes for child nodes
    pub fn cell_sizes(self) -> CellSizes {
        let mut cell_sizes = CellSizes::default();

        for property in self.properties() {
            match property.name {
                "#address-cells" => {
                    cell_sizes.address_cells =
                        BigEndianU32::from_bytes(property.value).unwrap_or_default().get().into();
                }
                "#size-cells" => {
                    cell_sizes.size_cells =
                        BigEndianU32::from_bytes(property.value).unwrap_or_default().get().into();
                }
                _ => {}
            }
        }

        cell_sizes
    }

    /// Searches for the interrupt parent, if the node contains one
    pub fn interrupt_parent(self) -> Option<FdtNode<'b, 'a>> {
        self.properties()
            .find(|p| p.name == "interrupt-parent")
            .and_then(|p| self.header.find_phandle(BigEndianU32::from_bytes(p.value)?.get()))
    }

    /// `#interrupt-cells` property
    pub fn interrupt_cells(self) -> Option<usize> {
        let mut interrupt_cells = None;

        if let Some(prop) = self.property("#interrupt-cells") {
            interrupt_cells = BigEndianU32::from_bytes(prop.value).map(|n| n.get() as usize)
        }

        interrupt_cells
    }

    /// Searches for the `interrupts` property.
    pub fn interrupts(self) -> impl Iterator<Item = usize> + 'a {
        let sizes = self.parent_interrupt_cells();

        let mut interrupt =
            self.properties().find(|p| p.name == "interrupts").map(|p| FdtData::new(p.value));

        core::iter::from_fn(move || match interrupt.as_mut() {
            Some(stream) => match sizes {
                Some(1) => Some(stream.u32()?.get() as usize),
                Some(2) => Some(stream.u64()?.get() as usize),
                _ => None,
            },
            None => None,
        })
    }

    pub(crate) fn parent_cell_sizes(self) -> CellSizes {
        let mut cell_sizes = CellSizes::default();

        if let Some(parent) = self.parent_props {
            let parent =
                FdtNode { name: "", props: parent, header: self.header, parent_props: None };
            cell_sizes = parent.cell_sizes();
        }

        cell_sizes
    }

    pub(crate) fn parent_interrupt_cells(self) -> Option<usize> {
        let mut interrupt_cells = None;
        let parent = self
            .property("interrupt-parent")
            .and_then(|p| self.header.find_phandle(BigEndianU32::from_bytes(p.value)?.get()))
            .or_else(|| {
                // attempt to find the `interrupt-parent` property in the parent node
                let p = FdtNode::new("", self.header, self.parent_props?, None)
                    .property("interrupt-parent")?;
                self.header.find_phandle(BigEndianU32::from_bytes(p.value)?.get())
            });

        if let Some(size) = parent.and_then(|parent| parent.interrupt_cells()) {
            interrupt_cells = Some(size);
        }

        interrupt_cells
    }
}

/// The number of cells (big endian u32s) that addresses and sizes take
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct CellSizes {
    /// Size of values representing an address
    pub address_cells: CellSize,
    /// Size of values representing a size
    pub size_cells: CellSize,
}

impl CellSizes {
    /// Creates a new [CellSizes].
    pub const fn new() -> Self {
        Self { address_cells: CellSize::Two, size_cells: CellSize::One }
    }
}

impl Default for CellSizes {
    fn default() -> Self {
        Self::new()
    }
}

/// A raw `reg` property value set
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct RawReg<'a> {
    /// Big-endian encoded bytes making up the address portion of the property.
    /// Length will always be a multiple of 4 bytes.
    pub address: &'a [u8],
    /// Big-endian encoded bytes making up the size portion of the property.
    /// Length will always be a multiple of 4 bytes.
    pub size: &'a [u8],
}

pub(crate) fn find_node<'b, 'a: 'b>(
    stream: &mut FdtData<'a>,
    name: &str,
    header: &'b Fdt<'a>,
    parent_props: Option<&'a [u8]>,
) -> Option<FdtNode<'b, 'a>> {
    let mut parts = name.splitn(2, '/');
    let looking_for = parts.next()?;

    stream.skip_nops();

    let curr_data = stream.remaining();

    match stream.u32()?.get() {
        FDT_BEGIN_NODE => {}
        _ => return None,
    }

    let unit_name = CStr::from_bytes_until_nul(stream.remaining()).ok()?.to_str().ok()?;

    let full_name_len = unit_name.len() + 1;
    skip_4_aligned(stream, full_name_len);

    let looking_contains_addr = looking_for.contains('@');
    let addr_name_same = unit_name == looking_for;
    let base_name_same = unit_name.split('@').next()? == looking_for;

    if (looking_contains_addr && !addr_name_same) || (!looking_contains_addr && !base_name_same) {
        *stream = FdtData::new(curr_data);
        skip_current_node(stream, header)?;

        return None;
    }

    let next_part = match parts.next() {
        None | Some("") => {
            return Some(FdtNode::new(unit_name, header, stream.remaining(), parent_props))
        }
        Some(part) => part,
    };

    stream.skip_nops();

    let parent_props = Some(stream.remaining());

    while stream.peek_u32()?.get() == FDT_PROP {
        let _ = NodeProperty::parse(stream, header);
    }

    while stream.peek_u32()?.get() == FDT_BEGIN_NODE {
        if let Some(p) = find_node(stream, next_part, header, parent_props) {
            return Some(p);
        }
    }

    stream.skip_nops();

    if stream.u32()?.get() != FDT_END_NODE {
        return None;
    }

    None
}

// FIXME: this probably needs refactored
pub(crate) fn all_nodes<'b, 'a: 'b>(header: &'b Fdt<'a>) -> impl Iterator<Item = FdtNode<'b, 'a>> {
    let mut stream = FdtData::new(header.structs_block());
    let mut done = false;
    let mut parents: [&[u8]; 64] = [&[]; 64];
    let mut parent_index = 0;

    core::iter::from_fn(move || {
        if stream.is_empty() || done {
            return None;
        }

        while stream.peek_u32()?.get() == FDT_END_NODE {
            parent_index -= 1;
            stream.skip(4);
        }

        if stream.peek_u32()?.get() == FDT_END {
            done = true;
            return None;
        }

        while stream.peek_u32()?.get() == FDT_NOP {
            stream.skip(4);
        }

        match stream.u32()?.get() {
            FDT_BEGIN_NODE => {}
            _ => return None,
        }

        let unit_name = CStr::from_bytes_until_nul(stream.remaining()).ok()?.to_str().ok()?;
        let full_name_len = unit_name.len() + 1;
        skip_4_aligned(&mut stream, full_name_len);

        let curr_node = stream.remaining();

        parent_index += 1;
        parents[parent_index] = curr_node;

        while stream.peek_u32()?.get() == FDT_NOP {
            stream.skip(4);
        }

        while stream.peek_u32()?.get() == FDT_PROP {
            NodeProperty::parse(&mut stream, header).ok()?;
        }

        Some(FdtNode {
            name: if unit_name.is_empty() { "/" } else { unit_name },
            header,
            parent_props: match parent_index {
                1 => None,
                _ => parents.get(parent_index.saturating_sub(1)).copied(),
            },
            props: curr_node,
        })
    })
}

pub(crate) fn skip_current_node<'a>(stream: &mut FdtData<'a>, header: &Fdt<'a>) -> Option<()> {
    if stream.u32()?.get() == FDT_BEGIN_NODE { Some(()) } else { None }?;

    let unit_name = CStr::from_bytes_until_nul(stream.remaining()).ok()?.to_str().ok()?;
    let full_name_len = unit_name.len().saturating_add(1);
    skip_4_aligned(stream, full_name_len);

    while stream.peek_u32()?.get() == FDT_PROP {
        NodeProperty::parse(stream, header).ok()?;
    }

    while stream.peek_u32()?.get() == FDT_BEGIN_NODE {
        skip_current_node(stream, header);
    }

    stream.skip_nops();

    if stream.u32()?.get() == FDT_END_NODE {
        Some(())
    } else {
        None
    }
}

/// A node property
#[derive(Debug, Clone, Copy)]
pub struct NodeProperty<'a> {
    /// Property name
    pub name: &'a str,
    /// Property value
    pub value: &'a [u8],
}

impl<'a> NodeProperty<'a> {
    /// Attempt to parse the property value as a `usize`
    pub fn as_usize(self) -> Option<usize> {
        match self.value.len() {
            4 => BigEndianU32::from_bytes(self.value).map(|i| i.get() as usize),
            8 => BigEndianU64::from_bytes(self.value).map(|i| i.get() as usize),
            _ => None,
        }
    }

    /// Attempts to parse the property value as a list of [`u64`].
    ///
    /// Only handles property values with uniform cell sizes.
    ///
    /// For `prop-encoded-array` property values use [iter_prop_encoded](Self::iter_prop_encoded).
    pub fn iter_cell_size(self, cell_size: CellSize) -> impl Iterator<Item = u64> + 'a {
        let mut cells = FdtData::new(self.value);

        core::iter::from_fn(move || match cell_size {
            CellSize::One => Some(cells.u32()?.get() as u64),
            CellSize::Two => Some(cells.u64()?.get()),
            _ => None,
        })
    }

    /// Attempts to parse the property value as a `prop-encoded-array` list of [`u64`] tuples.
    pub fn iter_prop_encoded(self, cell_sizes: CellSizes) -> impl Iterator<Item = (u64, u64)> + 'a {
        let mut cells = FdtData::new(self.value);

        core::iter::from_fn(move || {
            let addr = match cell_sizes.address_cells {
                CellSize::One => Some(cells.u32()?.get() as u64),
                CellSize::Two => Some(cells.u64()?.get()),
                _ => None,
            }?;

            let size = match cell_sizes.size_cells {
                CellSize::One => Some(cells.u32()?.get() as u64),
                CellSize::Two => Some(cells.u64()?.get()),
                _ => None,
            }?;

            Some((addr, size))
        })
    }

    /// Attempt to parse the property value as a `&str`
    pub fn as_str(self) -> Option<&'a str> {
        core::str::from_utf8(self.value).map(|s| s.trim_end_matches('\0')).ok()
    }

    /// Attempts to parse the property value as a list of [`&str`].
    pub fn iter_str(self) -> impl Iterator<Item = &'a str> + 'a {
        let mut strs = self.as_str().map(|s| s.split('\0'));

        core::iter::from_fn(move || match strs.as_mut() {
            Some(s) => s.next(),
            None => None,
        })
    }

    fn parse(stream: &mut FdtData<'a>, header: &Fdt<'a>) -> Result<Self> {
        match stream.u32() {
            Some(p) if p.get() == FDT_PROP => Ok(()),
            Some(other) => Err(Error::BadPropTag((other.get(), FDT_PROP))),
            None => Err(Error::BadPropTag((0, FDT_PROP))),
        }?;

        let prop = FdtProperty::from_bytes(stream).ok_or(Error::MissingProperty)?;
        let data_len = prop.len.get() as usize;

        let data = stream.remaining().get(..data_len).unwrap_or_default();

        skip_4_aligned(stream, data_len);

        Ok(NodeProperty {
            name: header.str_at_offset(prop.name_offset.get() as usize),
            value: data,
        })
    }
}

/// A memory reservation
#[derive(Debug)]
#[repr(C)]
pub struct MemoryReservation {
    pub(crate) address: BigEndianU64,
    pub(crate) size: BigEndianU64,
}

impl MemoryReservation {
    /// Pointer representing the memory reservation address
    pub fn address(&self) -> *const u8 {
        self.address.get() as usize as *const u8
    }

    /// Size of the memory reservation
    pub fn size(&self) -> usize {
        self.size.get() as usize
    }

    pub(crate) fn from_bytes(bytes: &mut FdtData<'_>) -> Option<Self> {
        let address = bytes.u64()?;
        let size = bytes.u64()?;

        Some(Self { address, size })
    }
}

fn skip_4_aligned(stream: &mut FdtData<'_>, len: usize) {
    stream.skip((len + 3) & !0x3);
}
