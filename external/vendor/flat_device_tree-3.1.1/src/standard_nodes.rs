// This Source Code Form is subject to the terms of the Mozilla Public License,
// v. 2.0. If a copy of the MPL was not distributed with this file, You can
// obtain one at https://mozilla.org/MPL/2.0/.

//! Standard nodes found in many Device Tree files.

use crate::node::{CellSizes, FdtNode, NodeProperty};
use crate::parsing::{BigEndianU32, BigEndianU64, FdtData};
use crate::{Error, Fdt, Result};

/// Represents the `/chosen` node with specific helper methods
#[derive(Debug, Clone, Copy)]
pub struct Chosen<'b, 'a: 'b> {
    pub(crate) node: FdtNode<'b, 'a>,
}

impl<'b, 'a: 'b> Chosen<'b, 'a> {
    /// Contains the bootargs, if they exist
    pub fn bootargs(self) -> Option<&'a str> {
        self.node.properties().find(|n| n.name == "bootargs").and_then(|n| n.as_str())
    }

    /// Searches for the node representing `stdout`, if the property exists,
    /// attempting to resolve aliases if the node name doesn't exist as-is
    pub fn stdout(self) -> Option<StdInOutPath<'b, 'a>> {
        self.node
            .properties()
            .find(|n| n.name == "stdout-path")
            .and_then(|n| n.as_str())
            .map(Self::split_stdinout_property)
            .and_then(|(name, params)| {
                self.node.header.find_node(name).map(|node| StdInOutPath::new(node, params))
            })
    }

    /// Searches for the node representing `stdout`, if the property exists,
    /// attempting to resolve aliases if the node name doesn't exist as-is. If
    /// no `stdin` property exists, but `stdout` is present, it will return the
    /// node specified by the `stdout` property.
    pub fn stdin(self) -> Option<StdInOutPath<'b, 'a>> {
        self.node
            .properties()
            .find(|n| n.name == "stdin-path")
            .and_then(|n| n.as_str())
            .map(Self::split_stdinout_property)
            .and_then(|(name, params)| {
                self.node.header.find_node(name).map(|node| StdInOutPath::new(node, params))
            })
            .or_else(|| self.stdout())
    }

    /// Splits a stdout-path or stdin-path property into its node path and optional parameters which are seperated by a colon ':'.
    /// see https://devicetree-specification.readthedocs.io/en/latest/chapter3-devicenodes.html#chosen-node
    /// example "/soc/uart@10000000" => ("/soc/uart@10000000", None)
    /// example "/soc/uart@10000000:115200" => ("/soc/uart@10000000", Some("115200"))
    /// example "/soc/uart@10000000:115200n8r" => ("/soc/uart@10000000", Some("115200n8r"))
    fn split_stdinout_property(property: &str) -> (&str, Option<&str>) {
        property
            .split_once(':')
            .map_or_else(|| (property, None), |(name, params)| (name, Some(params)))
    }
}

pub struct StdInOutPath<'b, 'a> {
    pub(crate) node: FdtNode<'b, 'a>,
    pub(crate) params: Option<&'a str>,
}

impl<'b, 'a> StdInOutPath<'b, 'a> {
    fn new(node: FdtNode<'b, 'a>, params: Option<&'a str>) -> Self {
        Self { node, params }
    }

    pub fn node(&self) -> FdtNode<'b, 'a> {
        self.node
    }

    pub fn params(&self) -> Option<&'a str> {
        self.params
    }
}

/// Represents the root (`/`) node with specific helper methods
#[derive(Debug, Clone, Copy)]
pub struct Root<'b, 'a: 'b> {
    pub(crate) node: FdtNode<'b, 'a>,
}

impl<'b, 'a: 'b> Root<'b, 'a> {
    /// Root node cell sizes
    pub fn cell_sizes(self) -> CellSizes {
        self.node.cell_sizes()
    }

    /// `model` property
    pub fn model(self) -> &'a str {
        self.node
            .properties()
            .find(|p| p.name == "model")
            .and_then(|p| p.as_str())
            .unwrap_or_default()
    }

    /// `compatible` property
    pub fn compatible(self) -> Compatible<'a> {
        self.node.compatible().unwrap_or_default()
    }

    /// Returns an iterator over all of the available properties
    pub fn properties(self) -> impl Iterator<Item = NodeProperty<'a>> + 'b {
        self.node.properties()
    }

    /// Attempts to find the a property by its name
    pub fn property(self, name: &str) -> Option<NodeProperty<'a>> {
        self.node.properties().find(|p| p.name == name)
    }
}

/// Represents the `/aliases` node with specific helper methods
#[derive(Debug, Clone, Copy)]
pub struct Aliases<'b, 'a: 'b> {
    pub(crate) header: &'b Fdt<'a>,
    pub(crate) node: FdtNode<'b, 'a>,
}

impl<'b, 'a: 'b> Aliases<'b, 'a> {
    /// Attempt to resolve an alias to a node name
    pub fn resolve(self, alias: &str) -> Option<&'a str> {
        self.node.properties().find(|p| p.name == alias).and_then(|p| p.as_str())
    }

    /// Attempt to find the node specified by the given alias
    pub fn resolve_node(self, alias: &str) -> Option<FdtNode<'b, 'a>> {
        self.resolve(alias).and_then(|name| self.header.find_node(name))
    }

    /// Returns an iterator over all of the available aliases
    pub fn all(self) -> impl Iterator<Item = (&'a str, &'a str)> + 'b {
        self.node.properties().filter_map(|p| Some((p.name, p.as_str()?)))
    }
}

/// Represents a `/cpus/cpu*` node with specific helper methods
#[derive(Debug, Clone, Copy)]
pub struct Cpu<'b, 'a: 'b> {
    pub(crate) parent: FdtNode<'b, 'a>,
    pub(crate) node: FdtNode<'b, 'a>,
}

impl<'b, 'a: 'b> Cpu<'b, 'a> {
    /// Return the IDs for the given CPU
    pub fn ids(self) -> Result<CpuIds<'a>> {
        let reg = self.node.properties().find(|p| p.name == "reg").ok_or(Error::CpuNoReg)?;

        let address_cells = self.node.parent_cell_sizes().address_cells.to_usize();

        Ok(CpuIds { reg, address_cells })
    }

    /// `clock-frequency` property
    pub fn clock_frequency(self) -> Result<usize> {
        self.node
            .properties()
            .find(|p| p.name == "clock-frequency")
            .or_else(|| self.parent.property("clock-frequency"))
            .map(|p| match p.value.len() {
                4 => Some(BigEndianU32::from_bytes(p.value)?.get() as usize),
                8 => Some(BigEndianU64::from_bytes(p.value)?.get() as usize),
                _ => None,
            })
            .ok_or(Error::BadCellSize(0))?
            .ok_or(Error::CpuNoClockHz)
    }

    /// `timebase-frequency` property
    pub fn timebase_frequency(self) -> Result<usize> {
        self.node
            .properties()
            .find(|p| p.name == "timebase-frequency")
            .or_else(|| self.parent.property("timebase-frequency"))
            .map(|p| match p.value.len() {
                4 => Some(BigEndianU32::from_bytes(p.value)?.get() as usize),
                8 => Some(BigEndianU64::from_bytes(p.value)?.get() as usize),
                _ => None,
            })
            .ok_or(Error::BadCellSize(0))?
            .ok_or(Error::CpuNoTimebaseHz)
    }

    /// Returns an iterator over all of the properties for the CPU node
    pub fn properties(self) -> impl Iterator<Item = NodeProperty<'a>> + 'b {
        self.node.properties()
    }

    /// Attempts to find the a property by its name
    pub fn property(self, name: &str) -> Option<NodeProperty<'a>> {
        self.node.properties().find(|p| p.name == name)
    }
}

/// Represents the value of the `reg` property of a `/cpus/cpu*` node which may
/// contain more than one CPU or thread ID
#[derive(Debug, Clone, Copy)]
pub struct CpuIds<'a> {
    pub(crate) reg: NodeProperty<'a>,
    pub(crate) address_cells: usize,
}

impl<'a> CpuIds<'a> {
    /// The first listed CPU ID, which will always exist
    pub fn first(self) -> Result<usize> {
        match self.address_cells {
            1 => Ok(BigEndianU32::from_bytes(self.reg.value).ok_or(Error::BadCell)?.get() as usize),
            2 => Ok(BigEndianU64::from_bytes(self.reg.value).ok_or(Error::BadCell)?.get() as usize),
            n => Err(Error::BadCellSize(n)),
        }
    }

    /// Returns an iterator over all of the listed CPU IDs
    pub fn all(self) -> impl Iterator<Item = usize> + 'a {
        let mut vals = FdtData::new(self.reg.value);
        core::iter::from_fn(move || match vals.remaining() {
            [] => None,
            _ => match self.address_cells {
                1 => Some(vals.u32()?.get() as usize),
                2 => Some(vals.u64()?.get() as usize),
                _ => None,
            },
        })
    }
}

/// Represents the `compatible` property of a node
#[derive(Clone, Copy, Debug)]
pub struct Compatible<'a> {
    pub(crate) data: &'a [u8],
}

impl<'a> Compatible<'a> {
    /// Creates a new [Compatible].
    pub const fn new() -> Self {
        Self { data: &[] }
    }

    /// First compatible string.
    pub fn first(self) -> Option<&'a str> {
        self.all().next()
    }

    /// Returns an iterator over all available compatible strings
    pub fn all(self) -> impl Iterator<Item = &'a str> {
        let mut data =
            core::str::from_utf8(self.data).ok().map(|s| s.trim_end_matches('\0').split('\0'));

        core::iter::from_fn(move || match data.as_mut() {
            Some(d) => d.next(),
            None => None,
        })
    }
}

impl<'a> Default for Compatible<'a> {
    fn default() -> Self {
        Self::new()
    }
}

/// Represents the `/memory` node with specific helper methods
#[derive(Debug, Clone, Copy)]
pub struct Memory<'b, 'a: 'b> {
    pub(crate) node: FdtNode<'b, 'a>,
}

impl<'a> Memory<'_, 'a> {
    /// Returns an iterator over all of the available memory regions
    pub fn regions(&self) -> impl Iterator<Item = MemoryRegion> + 'a {
        self.node.reg()
    }

    /// Returns the initial mapped area, if it exists
    pub fn initial_mapped_area(&self) -> Result<MappedArea> {
        let init_mapped_area =
            self.node.property("initial-mapped-area").ok_or(Error::MemoryNoInitialMapped)?;

        let mut stream = FdtData::new(init_mapped_area.value);
        let effective_address = stream.u64().ok_or(Error::MappedNoEffectiveAddr)?;
        let physical_address = stream.u64().ok_or(Error::MappedNoPhysicalAddr)?;
        let size = stream.u32().ok_or(Error::MappedNoSize)?;

        Ok(MappedArea {
            effective_address: effective_address.get() as usize,
            physical_address: physical_address.get() as usize,
            size: size.get() as usize,
        })
    }
}

/// An area described by the `initial-mapped-area` property of the `/memory`
/// node
#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(C)]
pub struct MappedArea {
    /// Effective address of the mapped area
    pub effective_address: usize,
    /// Physical address of the mapped area
    pub physical_address: usize,
    /// Size of the mapped area
    pub size: usize,
}

/// A memory region
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MemoryRegion {
    /// Starting address represented as a pointer
    pub starting_address: *const u8,
    /// Size of the memory region
    pub size: Option<usize>,
}

/// Range mapping child bus addresses to parent bus addresses
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MemoryRange {
    /// Starting address on child bus
    pub child_bus_address: usize,
    /// The high bits of the child bus' starting address, if present
    pub child_bus_address_hi: u32,
    /// Starting address on parent bus
    pub parent_bus_address: usize,
    /// Size of range
    pub size: usize,
}
