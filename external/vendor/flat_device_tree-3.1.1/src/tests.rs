// This Source Code Form is subject to the terms of the Mozilla Public License,
// v. 2.0. If a copy of the MPL was not distributed with this file, You can
// obtain one at https://mozilla.org/MPL/2.0/.

extern crate std;

use crate::{node::RawReg, standard_nodes::*, *};

static TEST: &[u8] = include_bytes!("../dtb/test.dtb");
static ISSUE_3: &[u8] = include_bytes!("../dtb/issue-3.dtb");
static SIFIVE: &[u8] = include_bytes!("../dtb/sifive.dtb");

#[test]
fn returns_fdt() {
    assert!(Fdt::new(TEST).is_ok());
}

#[test]
fn finds_root_node() {
    let fdt = Fdt::new(TEST).unwrap();
    assert!(fdt.find_node("/").is_some(), "couldn't find root node");
}

#[test]
fn finds_root_node_properties() {
    let fdt = Fdt::new(TEST).unwrap();
    let prop = fdt
        .find_node("/")
        .unwrap()
        .properties()
        .any(|p| p.name == "compatible" && p.value == b"riscv-virtio\0");

    assert!(prop);
}

#[test]
fn finds_child_of_root_node() {
    let fdt = Fdt::new(TEST).unwrap();
    assert!(fdt.find_node("/cpus").is_some(), "couldn't find cpus node");
}

#[test]
fn correct_flash_regions() {
    let fdt = Fdt::new(TEST).unwrap();
    let regions = fdt.find_node("/soc/flash").unwrap().reg().collect::<std::vec::Vec<_>>();

    assert_eq!(
        regions,
        &[
            MemoryRegion { starting_address: 0x20000000 as *const u8, size: Some(0x2000000) },
            MemoryRegion { starting_address: 0x22000000 as *const u8, size: Some(0x2000000) }
        ]
    );
}

#[test]
fn parses_populated_ranges() {
    let fdt = Fdt::new(TEST).unwrap();
    let ranges = fdt.find_node("/soc/pci").unwrap().ranges().collect::<std::vec::Vec<_>>();

    assert_eq!(
        ranges,
        &[
            MemoryRange {
                child_bus_address: 0x0000_0000_0000_0000,
                child_bus_address_hi: 0x0100_0000,
                parent_bus_address: 0x3000000,
                size: 0x10000,
            },
            MemoryRange {
                child_bus_address: 0x40000000,
                child_bus_address_hi: 0x2000000,
                parent_bus_address: 0x4000_0000,
                size: 0x4000_0000,
            }
        ]
    );
}

#[test]
fn parses_empty_ranges() {
    let fdt = Fdt::new(TEST).unwrap();
    let ranges = fdt.find_node("/soc").unwrap().ranges().collect::<std::vec::Vec<_>>();

    assert_eq!(ranges, &[]);
}

#[test]
fn finds_with_addr() {
    let fdt = Fdt::new(TEST).unwrap();
    assert_eq!(fdt.find_node("/soc/virtio_mmio@10004000").unwrap().name, "virtio_mmio@10004000");
}

#[test]
fn compatibles() {
    let fdt = Fdt::new(TEST).unwrap();
    let compat = fdt.find_node("/soc/test").unwrap().compatible().unwrap();

    std::println!("Compatible: {compat:?}");

    compat.all().enumerate().for_each(|(i, s)| {
        std::println!("Compatible[{i}]: {s}");
    });

    let res = compat.all().all(|s| ["sifive,test1", "sifive,test0", "syscon"].contains(&s));

    assert!(res);
}

#[test]
fn parent_cell_sizes() {
    let fdt = Fdt::new(TEST).unwrap();
    let regions = fdt.find_node("/memory").unwrap().reg().collect::<std::vec::Vec<_>>();

    assert_eq!(
        regions,
        &[MemoryRegion { starting_address: 0x80000000 as *const u8, size: Some(0x20000000) }]
    );
}

#[test]
fn no_properties() {
    let fdt = Fdt::new(TEST).unwrap();
    let regions = fdt.find_node("/emptyproptest").unwrap();
    assert_eq!(regions.properties().count(), 0);
}

#[test]
fn finds_all_nodes() {
    let fdt = Fdt::new(TEST).unwrap();

    let mut all_nodes: std::vec::Vec<_> = fdt.all_nodes().map(|n| n.name).collect();
    all_nodes.sort_unstable();

    assert_eq!(
        all_nodes,
        &[
            "/",
            "chosen",
            "clint@2000000",
            "cluster0",
            "core0",
            "cpu-map",
            "cpu@0",
            "cpus",
            "emptyproptest",
            "flash@20000000",
            "interrupt-controller",
            "memory@80000000",
            "pci@30000000",
            "plic@c000000",
            "poweroff",
            "reboot",
            "rtc@101000",
            "soc",
            "test@100000",
            "uart@10000000",
            "virtio_mmio@10001000",
            "virtio_mmio@10002000",
            "virtio_mmio@10003000",
            "virtio_mmio@10004000",
            "virtio_mmio@10005000",
            "virtio_mmio@10006000",
            "virtio_mmio@10007000",
            "virtio_mmio@10008000"
        ]
    )
}

#[test]
fn required_nodes() {
    let fdt = Fdt::new(TEST).unwrap();
    fdt.cpus().next().unwrap();
    fdt.memory().unwrap();
    fdt.chosen().unwrap();
}

#[test]
fn doesnt_exist() {
    let fdt = Fdt::new(TEST).unwrap();
    assert!(fdt.find_node("/this/doesnt/exist").is_none());
}

#[test]
fn raw_reg() {
    let fdt = Fdt::new(TEST).unwrap();
    let regions = fdt.find_node("/soc/flash").unwrap().raw_reg().collect::<std::vec::Vec<_>>();

    assert_eq!(
        regions,
        &[
            RawReg { address: &0x20000000u64.to_be_bytes(), size: &0x2000000u64.to_be_bytes() },
            RawReg { address: &0x22000000u64.to_be_bytes(), size: &0x2000000u64.to_be_bytes() }
        ]
    );
}

#[test]
fn issue_3() {
    let fdt = Fdt::new(ISSUE_3).unwrap();
    fdt.find_all_nodes("uart").for_each(|n| std::println!("{:?}", n));
}

#[test]
fn issue_4() {
    let fdt = Fdt::new(ISSUE_3).unwrap();
    fdt.all_nodes().for_each(|n| std::println!("{:?}", n));
}

#[test]
fn cpus() {
    let fdt = Fdt::new(TEST).unwrap();
    for cpu in fdt.cpus() {
        cpu.ids().unwrap().all().for_each(|n| std::println!("{:?}", n));
    }
}

#[test]
fn invalid_node() {
    let fdt = Fdt::new(TEST).unwrap();
    assert!(fdt.find_node("this/is/an invalid node///////////").is_none());
}

#[test]
fn aliases() {
    let fdt = Fdt::new(SIFIVE).unwrap();
    let aliases = fdt.aliases().unwrap();
    for (_, node_path) in aliases.all() {
        assert!(fdt.find_node(node_path).is_some(), "path: {:?}", node_path);
    }
}

#[test]
fn stdout() {
    let fdt = Fdt::new(TEST).unwrap();
    let stdout = fdt.chosen().unwrap().stdout().unwrap();
    assert_eq!(stdout.node().name, "uart@10000000");
    assert_eq!(stdout.params(), Some("115200"));
}

#[test]
fn stdin() {
    let fdt = Fdt::new(TEST).unwrap();
    let stdin = fdt.chosen().unwrap().stdin().unwrap();
    assert_eq!(stdin.node().name, "uart@10000000");
    assert!(stdin.params().is_none());
}

#[test]
fn node_property_str_value() {
    let fdt = Fdt::new(TEST).unwrap();
    let cpu0 = fdt.find_node("/cpus/cpu@0").unwrap();
    assert_eq!(cpu0.property("riscv,isa").unwrap().as_str().unwrap(), "rv64imafdcsu");
}

#[test]
fn model_value() {
    let fdt = Fdt::new(TEST).unwrap();
    assert_eq!(fdt.root().unwrap().model(), "riscv-virtio,qemu");
}

#[test]
fn memory_node() {
    let fdt = Fdt::new(TEST).unwrap();
    assert_eq!(fdt.memory().unwrap().regions().count(), 1);
}

#[test]
fn interrupt_cells() {
    let fdt = Fdt::new(TEST).unwrap();
    let uart = fdt.find_node("/soc/uart").unwrap();
    std::println!("{:?}", uart.parent_interrupt_cells());
    assert_eq!(uart.interrupts().collect::<std::vec::Vec<_>>(), std::vec![0xA]);
}

#[test]
fn interrupt_cells_no_interrupt_parent() {
    let fdt = Fdt::new(TEST).unwrap();
    let test = fdt.find_node("/soc/test").unwrap();
    std::println!("{:?}", test.parent_interrupt_cells());
    assert_eq!(test.interrupts().collect::<std::vec::Vec<_>>(), std::vec![0xFF]);
}

#[test]
fn property_str_list() {
    let fdt = Fdt::new(TEST).unwrap();
    let test = fdt.find_node("/soc/test").unwrap();
    let expected = ["sifive,test1", "sifive,test0", "syscon"];
    let compat = test.property("compatible").unwrap();

    assert_eq!(compat.iter_str().count(), expected.len());

    test.property("compatible").unwrap().iter_str().zip(expected).for_each(|(prop, exp)| {
        assert_eq!(prop, exp);
    });
}

#[test]
fn property_cell_size_list() {
    let fdt = Fdt::new(TEST).unwrap();
    let uart = fdt.find_node("/soc/pci").unwrap();

    let int_map_mask_list = uart
        .property("interrupt-map-mask")
        .unwrap()
        .iter_cell_size(uart.interrupt_cells().unwrap_or(1).into())
        .collect::<std::vec::Vec<u64>>();

    std::println!("{int_map_mask_list:?}");
    assert_eq!(int_map_mask_list, std::vec![0x1800, 0x00, 0x00, 0x07]);
}

#[test]
fn property_prop_encoded_list() {
    let fdt = Fdt::new(TEST).unwrap();
    let node = fdt.find_node("/soc/rtc").unwrap();

    let int_map_mask_list = node
        .property("reg")
        .unwrap()
        .iter_prop_encoded(node.parent_cell_sizes())
        .collect::<std::vec::Vec<(u64, u64)>>();

    std::println!("{int_map_mask_list:?}");
    assert_eq!(int_map_mask_list, std::vec![(0x101000, 0x1000)]);
}
