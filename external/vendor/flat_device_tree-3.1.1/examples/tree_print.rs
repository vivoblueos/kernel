extern crate flat_device_tree as fdt;

use fdt::node::FdtNode;

static MY_FDT: &[u8] = include_bytes!("../dtb/test.dtb");

fn main() {
    let fdt = fdt::Fdt::new(MY_FDT).unwrap();

    print_node(fdt.find_node("/").unwrap(), 0);
}

fn print_node(node: FdtNode<'_, '_>, n_spaces: usize) {
    (0..n_spaces).for_each(|_| print!(" "));
    println!("{}/", node.name);

    for child in node.children() {
        print_node(child, n_spaces + 4);
    }
}
