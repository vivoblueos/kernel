extern crate flat_device_tree as fdt;

static MY_FDT: &[u8] = include_bytes!("../dtb/test.dtb");

fn main() {
    let fdt = fdt::Fdt::new(MY_FDT).unwrap();

    println!("This is a devicetree representation of a {}", fdt.root().unwrap().model());
    println!(
        "...which is compatible with at least: {}",
        fdt.root().unwrap().compatible().first().unwrap()
    );
    println!("...and has {} CPU(s)", fdt.cpus().count());
    println!(
        "...and has at least one memory location at: {:#X}\n",
        fdt.memory().unwrap().regions().next().unwrap().starting_address as usize
    );

    let chosen = fdt.chosen().unwrap();
    if let Some(bootargs) = chosen.bootargs() {
        println!("The bootargs are: {:?}", bootargs);
    }

    if let Some(stdout) = chosen.stdout() {
        println!(
            "It would write stdout to: {} with params: {:?}",
            stdout.node().name,
            stdout.params()
        );
    }

    let soc = fdt.find_node("/soc");
    println!("Does it have a `/soc` node? {}", if soc.is_some() { "yes" } else { "no" });
    if let Some(soc) = soc {
        println!("...and it has the following children:");
        for child in soc.children() {
            println!("    {}", child.name);
        }
    }
}
