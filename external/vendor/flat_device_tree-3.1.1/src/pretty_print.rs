// This Source Code Form is subject to the terms of the Mozilla Public License,
// v. 2.0. If a copy of the MPL was not distributed with this file, You can
// obtain one at https://mozilla.org/MPL/2.0/.

pub fn print_node(
    f: &mut core::fmt::Formatter<'_>,
    node: crate::node::FdtNode<'_, '_>,
    n_spaces: usize,
) -> core::fmt::Result {
    write!(f, "{:width$}", ' ', width = n_spaces)?;
    writeln!(f, "{} {{", if node.name.is_empty() { "/" } else { node.name })?;
    let mut were_props = false;
    for prop in node.properties() {
        were_props = true;

        match prop.name {
            "reg" => {
                write!(f, "{:width$}reg = <", ' ', width = n_spaces + 4)?;
                for (i, reg) in node.reg().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }

                    match reg.size {
                        Some(size) => {
                            write!(f, "{:#x} {:#x}", reg.starting_address as usize, size)?
                        }
                        None => write!(f, "{:#x}", reg.starting_address as usize)?,
                    }
                }
                writeln!(f, ">")?;
            }
            "compatible" => writeln!(
                f,
                "{:width$}compatible = {:?}",
                ' ',
                prop.as_str().unwrap(),
                width = n_spaces + 4
            )?,
            name if name.contains("-cells") => {
                writeln!(
                    f,
                    "{:width$}{} = <{:#x}>",
                    ' ',
                    name,
                    prop.as_usize().unwrap(),
                    width = n_spaces + 4
                )?;
            }
            _ => match prop.as_str() {
                Some(value)
                    if (!value.is_empty() && value.chars().all(|c| c.is_ascii_graphic()))
                        || prop.value == [0] =>
                {
                    writeln!(f, "{:width$}{} = {:?}", ' ', prop.name, value, width = n_spaces + 4)?
                }
                _ => match prop.value.len() {
                    4 | 8 => writeln!(
                        f,
                        "{:width$}{} = <{:#x}>",
                        ' ',
                        prop.name,
                        prop.as_usize().unwrap(),
                        width = n_spaces + 4
                    )?,
                    _ => writeln!(
                        f,
                        "{:width$}{} = {:?}",
                        ' ',
                        prop.name,
                        prop.value,
                        width = n_spaces + 4
                    )?,
                },
            },
        }
    }

    if node.children().next().is_some() && were_props {
        writeln!(f)?;
    }

    let mut first = true;
    for child in node.children() {
        if !first {
            writeln!(f)?;
        }

        print_node(f, child, n_spaces + 4)?;
        first = false;
    }

    if n_spaces > 0 {
        write!(f, "{:width$}", ' ', width = n_spaces)?;
    }

    writeln!(f, "}};")?;

    Ok(())
}
