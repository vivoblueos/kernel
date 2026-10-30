//! mcycle register

read_csr_as_usize!(0xB00);
write_csr_as_usize!(0xB00);
read_composite_csr!(super::mcycleh::read(), read());
write_composite_csr!(super::mcycleh::write, write);
