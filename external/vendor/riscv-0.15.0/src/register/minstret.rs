//! minstret register

read_csr_as_usize!(0xB02);
write_csr_as_usize!(0xB02);
read_composite_csr!(super::minstreth::read(), read());
write_composite_csr!(super::minstreth::write, write);
