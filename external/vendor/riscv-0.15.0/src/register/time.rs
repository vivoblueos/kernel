//! time register

read_csr_as_usize!(0xC01);
read_composite_csr!(super::timeh::read(), read());
