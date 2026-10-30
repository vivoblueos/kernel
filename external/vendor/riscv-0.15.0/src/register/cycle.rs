//! cycle register
//!
//! Shadow of mcycle register
//! must have `scounteren::cy` or `mcounteren::cy` bit enabled depending on whether
//! S-mode is implemented or not

read_csr_as_usize!(0xC00);
read_composite_csr!(super::cycleh::read(), read());
