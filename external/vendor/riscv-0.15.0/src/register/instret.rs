//! instret register
//!
//! Shadow of minstret register
//! must have `scounteren::ir` or `mcounteren::ir` bit enabled depending on whether
//! S-mode is implemented or not

read_csr_as_usize!(0xC02);
read_composite_csr!(super::instreth::read(), read());
