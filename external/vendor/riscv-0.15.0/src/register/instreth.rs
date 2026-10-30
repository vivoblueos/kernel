//! instreth register
//!
//! Shadow of minstreth register (rv32)
//! must have `scounteren::ir` or `mcounteren::ir` bit enabled depending on whether
//! S-mode is implemented or not

read_csr_as_usize!(0xC82);
