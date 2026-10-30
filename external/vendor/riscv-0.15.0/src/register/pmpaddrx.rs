macro_rules! reg {
    (
        $addr:expr, $csr:ident
    ) => {
        /// Physical memory protection address register
        pub mod $csr {
            read_csr_as_usize!($addr);
            write_csr_as_usize!($addr);
        }
    };
}

reg!(0x3B0, pmpaddr0);
reg!(0x3B1, pmpaddr1);
reg!(0x3B2, pmpaddr2);
reg!(0x3B3, pmpaddr3);
reg!(0x3B4, pmpaddr4);
reg!(0x3B5, pmpaddr5);
reg!(0x3B6, pmpaddr6);
reg!(0x3B7, pmpaddr7);
reg!(0x3B8, pmpaddr8);
reg!(0x3B9, pmpaddr9);
reg!(0x3BA, pmpaddr10);
reg!(0x3BB, pmpaddr11);
reg!(0x3BC, pmpaddr12);
reg!(0x3BD, pmpaddr13);
reg!(0x3BE, pmpaddr14);
reg!(0x3BF, pmpaddr15);
