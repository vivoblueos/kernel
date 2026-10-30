macro_rules! reg {
    (
        $addr:expr, $csr:ident
    ) => {
        /// Machine performance-monitoring event selector
        pub mod $csr {
            read_csr_as_usize!($addr);
            write_csr_as_usize!($addr);
        }
    };
}

reg!(0x323, mhpmevent3);
reg!(0x324, mhpmevent4);
reg!(0x325, mhpmevent5);
reg!(0x326, mhpmevent6);
reg!(0x327, mhpmevent7);
reg!(0x328, mhpmevent8);
reg!(0x329, mhpmevent9);
reg!(0x32A, mhpmevent10);
reg!(0x32B, mhpmevent11);
reg!(0x32C, mhpmevent12);
reg!(0x32D, mhpmevent13);
reg!(0x32E, mhpmevent14);
reg!(0x32F, mhpmevent15);
reg!(0x330, mhpmevent16);
reg!(0x331, mhpmevent17);
reg!(0x332, mhpmevent18);
reg!(0x333, mhpmevent19);
reg!(0x334, mhpmevent20);
reg!(0x335, mhpmevent21);
reg!(0x336, mhpmevent22);
reg!(0x337, mhpmevent23);
reg!(0x338, mhpmevent24);
reg!(0x339, mhpmevent25);
reg!(0x33A, mhpmevent26);
reg!(0x33B, mhpmevent27);
reg!(0x33C, mhpmevent28);
reg!(0x33D, mhpmevent29);
reg!(0x33E, mhpmevent30);
reg!(0x33F, mhpmevent31);
