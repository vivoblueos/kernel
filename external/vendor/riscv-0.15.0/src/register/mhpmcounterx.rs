macro_rules! reg {
    (
        $addr:expr, $csrl:ident, $csrh:ident
    ) => {
        /// Machine performance-monitoring counter
        pub mod $csrl {
            read_csr_as_usize!($addr);
            write_csr_as_usize!($addr);
            read_composite_csr!(super::$csrh::read(), read());
        }
    };
}

macro_rules! regh {
    (
        $addr:expr, $csrh:ident
    ) => {
        /// Upper 32 bits of machine performance-monitoring counter (RV32I only)
        pub mod $csrh {
            read_csr_as_usize_rv32!($addr);
            write_csr_as_usize_rv32!($addr);
        }
    };
}

reg!(0xB03, mhpmcounter3, mhpmcounter3h);
reg!(0xB04, mhpmcounter4, mhpmcounter4h);
reg!(0xB05, mhpmcounter5, mhpmcounter5h);
reg!(0xB06, mhpmcounter6, mhpmcounter6h);
reg!(0xB07, mhpmcounter7, mhpmcounter7h);
reg!(0xB08, mhpmcounter8, mhpmcounter8h);
reg!(0xB09, mhpmcounter9, mhpmcounter9h);
reg!(0xB0A, mhpmcounter10, mhpmcounter10h);
reg!(0xB0B, mhpmcounter11, mhpmcounter11h);
reg!(0xB0C, mhpmcounter12, mhpmcounter12h);
reg!(0xB0D, mhpmcounter13, mhpmcounter13h);
reg!(0xB0E, mhpmcounter14, mhpmcounter14h);
reg!(0xB0F, mhpmcounter15, mhpmcounter15h);
reg!(0xB10, mhpmcounter16, mhpmcounter16h);
reg!(0xB11, mhpmcounter17, mhpmcounter17h);
reg!(0xB12, mhpmcounter18, mhpmcounter18h);
reg!(0xB13, mhpmcounter19, mhpmcounter19h);
reg!(0xB14, mhpmcounter20, mhpmcounter20h);
reg!(0xB15, mhpmcounter21, mhpmcounter21h);
reg!(0xB16, mhpmcounter22, mhpmcounter22h);
reg!(0xB17, mhpmcounter23, mhpmcounter23h);
reg!(0xB18, mhpmcounter24, mhpmcounter24h);
reg!(0xB19, mhpmcounter25, mhpmcounter25h);
reg!(0xB1A, mhpmcounter26, mhpmcounter26h);
reg!(0xB1B, mhpmcounter27, mhpmcounter27h);
reg!(0xB1C, mhpmcounter28, mhpmcounter28h);
reg!(0xB1D, mhpmcounter29, mhpmcounter29h);
reg!(0xB1E, mhpmcounter30, mhpmcounter30h);
reg!(0xB1F, mhpmcounter31, mhpmcounter31h);

regh!(0xB83, mhpmcounter3h);
regh!(0xB84, mhpmcounter4h);
regh!(0xB85, mhpmcounter5h);
regh!(0xB86, mhpmcounter6h);
regh!(0xB87, mhpmcounter7h);
regh!(0xB88, mhpmcounter8h);
regh!(0xB89, mhpmcounter9h);
regh!(0xB8A, mhpmcounter10h);
regh!(0xB8B, mhpmcounter11h);
regh!(0xB8C, mhpmcounter12h);
regh!(0xB8D, mhpmcounter13h);
regh!(0xB8E, mhpmcounter14h);
regh!(0xB8F, mhpmcounter15h);
regh!(0xB90, mhpmcounter16h);
regh!(0xB91, mhpmcounter17h);
regh!(0xB92, mhpmcounter18h);
regh!(0xB93, mhpmcounter19h);
regh!(0xB94, mhpmcounter20h);
regh!(0xB95, mhpmcounter21h);
regh!(0xB96, mhpmcounter22h);
regh!(0xB97, mhpmcounter23h);
regh!(0xB98, mhpmcounter24h);
regh!(0xB99, mhpmcounter25h);
regh!(0xB9A, mhpmcounter26h);
regh!(0xB9B, mhpmcounter27h);
regh!(0xB9C, mhpmcounter28h);
regh!(0xB9D, mhpmcounter29h);
regh!(0xB9E, mhpmcounter30h);
regh!(0xB9F, mhpmcounter31h);
