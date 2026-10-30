macro_rules! reg {
    (
        $addr:expr, $csrl:ident, $csrh:ident
    ) => {
        /// Performance-monitoring counter
        pub mod $csrl {
            read_csr_as_usize!($addr);
            read_composite_csr!(super::$csrh::read(), read());
        }
    };
}

macro_rules! regh {
    (
        $addr:expr, $csrh:ident
    ) => {
        /// Upper 32 bits of performance-monitoring counter (RV32I only)
        pub mod $csrh {
            read_csr_as_usize_rv32!($addr);
        }
    };
}

reg!(0xC03, hpmcounter3, hpmcounter3h);
reg!(0xC04, hpmcounter4, hpmcounter4h);
reg!(0xC05, hpmcounter5, hpmcounter5h);
reg!(0xC06, hpmcounter6, hpmcounter6h);
reg!(0xC07, hpmcounter7, hpmcounter7h);
reg!(0xC08, hpmcounter8, hpmcounter8h);
reg!(0xC09, hpmcounter9, hpmcounter9h);
reg!(0xC0A, hpmcounter10, hpmcounter10h);
reg!(0xC0B, hpmcounter11, hpmcounter11h);
reg!(0xC0C, hpmcounter12, hpmcounter12h);
reg!(0xC0D, hpmcounter13, hpmcounter13h);
reg!(0xC0E, hpmcounter14, hpmcounter14h);
reg!(0xC0F, hpmcounter15, hpmcounter15h);
reg!(0xC10, hpmcounter16, hpmcounter16h);
reg!(0xC11, hpmcounter17, hpmcounter17h);
reg!(0xC12, hpmcounter18, hpmcounter18h);
reg!(0xC13, hpmcounter19, hpmcounter19h);
reg!(0xC14, hpmcounter20, hpmcounter20h);
reg!(0xC15, hpmcounter21, hpmcounter21h);
reg!(0xC16, hpmcounter22, hpmcounter22h);
reg!(0xC17, hpmcounter23, hpmcounter23h);
reg!(0xC18, hpmcounter24, hpmcounter24h);
reg!(0xC19, hpmcounter25, hpmcounter25h);
reg!(0xC1A, hpmcounter26, hpmcounter26h);
reg!(0xC1B, hpmcounter27, hpmcounter27h);
reg!(0xC1C, hpmcounter28, hpmcounter28h);
reg!(0xC1D, hpmcounter29, hpmcounter29h);
reg!(0xC1E, hpmcounter30, hpmcounter30h);
reg!(0xC1F, hpmcounter31, hpmcounter31h);

regh!(0xC83, hpmcounter3h);
regh!(0xC84, hpmcounter4h);
regh!(0xC85, hpmcounter5h);
regh!(0xC86, hpmcounter6h);
regh!(0xC87, hpmcounter7h);
regh!(0xC88, hpmcounter8h);
regh!(0xC89, hpmcounter9h);
regh!(0xC8A, hpmcounter10h);
regh!(0xC8B, hpmcounter11h);
regh!(0xC8C, hpmcounter12h);
regh!(0xC8D, hpmcounter13h);
regh!(0xC8E, hpmcounter14h);
regh!(0xC8F, hpmcounter15h);
regh!(0xC90, hpmcounter16h);
regh!(0xC91, hpmcounter17h);
regh!(0xC92, hpmcounter18h);
regh!(0xC93, hpmcounter19h);
regh!(0xC94, hpmcounter20h);
regh!(0xC95, hpmcounter21h);
regh!(0xC96, hpmcounter22h);
regh!(0xC97, hpmcounter23h);
regh!(0xC98, hpmcounter24h);
regh!(0xC99, hpmcounter25h);
regh!(0xC9A, hpmcounter26h);
regh!(0xC9B, hpmcounter27h);
regh!(0xC9C, hpmcounter28h);
regh!(0xC9D, hpmcounter29h);
regh!(0xC9E, hpmcounter30h);
regh!(0xC9F, hpmcounter31h);
