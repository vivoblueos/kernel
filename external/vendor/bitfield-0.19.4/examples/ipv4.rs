#![allow(dead_code)]

use std::net::Ipv4Addr;

use bitfield::bitfield;

bitfield! {
    struct IpV4Header(MSB0 [u8]);
    impl Debug;
    u32;
    get_version, _: 3, 0;
    get_ihl, _: 7, 4;
    get_dscp, _: 13, 8;
    get_ecn, _: 15, 14;
    get_total_length, _: 31, 16;
    get_identification, _: 47, 32;
    get_df, _: 49;
    get_mf, _: 50;
    get_fragment_offset, _: 63, 51;
    get_time_to_live, _: 71, 64;
    get_protocol, _: 79, 72;
    get_header_checksum, _: 95, 80;
    u8, get_source_address, _: 103, 96, 4;
    u32, into Ipv4Addr, get_destination_address, _: 159, 128;
}

impl<T: AsRef<[u8]>> IpV4Header<T> {
    fn get_source_as_ip_addr(&self) -> Ipv4Addr {
        let mut src = [0; 4];
        for (i, src) in src.iter_mut().enumerate() {
            *src = self.get_source_address(i);
        }
        src.into()
    }
}

fn main() {
    let data = [
        0x45, 0x00, 0x00, 0x40, 0x69, 0x27, 0x40, 0x00, 0x40, 0x11, 0x4d, 0x0d, 0xc0, 0xa8, 0x01,
        0x2a, 0xc0, 0xa8, 0x01, 0xfe,
    ];

    let header = IpV4Header(data);

    assert_eq!(header.get_version(), 4);
    assert_eq!(header.get_total_length(), 64);
    assert_eq!(header.get_identification(), 0x6927);
    assert!(header.get_df());
    assert!(!header.get_mf());
    assert_eq!(header.get_fragment_offset(), 0);
    assert_eq!(header.get_protocol(), 0x11);
    println!(
        "from {} to {}",
        header.get_source_as_ip_addr(),
        header.get_destination_address()
    );

    println!("{:#?}", header);
}
