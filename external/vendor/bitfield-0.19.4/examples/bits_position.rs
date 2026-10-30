use bitfield::bitfield;
use bitfield::BitMut;
use bitfield::BitRangeMut;

bitfield! {
    struct BitsLocations([u8]);
}

bitfield! {
    struct BitsLocationsMsb0(MSB0 [u8]);
}

fn println_slice_bits(slice: &[u8]) {
    if slice.is_empty() {
        println!("[]");
    } else {
        print!("[{:08b}", slice[0]);

        for byte in &slice[1..] {
            print!(", {:08b}", byte);
        }

        println!("]");
    }
}

fn main() {
    let mut bits_locations = BitsLocations([0; 3]);
    let mut bits_locations_msb0 = BitsLocationsMsb0([0; 3]);

    println!("Default version:");
    for i in 0..(3 * 8) {
        bits_locations.set_bit(i, true);
        print!("{:2}: ", i);
        println_slice_bits(&bits_locations.0);
        bits_locations.set_bit(i, false);
    }

    for i in 0..(3 * 8 - 3) {
        let msb = i + 3;
        let lsb = i;
        for value in &[0b1111u8, 0b0001, 0b1000] {
            bits_locations.set_bit_range(msb, lsb, *value);
            print!("{:2} - {:2} ({:04b}): ", msb, lsb, value);
            println_slice_bits(&bits_locations.0);
        }
        println!();
        bits_locations.set_bit_range(msb, lsb, 0u8);
    }

    println!("MSB0 version:");

    for i in 0..(3 * 8) {
        bits_locations_msb0.set_bit(i, true);
        print!("{:2}: ", i);
        println_slice_bits(&bits_locations_msb0.0);

        bits_locations_msb0.set_bit(i, false);
    }

    for i in 0..(3 * 8 - 3) {
        let msb = i + 3;
        let lsb = i;
        for value in &[0b1111u8, 0b0001, 0b1000] {
            bits_locations_msb0.set_bit_range(msb, lsb, *value);
            print!("{:2} - {:2} ({:04b}): ", msb, lsb, value);
            println_slice_bits(&bits_locations_msb0.0);
        }
        println!();

        bits_locations_msb0.set_bit_range(msb, lsb, 0u8);
    }
}
