const BASIS: u32 = 0x811c9dc5;
const PRIME: u32 = 0x1000193;

/// 32-bit Fowler-Noll-Vo hasher
pub struct Hasher {
    state: u32,
}

impl Default for Hasher {
    fn default() -> Self {
        Hasher { state: BASIS }
    }
}

impl ::Hasher for Hasher {
    #[inline]
    fn finish(&self) -> u32 {
        self.state
    }

    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.state ^= u32::from(*byte);
            self.state = self.state.wrapping_mul(PRIME);
        }
    }
}
