use rand_core::RngCore;

// Clients need a proper random number generator to generate a mask key
// However, server websockets do not require this and the payload is not masked
// EmptyRng is used for servers. In theory, you can use it for clients but you may run into
// proxy server caching issues so it is advisable to use a proper random number generator.
// Note that data masking does not require a cryptographically strong random number because
// the key is sent with the payload anyway

#[derive(Default)]
pub struct EmptyRng {}

impl EmptyRng {
    pub fn new() -> EmptyRng {
        EmptyRng {}
    }
}

impl RngCore for EmptyRng {
    fn next_u32(&mut self) -> u32 {
        0
    }
    fn next_u64(&mut self) -> u64 {
        0
    }
    fn fill_bytes(&mut self, _dest: &mut [u8]) {}
    fn try_fill_bytes(&mut self, _dest: &mut [u8]) -> core::result::Result<(), rand_core::Error> {
        Ok(())
    }
}
