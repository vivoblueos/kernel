use crate::buffer::*;
use crate::TlsError;
use core::fmt::{Debug, Formatter};
//use digest::generic_array::{ArrayLength, GenericArray};
use generic_array::{ArrayLength, GenericArray};
// use heapless::Vec;

pub struct PskBinder<N: ArrayLength<u8>> {
    pub verify: GenericArray<u8, N>,
}

#[cfg(feature = "defmt")]
impl<N: ArrayLength<u8>> defmt::Format for PskBinder<N> {
    fn format(&self, f: defmt::Formatter<'_>) {
        defmt::write!(f, "verify length:{}", &self.verify.len());
    }
}

impl<N: ArrayLength<u8>> Debug for PskBinder<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PskBinder").finish()
    }
}

impl<N: ArrayLength<u8>> PskBinder<N> {
    pub(crate) fn encode(&self, buf: &mut CryptoBuffer<'_>) -> Result<(), TlsError> {
        let len = self.verify.len() as u8;
        //buf.extend_from_slice(&[len[1], len[2], len[3]]);
        buf.push(len).map_err(|_| TlsError::EncodeError)?;
        buf.extend_from_slice(&self.verify[..self.verify.len()])
            .map_err(|_| TlsError::EncodeError)?;
        Ok(())
    }

    pub fn len() -> usize {
        N::to_usize()
    }
}
