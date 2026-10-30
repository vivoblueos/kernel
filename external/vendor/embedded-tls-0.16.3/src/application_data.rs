use crate::buffer::*;
use crate::record::RecordHeader;
use core::fmt::{Debug, Formatter};

pub struct ApplicationData<'a> {
    pub(crate) header: RecordHeader,
    pub(crate) data: CryptoBuffer<'a>,
}

impl<'a> Debug for ApplicationData<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "ApplicationData {:x?}", self.data.len())
    }
}

#[cfg(feature = "defmt")]
impl<'a> defmt::Format for ApplicationData<'a> {
    fn format(&self, f: defmt::Formatter<'_>) {
        defmt::write!(f, "ApplicationData {}", self.data.len());
    }
}

impl<'a> ApplicationData<'a> {
    pub fn new(rx_buf: CryptoBuffer<'a>, header: RecordHeader) -> ApplicationData<'a> {
        Self {
            header,
            data: rx_buf,
        }
    }
}
