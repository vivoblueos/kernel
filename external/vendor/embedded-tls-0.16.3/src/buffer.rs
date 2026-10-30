use crate::TlsError;
use aes_gcm::aead::Buffer;
use aes_gcm::Error;

pub struct CryptoBuffer<'b> {
    buf: &'b mut [u8],
    offset: usize,
    len: usize,
}

impl<'b> CryptoBuffer<'b> {
    pub(crate) fn empty() -> Self {
        Self {
            buf: &mut [],
            offset: 0,
            len: 0,
        }
    }

    pub(crate) fn wrap(buf: &'b mut [u8]) -> Self {
        Self {
            buf,
            offset: 0,
            len: 0,
        }
    }

    pub(crate) fn wrap_with_pos(buf: &'b mut [u8], pos: usize) -> Self {
        Self {
            buf,
            offset: 0,
            len: pos,
        }
    }

    pub fn push(&mut self, b: u8) -> Result<(), TlsError> {
        if self.space() > 0 {
            self.buf[self.offset + self.len] = b;
            self.len += 1;
            Ok(())
        } else {
            error!("Failed to push byte");
            Err(TlsError::InsufficientSpace)
        }
    }

    pub fn push_u16(&mut self, num: u16) -> Result<(), TlsError> {
        let data = num.to_be_bytes();
        self.extend_from_slice(&data)
    }

    pub fn push_u24(&mut self, num: u32) -> Result<(), TlsError> {
        let data = num.to_be_bytes();
        self.extend_from_slice(&[data[1], data[2], data[3]])
    }

    pub fn push_u32(&mut self, num: u32) -> Result<(), TlsError> {
        let data = num.to_be_bytes();
        self.extend_from_slice(&data)
    }

    fn set(&mut self, idx: usize, val: u8) -> Result<(), TlsError> {
        if idx < self.len {
            self.buf[self.offset + idx] = val;
            Ok(())
        } else {
            error!(
                "Failed to set byte: index {} is out of range for {} elements",
                idx, self.len
            );
            Err(TlsError::InsufficientSpace)
        }
    }

    fn set_u16(&mut self, idx: usize, val: u16) -> Result<(), TlsError> {
        let [upper, lower] = val.to_be_bytes();
        self.set(idx, upper)?;
        self.set(idx + 1, lower)?;
        Ok(())
    }

    fn set_u24(&mut self, idx: usize, val: u32) -> Result<(), TlsError> {
        let [_, upper, mid, lower] = val.to_be_bytes();
        self.set(idx, upper)?;
        self.set(idx + 1, mid)?;
        self.set(idx + 2, lower)?;
        Ok(())
    }

    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        &mut self.buf[self.offset..self.offset + self.len]
    }

    pub fn as_slice(&self) -> &[u8] {
        &self.buf[self.offset..self.offset + self.len]
    }

    fn extend_internal(&mut self, other: &[u8]) -> Result<(), TlsError> {
        if self.space() < other.len() {
            error!(
                "Failed to extend buffer. Space: {} required: {}",
                self.space(),
                other.len()
            );
            Err(TlsError::InsufficientSpace)
        } else {
            let start = self.offset + self.len;
            self.buf[start..start + other.len()].clone_from_slice(other);
            self.len += other.len();
            Ok(())
        }
    }

    fn space(&self) -> usize {
        self.capacity() - (self.offset + self.len)
    }

    pub fn extend_from_slice(&mut self, other: &[u8]) -> Result<(), TlsError> {
        self.extend_internal(other)
    }

    fn truncate_internal(&mut self, len: usize) {
        if len <= self.capacity() - self.offset {
            self.len = len;
        }
    }

    pub fn truncate(&mut self, len: usize) {
        self.truncate_internal(len)
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn release(self) -> (&'b mut [u8], usize, usize) {
        (self.buf, self.offset, self.len)
    }

    pub fn capacity(&self) -> usize {
        self.buf.len()
    }

    pub fn forward(self) -> CryptoBuffer<'b> {
        let len = self.len;
        self.offset(len)
    }

    pub fn rewind(self) -> CryptoBuffer<'b> {
        self.offset(0)
    }

    pub(crate) fn offset(self, offset: usize) -> CryptoBuffer<'b> {
        let new_len = self.len + self.offset - offset;
        /*info!(
            "offset({}) len({}) -> offset({}), len({})",
            self.offset, self.len, offset, new_len
        );*/
        CryptoBuffer {
            buf: self.buf,
            len: new_len,
            offset,
        }
    }

    pub fn with_u8_length<R>(
        &mut self,
        op: impl FnOnce(&mut Self) -> Result<R, TlsError>,
    ) -> Result<R, TlsError> {
        let len_pos = self.len;
        self.push(0)?;
        let start = self.len;

        let r = op(self)?;

        let len = (self.len() - start) as u8;
        self.set(len_pos, len)?;

        Ok(r)
    }

    pub fn with_u16_length<R>(
        &mut self,
        op: impl FnOnce(&mut Self) -> Result<R, TlsError>,
    ) -> Result<R, TlsError> {
        let len_pos = self.len;
        self.push_u16(0)?;
        let start = self.len;

        let r = op(self)?;

        let len = (self.len() - start) as u16;
        self.set_u16(len_pos, len)?;

        Ok(r)
    }

    pub fn with_u24_length<R>(
        &mut self,
        op: impl FnOnce(&mut Self) -> Result<R, TlsError>,
    ) -> Result<R, TlsError> {
        let len_pos = self.len;
        self.push_u24(0)?;
        let start = self.len;

        let r = op(self)?;

        let len = (self.len() - start) as u32;
        self.set_u24(len_pos, len)?;

        Ok(r)
    }
}

impl<'b> AsRef<[u8]> for CryptoBuffer<'b> {
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl<'b> AsMut<[u8]> for CryptoBuffer<'b> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_mut_slice()
    }
}

impl<'b> Buffer for CryptoBuffer<'b> {
    fn extend_from_slice(&mut self, other: &[u8]) -> Result<(), Error> {
        self.extend_internal(other).map_err(|_| Error)
    }

    fn truncate(&mut self, len: usize) {
        self.truncate_internal(len)
    }
}

#[cfg(test)]
mod test {
    use super::CryptoBuffer;

    #[test]
    fn encode() {
        let mut buf1 = [0; 4];
        let mut c = CryptoBuffer::wrap(&mut buf1);
        c.push_u24(1027).unwrap();

        let mut buf2 = [0; 4];
        let mut c = CryptoBuffer::wrap(&mut buf2);
        c.push_u24(0).unwrap();
        c.set_u24(0, 1027).unwrap();

        assert_eq!(buf1, buf2);

        let decoded = u32::from_be_bytes([0, buf1[0], buf1[1], buf1[2]]);
        assert_eq!(1027, decoded);
    }

    #[test]
    fn offset_calc() {
        let mut buf = [0; 8];
        let mut c = CryptoBuffer::wrap(&mut buf);
        c.push(1).unwrap();
        c.push(2).unwrap();
        c.push(3).unwrap();

        assert_eq!(&[1, 2, 3], c.as_slice());

        let l = c.len();
        let mut c = c.offset(l);

        c.push(4).unwrap();
        c.push(5).unwrap();
        c.push(6).unwrap();

        assert_eq!(&[4, 5, 6], c.as_slice());

        let mut c = c.offset(0);

        c.push(7).unwrap();
        c.push(8).unwrap();

        assert_eq!(&[1, 2, 3, 4, 5, 6, 7, 8], c.as_slice());

        let mut c = c.offset(6);
        c.set(0, 14).unwrap();
        c.set(1, 15).unwrap();

        let c = c.offset(0);
        assert_eq!(&[1, 2, 3, 4, 5, 6, 14, 15], c.as_slice());

        let mut c = c.offset(4);
        c.truncate(0);
        c.extend_from_slice(&[10, 11, 12, 13]).unwrap();
        assert_eq!(&[10, 11, 12, 13], c.as_slice());

        let c = c.offset(0);
        assert_eq!(&[1, 2, 3, 4, 10, 11, 12, 13], c.as_slice());
    }
}
