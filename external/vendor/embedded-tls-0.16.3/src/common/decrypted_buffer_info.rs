use crate::read_buffer::ReadBuffer;

#[derive(Default)]
pub struct DecryptedBufferInfo {
    pub offset: usize,
    pub len: usize,
    pub consumed: usize,
}

impl DecryptedBufferInfo {
    pub fn create_read_buffer<'b>(&'b mut self, buffer: &'b [u8]) -> ReadBuffer<'b> {
        let offset = self.offset + self.consumed;
        let end = self.offset + self.len;
        ReadBuffer::new(&buffer[offset..end], &mut self.consumed)
    }

    pub fn len(&self) -> usize {
        self.len - self.consumed
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
