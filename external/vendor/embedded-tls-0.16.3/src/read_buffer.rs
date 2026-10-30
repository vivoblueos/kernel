/// A reference to consume bytes from the internal buffer.
#[must_use]
pub struct ReadBuffer<'a> {
    data: &'a [u8],
    consumed: usize,
    used: bool,

    decrypted_consumed: &'a mut usize,
}

impl<'a> ReadBuffer<'a> {
    #[inline]
    pub(crate) fn new(buffer: &'a [u8], decrypted_consumed: &'a mut usize) -> Self {
        Self {
            data: buffer,
            consumed: 0,
            used: false,
            decrypted_consumed,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.data.len() - self.consumed
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Consumes and returns a slice of at most `count` bytes.
    #[inline]
    pub fn peek(&mut self, count: usize) -> &'a [u8] {
        let count = self.len().min(count);
        let start = self.consumed;

        // We mark the buffer used to prevent dropping unconsumed bytes.
        self.used = true;

        &self.data[start..start + count]
    }

    /// Consumes and returns a slice of at most `count` bytes.
    #[inline]
    pub fn peek_all(&mut self) -> &'a [u8] {
        self.peek(self.len())
    }

    /// Consumes and returns a slice of at most `count` bytes.
    #[inline]
    pub fn pop(&mut self, count: usize) -> &'a [u8] {
        let count = self.len().min(count);
        let start = self.consumed;
        self.consumed += count;
        self.used = true;

        &self.data[start..start + count]
    }

    /// Consumes and returns the internal buffer.
    #[inline]
    pub fn pop_all(&mut self) -> &'a [u8] {
        self.pop(self.len())
    }

    /// Drops the reference and restores internal buffer.
    #[inline]
    pub fn revert(self) {
        core::mem::forget(self);
    }

    /// Tries to fills the buffer by consuming and copying bytes into it.
    #[inline]
    pub fn pop_into(&mut self, buf: &mut [u8]) -> usize {
        let to_copy = self.pop(buf.len());

        buf[..to_copy.len()].copy_from_slice(to_copy);

        to_copy.len()
    }
}

impl Drop for ReadBuffer<'_> {
    #[inline]
    fn drop(&mut self) {
        *self.decrypted_consumed += if self.used {
            self.consumed
        } else {
            // Consume all if dropped unused
            self.data.len()
        };
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn dropping_unused_buffer_consumes_all() {
        let mut consumed = 1000;
        let buffer = [0, 1, 2, 3];

        _ = ReadBuffer::new(&buffer, &mut consumed);

        assert_eq!(consumed, 1004);
    }

    #[test]
    fn pop_moves_internal_cursor() {
        let mut consumed = 0;

        let mut buffer = ReadBuffer::new(&[0, 1, 2, 3], &mut consumed);

        assert_eq!(buffer.pop(1), &[0]);
        assert_eq!(buffer.pop(1), &[1]);
        assert_eq!(buffer.pop(1), &[2]);
    }

    #[test]
    fn dropping_consumes_as_many_bytes_as_used() {
        let mut consumed = 0;

        let mut buffer = ReadBuffer::new(&[0, 1, 2, 3], &mut consumed);

        assert_eq!(buffer.pop(1), &[0]);
        assert_eq!(buffer.pop(1), &[1]);
        assert_eq!(buffer.pop(1), &[2]);

        core::mem::drop(buffer);

        assert_eq!(consumed, 3);
    }

    #[test]
    fn pop_returns_fewer_bytes_if_requested_more_than_what_it_has() {
        let mut consumed = 0;

        let mut buffer = ReadBuffer::new(&[0, 1, 2, 3], &mut consumed);

        assert_eq!(buffer.pop(1), &[0]);
        assert_eq!(buffer.pop(1), &[1]);
        assert_eq!(buffer.pop(4), &[2, 3]);
        assert_eq!(buffer.pop(1), &[]);

        core::mem::drop(buffer);

        assert_eq!(consumed, 4);
    }

    #[test]
    fn peek_does_not_consume() {
        let mut consumed = 0;

        let mut buffer = ReadBuffer::new(&[0, 1, 2, 3], &mut consumed);

        assert_eq!(buffer.peek(1), &[0]);
        assert_eq!(buffer.peek(1), &[0]);

        core::mem::drop(buffer);

        assert_eq!(consumed, 0);
    }

    #[test]
    fn revert_undoes_pop() {
        let mut consumed = 0;

        let mut buffer = ReadBuffer::new(&[0, 1, 2, 3], &mut consumed);

        assert_eq!(buffer.pop(4), &[0, 1, 2, 3]);

        buffer.revert();

        assert_eq!(consumed, 0);
    }
}
