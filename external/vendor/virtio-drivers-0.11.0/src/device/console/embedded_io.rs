//! Implementation of `embedded-io` traits for `VirtIOConsole`.

use super::VirtIOConsole;
use crate::{transport::Transport, Error, Hal};
use core::cmp::min;
use embedded_io::{BufRead, ErrorType, Read, ReadReady, Write};

impl<H: Hal, T: Transport> ErrorType for VirtIOConsole<H, T> {
    type Error = Error;
}

impl<H: Hal, T: Transport> Write for VirtIOConsole<H, T> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        if buf.is_empty() {
            Ok(0)
        } else {
            self.send_bytes(buf)?;
            Ok(buf.len())
        }
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        // We don't buffer writes, so nothing to do here.
        Ok(())
    }
}

impl<H: Hal, T: Transport> ReadReady for VirtIOConsole<H, T> {
    fn read_ready(&mut self) -> Result<bool, Self::Error> {
        self.finish_receive()?;
        Ok(self.cursor != self.pending_len)
    }
}

impl<H: Hal, T: Transport> Read for VirtIOConsole<H, T> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        if buf.is_empty() {
            Ok(0)
        } else {
            self.wait_for_receive()?;
            let read_length = min(buf.len(), self.pending_len - self.cursor);
            buf[..read_length]
                .copy_from_slice(&self.queue_buf_rx[self.cursor..self.cursor + read_length]);
            Ok(read_length)
        }
    }
}

impl<H: Hal, T: Transport> BufRead for VirtIOConsole<H, T> {
    fn fill_buf(&mut self) -> Result<&[u8], Self::Error> {
        self.wait_for_receive()?;
        Ok(&self.queue_buf_rx[self.cursor..self.pending_len])
    }

    fn consume(&mut self, amt: usize) {
        assert!(self.cursor + amt <= self.pending_len);
        self.cursor += amt;
    }
}
