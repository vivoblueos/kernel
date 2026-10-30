use std::io;

use bytes::{BufMut, BytesMut};
use tokio_util::codec::{Decoder, Encoder};

pub struct MyCodec {}

impl MyCodec {
    pub fn new() -> Self {
        MyCodec {}
    }
}

impl Decoder for MyCodec {
    type Item = BytesMut;
    type Error = io::Error;

    fn decode(&mut self, buf: &mut BytesMut) -> Result<Option<BytesMut>, io::Error> {
        if !buf.is_empty() {
            let len = buf.len();
            Ok(Some(buf.split_to(len)))
        } else {
            Ok(None)
        }
    }
}

impl Encoder<&[u8]> for MyCodec {
    type Error = io::Error;

    fn encode(&mut self, data: &[u8], buf: &mut BytesMut) -> Result<(), io::Error> {
        buf.reserve(data.len());
        buf.put(data);
        Ok(())
    }
}
