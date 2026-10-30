use core::ops::Range;

use crate::{
    alert::AlertDescription, common::decrypted_buffer_info::DecryptedBufferInfo,
    config::TlsCipherSuite, handshake::ServerHandshake, record::ServerRecord, TlsError,
};

pub struct DecryptedReadHandler<'a> {
    pub source_buffer: Range<*const u8>,
    pub buffer_info: &'a mut DecryptedBufferInfo,
    pub is_open: &'a mut bool,
}

impl DecryptedReadHandler<'_> {
    pub fn handle<CipherSuite: TlsCipherSuite>(
        &mut self,
        record: ServerRecord<'_, CipherSuite>,
    ) -> Result<(), TlsError> {
        match record {
            ServerRecord::ApplicationData(data) => {
                let slice = data.data.as_slice();
                let slice_ptrs = slice.as_ptr_range();

                debug_assert!(
                    self.source_buffer.contains(&slice_ptrs.start)
                        && self.source_buffer.contains(&slice_ptrs.end)
                );

                let offset = unsafe {
                    // SAFETY: The assertion above ensures `slice` is a subslice of the read buffer.
                    // This, in turn, ensures we don't violate safety constraints of `offset_from`.

                    // TODO: We are only assuming here that the pointers are derived from the read
                    // buffer. While this is reasonable, and we don't do any pointer magic,
                    // it's not an invariant.
                    slice_ptrs.start.offset_from(self.source_buffer.start) as usize
                };

                self.buffer_info.offset = offset;
                self.buffer_info.len = slice.len();
                self.buffer_info.consumed = 0;
                Ok(())
            }
            ServerRecord::Alert(alert) => {
                if let AlertDescription::CloseNotify = alert.description {
                    *self.is_open = false;
                    Err(TlsError::ConnectionClosed)
                } else {
                    Err(TlsError::InternalError)
                }
            }
            ServerRecord::ChangeCipherSpec(_) => Err(TlsError::InternalError),
            ServerRecord::Handshake(ServerHandshake::NewSessionTicket(_)) => {
                // TODO: we should validate extensions and abort. We can do this automatically
                // as long as the connection is unsplit, however, split connections must be aborted
                // by the user.
                Ok(())
            }
            _ => {
                unimplemented!()
            }
        }
    }
}
