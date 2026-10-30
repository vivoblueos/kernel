use core::{fmt::Debug, ops::Deref, str::Utf8Error};

use futures::{Sink, SinkExt, Stream, StreamExt};
use rand_core::RngCore;

use crate::{
    WebSocket, WebSocketCloseStatusCode, WebSocketContext, WebSocketOptions,
    WebSocketReceiveMessageType, WebSocketSendMessageType, WebSocketSubProtocol, WebSocketType,
};

pub struct CloseMessage<'a> {
    pub status_code: WebSocketCloseStatusCode,
    pub reason: &'a [u8],
}

pub enum ReadResult<'a> {
    Binary(&'a [u8]),
    Text(&'a str),
    /// We received a pong message in response to a ping message we sent earlier.
    /// This should contain the same data as was sent in the ping message
    Pong(&'a [u8]),
    /// We received a ping message from the other end
    /// A pong message with the same content will automatically be sent back as per the websocket spec
    /// However, this message is exposed to you so that you can see what is in the ping message
    Ping(&'a [u8]),
    /// The other end initiated a close handshake. The contents of this message is usually the reason for the close
    /// A close response message will automatically be sent back to the other end to complete the close handshake
    /// However, this message is exposed to you so that you can see why
    Close(CloseMessage<'a>),
}

#[derive(Debug)]
pub enum FramerError<E> {
    Io(E),
    FrameTooLarge(usize),
    Utf8(Utf8Error),
    HttpHeader(httparse::Error),
    WebSocket(crate::Error),
    Disconnected,
    RxBufferTooSmall(usize),
}

pub struct Framer<TRng, TWebSocketType>
where
    TRng: RngCore,
    TWebSocketType: WebSocketType,
{
    websocket: WebSocket<TRng, TWebSocketType>,
    frame_cursor: usize,
    rx_remainder_len: usize,
}

impl<TRng> Framer<TRng, crate::Server>
where
    TRng: RngCore,
{
    pub async fn accept<'a, B, E>(
        &mut self,
        stream: &mut (impl Stream<Item = Result<B, E>> + Sink<&'a [u8], Error = E> + Unpin),
        buffer: &'a mut [u8],
        websocket_context: &WebSocketContext,
    ) -> Result<(), FramerError<E>> {
        let len = self
            .websocket
            .server_accept(&websocket_context.sec_websocket_key, None, buffer)
            .map_err(FramerError::WebSocket)?;

        stream.send(&buffer[..len]).await.map_err(FramerError::Io)?;
        Ok(())
    }
}

impl<TRng> Framer<TRng, crate::Client>
where
    TRng: RngCore,
{
    pub async fn connect<'a, B, E>(
        &mut self,
        stream: &mut (impl Stream<Item = Result<B, E>> + Sink<&'a [u8], Error = E> + Unpin),
        buffer: &'a mut [u8],
        websocket_options: &WebSocketOptions<'_>,
    ) -> Result<Option<WebSocketSubProtocol>, FramerError<E>>
    where
        B: AsRef<[u8]>,
    {
        let (tx_len, web_socket_key) = self
            .websocket
            .client_connect(websocket_options, buffer)
            .map_err(FramerError::WebSocket)?;

        let (tx_buf, rx_buf) = buffer.split_at_mut(tx_len);
        stream.send(tx_buf).await.map_err(FramerError::Io)?;
        stream.flush().await.map_err(FramerError::Io)?;

        match stream.next().await {
            Some(buf) => {
                let buf = buf.map_err(FramerError::Io)?;
                let buf = buf.as_ref();

                match self.websocket.client_accept(&web_socket_key, buf) {
                    Ok((len, sub_protocol)) => {
                        // "consume" the HTTP header that we have read from the stream
                        // read_cursor would be 0 if we exactly read the HTTP header from the stream and nothing else

                        // copy the remaining bytes to the end of the rx_buf (which is also the end of the buffer) because they are the contents of the next websocket frame(s)
                        let from = len;
                        let to = buf.len();
                        let remaining_len = to - from;

                        if remaining_len > 0 {
                            let rx_start = rx_buf.len() - remaining_len;
                            rx_buf[rx_start..].copy_from_slice(&buf[from..to]);
                            self.rx_remainder_len = remaining_len;
                        }

                        Ok(sub_protocol)
                    }
                    Err(crate::Error::HttpHeaderIncomplete) => {
                        // TODO: continue reading HTTP header in loop
                        panic!("http header not complete");
                    }
                    Err(e) => Err(FramerError::WebSocket(e)),
                }
            }
            None => Err(FramerError::Disconnected),
        }
    }
}

impl<TRng, TWebSocketType> Framer<TRng, TWebSocketType>
where
    TRng: RngCore,
    TWebSocketType: WebSocketType,
{
    pub fn new(websocket: WebSocket<TRng, TWebSocketType>) -> Self {
        Self {
            websocket,
            frame_cursor: 0,
            rx_remainder_len: 0,
        }
    }

    pub fn encode<E>(
        &mut self,
        message_type: WebSocketSendMessageType,
        end_of_message: bool,
        from: &[u8],
        to: &mut [u8],
    ) -> Result<usize, FramerError<E>> {
        let len = self
            .websocket
            .write(message_type, end_of_message, from, to)
            .map_err(FramerError::WebSocket)?;

        Ok(len)
    }

    pub async fn write<'b, E>(
        &mut self,
        tx: &mut (impl Sink<&'b [u8], Error = E> + Unpin),
        tx_buf: &'b mut [u8],
        message_type: WebSocketSendMessageType,
        end_of_message: bool,
        frame_buf: &[u8],
    ) -> Result<(), FramerError<E>>
    where
        E: Debug,
    {
        let len = self
            .websocket
            .write(message_type, end_of_message, frame_buf, tx_buf)
            .map_err(FramerError::WebSocket)?;

        tx.send(&tx_buf[..len]).await.map_err(FramerError::Io)?;
        tx.flush().await.map_err(FramerError::Io)?;
        Ok(())
    }

    pub async fn close<'b, E>(
        &mut self,
        tx: &mut (impl Sink<&'b [u8], Error = E> + Unpin),
        tx_buf: &'b mut [u8],
        close_status: WebSocketCloseStatusCode,
        status_description: Option<&str>,
    ) -> Result<(), FramerError<E>>
    where
        E: Debug,
    {
        let len = self
            .websocket
            .close(close_status, status_description, tx_buf)
            .map_err(FramerError::WebSocket)?;

        tx.send(&tx_buf[..len]).await.map_err(FramerError::Io)?;
        tx.flush().await.map_err(FramerError::Io)?;
        Ok(())
    }

    // NOTE: any unused bytes read from the stream but not decoded are stored at the end
    // of the buffer to be used next time this read function is called. This also applies to
    // any unused bytes read when the connect handshake was made. Therefore it is important that
    // the caller does not clear this buffer between calls or use it for anthing other than reads.
    pub async fn read<'a, B: Deref<Target = [u8]>, E>(
        &mut self,
        stream: &mut (impl Stream<Item = Result<B, E>> + Sink<&'a [u8], Error = E> + Unpin),
        buffer: &'a mut [u8],
    ) -> Option<Result<ReadResult<'a>, FramerError<E>>>
    where
        E: Debug,
    {
        if self.rx_remainder_len == 0 {
            match stream.next().await {
                Some(Ok(input)) => {
                    if buffer.len() < input.len() {
                        return Some(Err(FramerError::RxBufferTooSmall(input.len())));
                    }

                    let rx_start = buffer.len() - input.len();

                    // copy to end of buffer
                    buffer[rx_start..].copy_from_slice(&input);
                    self.rx_remainder_len = input.len()
                }
                Some(Err(e)) => {
                    return Some(Err(FramerError::Io(e)));
                }
                None => return None,
            }
        }

        let rx_start = buffer.len() - self.rx_remainder_len;
        let (frame_buf, rx_buf) = buffer.split_at_mut(rx_start);

        let ws_result = match self.websocket.read(rx_buf, frame_buf) {
            Ok(ws_result) => ws_result,
            Err(e) => return Some(Err(FramerError::WebSocket(e))),
        };

        self.rx_remainder_len -= ws_result.len_from;

        match ws_result.message_type {
            WebSocketReceiveMessageType::Binary => {
                self.frame_cursor += ws_result.len_to;
                if ws_result.end_of_message {
                    let range = 0..self.frame_cursor;
                    self.frame_cursor = 0;
                    return Some(Ok(ReadResult::Binary(&frame_buf[range])));
                }
            }
            WebSocketReceiveMessageType::Text => {
                self.frame_cursor += ws_result.len_to;
                if ws_result.end_of_message {
                    let range = 0..self.frame_cursor;
                    self.frame_cursor = 0;
                    match core::str::from_utf8(&frame_buf[range]) {
                        Ok(text) => return Some(Ok(ReadResult::Text(text))),
                        Err(e) => return Some(Err(FramerError::Utf8(e))),
                    }
                }
            }
            WebSocketReceiveMessageType::CloseMustReply => {
                let range = self.frame_cursor..self.frame_cursor + ws_result.len_to;

                // create a tx_buf from the end of the frame_buf
                let tx_buf_len = ws_result.len_to + 14; // for extra websocket header
                let split_at = frame_buf.len() - tx_buf_len;
                let (frame_buf, tx_buf) = frame_buf.split_at_mut(split_at);

                match self.websocket.write(
                    WebSocketSendMessageType::CloseReply,
                    true,
                    &frame_buf[range.start..range.end],
                    tx_buf,
                ) {
                    Ok(len) => match stream.send(&tx_buf[..len]).await {
                        Ok(()) => {
                            self.frame_cursor = 0;
                            let status_code = ws_result
                                .close_status
                                .expect("close message must have code");
                            let reason = &frame_buf[range];
                            return Some(Ok(ReadResult::Close(CloseMessage {
                                status_code,
                                reason,
                            })));
                        }
                        Err(e) => return Some(Err(FramerError::Io(e))),
                    },
                    Err(e) => return Some(Err(FramerError::WebSocket(e))),
                }
            }
            WebSocketReceiveMessageType::CloseCompleted => return None,
            WebSocketReceiveMessageType::Pong => {
                let range = self.frame_cursor..self.frame_cursor + ws_result.len_to;
                return Some(Ok(ReadResult::Pong(&frame_buf[range])));
            }
            WebSocketReceiveMessageType::Ping => {
                let range = self.frame_cursor..self.frame_cursor + ws_result.len_to;

                // create a tx_buf from the end of the frame_buf
                let tx_buf_len = ws_result.len_to + 14; // for extra websocket header
                let split_at = frame_buf.len() - tx_buf_len;
                let (frame_buf, tx_buf) = frame_buf.split_at_mut(split_at);

                match self.websocket.write(
                    WebSocketSendMessageType::Pong,
                    true,
                    &frame_buf[range.start..range.end],
                    tx_buf,
                ) {
                    Ok(len) => match stream.send(&tx_buf[..len]).await {
                        Ok(()) => {
                            return Some(Ok(ReadResult::Ping(&frame_buf[range])));
                        }
                        Err(e) => return Some(Err(FramerError::Io(e))),
                    },
                    Err(e) => return Some(Err(FramerError::WebSocket(e))),
                }
            }
        }

        None
    }
}
