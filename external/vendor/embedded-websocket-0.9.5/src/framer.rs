// This module helps you work with the websocket library using a stream of data rather than using it as a raw codec.
// This is the most common use case when working with websockets and is recommended due to the hand shaky nature of
// the protocol as well as the fact that an input buffer can contain multiple websocket frames or maybe only a fragment of one.
// This module allows you to work with discrete websocket frames rather than the multiple fragments you read off a stream.
// NOTE: if you are using the standard library then you can use the built in Read and Write traits from std otherwise
//       you have to implement the Read and Write traits specified below

use crate::{
    WebSocket, WebSocketCloseStatusCode, WebSocketContext, WebSocketOptions,
    WebSocketReceiveMessageType, WebSocketSendMessageType, WebSocketState, WebSocketSubProtocol,
    WebSocketType,
};
use core::{cmp::min, str::Utf8Error};
use rand_core::RngCore;

// automagically implement the Stream trait for TcpStream if we are using the standard library
// if you were using no_std you would have to implement your own stream
#[cfg(feature = "std")]
impl Stream<std::io::Error> for std::net::TcpStream {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, std::io::Error> {
        std::io::Read::read(self, buf)
    }

    fn write_all(&mut self, buf: &[u8]) -> Result<(), std::io::Error> {
        std::io::Write::write_all(self, buf)
    }
}

pub trait Stream<E> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, E>;
    fn write_all(&mut self, buf: &[u8]) -> Result<(), E>;
}

pub enum ReadResult<'a> {
    Binary(&'a [u8]),
    Text(&'a str),
    Pong(&'a [u8]),
    Closed,
}

#[derive(Debug)]
pub enum FramerError<E> {
    Io(E),
    FrameTooLarge(usize),
    Utf8(Utf8Error),
    HttpHeader(httparse::Error),
    WebSocket(crate::Error),
}

pub struct Framer<'a, TRng, TWebSocketType>
where
    TRng: RngCore,
    TWebSocketType: WebSocketType,
{
    read_buf: &'a mut [u8],
    write_buf: &'a mut [u8],
    read_cursor: &'a mut usize,
    frame_cursor: usize,
    read_len: usize,
    websocket: &'a mut WebSocket<TRng, TWebSocketType>,
}

impl<'a, TRng> Framer<'a, TRng, crate::Client>
where
    TRng: RngCore,
{
    pub fn connect<E>(
        &mut self,
        stream: &mut impl Stream<E>,
        websocket_options: &WebSocketOptions,
    ) -> Result<Option<WebSocketSubProtocol>, FramerError<E>> {
        let (len, web_socket_key) = self
            .websocket
            .client_connect(websocket_options, self.write_buf)
            .map_err(FramerError::WebSocket)?;
        stream
            .write_all(&self.write_buf[..len])
            .map_err(FramerError::Io)?;
        *self.read_cursor = 0;

        loop {
            // read the response from the server and check it to complete the opening handshake
            let received_size = stream
                .read(&mut self.read_buf[*self.read_cursor..])
                .map_err(FramerError::Io)?;

            match self.websocket.client_accept(
                &web_socket_key,
                &self.read_buf[..*self.read_cursor + received_size],
            ) {
                Ok((len, sub_protocol)) => {
                    // "consume" the HTTP header that we have read from the stream
                    // read_cursor would be 0 if we exactly read the HTTP header from the stream and nothing else
                    *self.read_cursor += received_size - len;
                    return Ok(sub_protocol);
                }
                Err(crate::Error::HttpHeaderIncomplete) => {
                    *self.read_cursor += received_size;
                    // continue reading HTTP header in loop
                }
                Err(e) => {
                    *self.read_cursor += received_size;
                    return Err(FramerError::WebSocket(e));
                }
            }
        }
    }
}

impl<'a, TRng> Framer<'a, TRng, crate::Server>
where
    TRng: RngCore,
{
    pub fn accept<E>(
        &mut self,
        stream: &mut impl Stream<E>,
        websocket_context: &WebSocketContext,
    ) -> Result<(), FramerError<E>> {
        let len = self
            .websocket
            .server_accept(&websocket_context.sec_websocket_key, None, self.write_buf)
            .map_err(FramerError::WebSocket)?;

        stream
            .write_all(&self.write_buf[..len])
            .map_err(FramerError::Io)?;
        Ok(())
    }
}

impl<'a, TRng, TWebSocketType> Framer<'a, TRng, TWebSocketType>
where
    TRng: RngCore,
    TWebSocketType: WebSocketType,
{
    // read and write buffers are usually quite small (4KB) and can be smaller
    // than the frame buffer but use whatever is is appropriate for your stream
    pub fn new(
        read_buf: &'a mut [u8],
        read_cursor: &'a mut usize,
        write_buf: &'a mut [u8],
        websocket: &'a mut WebSocket<TRng, TWebSocketType>,
    ) -> Self {
        Self {
            read_buf,
            write_buf,
            read_cursor,
            frame_cursor: 0,
            read_len: 0,
            websocket,
        }
    }

    pub fn state(&self) -> WebSocketState {
        self.websocket.state
    }

    // calling close on a websocket that has already been closed by the other party has no effect
    pub fn close<E>(
        &mut self,
        stream: &mut impl Stream<E>,
        close_status: WebSocketCloseStatusCode,
        status_description: Option<&str>,
    ) -> Result<(), FramerError<E>> {
        let len = self
            .websocket
            .close(close_status, status_description, self.write_buf)
            .map_err(FramerError::WebSocket)?;
        stream
            .write_all(&self.write_buf[..len])
            .map_err(FramerError::Io)?;
        Ok(())
    }

    pub fn write<E>(
        &mut self,
        stream: &mut impl Stream<E>,
        message_type: WebSocketSendMessageType,
        end_of_message: bool,
        frame_buf: &[u8],
    ) -> Result<(), FramerError<E>> {
        let len = self
            .websocket
            .write(message_type, end_of_message, frame_buf, self.write_buf)
            .map_err(FramerError::WebSocket)?;
        stream
            .write_all(&self.write_buf[..len])
            .map_err(FramerError::Io)?;
        Ok(())
    }

    // frame_buf should be large enough to hold an entire websocket text frame
    // this function will block until it has recieved a full websocket frame.
    // It will wait until the last fragmented frame has arrived.
    pub fn read<'b, E>(
        &mut self,
        stream: &mut impl Stream<E>,
        frame_buf: &'b mut [u8],
    ) -> Result<ReadResult<'b>, FramerError<E>> {
        loop {
            if *self.read_cursor == 0 || *self.read_cursor == self.read_len {
                self.read_len = stream.read(self.read_buf).map_err(FramerError::Io)?;
                *self.read_cursor = 0;
            }

            if self.read_len == 0 {
                return Ok(ReadResult::Closed);
            }

            loop {
                if *self.read_cursor == self.read_len {
                    break;
                }

                if self.frame_cursor == frame_buf.len() {
                    return Err(FramerError::FrameTooLarge(frame_buf.len()));
                }

                let ws_result = self
                    .websocket
                    .read(
                        &self.read_buf[*self.read_cursor..self.read_len],
                        &mut frame_buf[self.frame_cursor..],
                    )
                    .map_err(FramerError::WebSocket)?;

                *self.read_cursor += ws_result.len_from;

                match ws_result.message_type {
                    WebSocketReceiveMessageType::Binary => {
                        self.frame_cursor += ws_result.len_to;
                        if ws_result.end_of_message {
                            let frame = &frame_buf[..self.frame_cursor];
                            self.frame_cursor = 0;
                            return Ok(ReadResult::Binary(frame));
                        }
                    }
                    WebSocketReceiveMessageType::Text => {
                        self.frame_cursor += ws_result.len_to;
                        if ws_result.end_of_message {
                            let frame = &frame_buf[..self.frame_cursor];
                            self.frame_cursor = 0;
                            let text = core::str::from_utf8(frame).map_err(FramerError::Utf8)?;
                            return Ok(ReadResult::Text(text));
                        }
                    }
                    WebSocketReceiveMessageType::CloseMustReply => {
                        self.send_back(
                            stream,
                            frame_buf,
                            ws_result.len_to,
                            WebSocketSendMessageType::CloseReply,
                        )?;
                        return Ok(ReadResult::Closed);
                    }
                    WebSocketReceiveMessageType::CloseCompleted => return Ok(ReadResult::Closed),
                    WebSocketReceiveMessageType::Ping => {
                        self.send_back(
                            stream,
                            frame_buf,
                            ws_result.len_to,
                            WebSocketSendMessageType::Pong,
                        )?;
                    }
                    WebSocketReceiveMessageType::Pong => {
                        let bytes =
                            &frame_buf[self.frame_cursor..self.frame_cursor + ws_result.len_to];
                        return Ok(ReadResult::Pong(bytes));
                    }
                }
            }
        }
    }

    fn send_back<E>(
        &mut self,
        stream: &mut impl Stream<E>,
        frame_buf: &'_ mut [u8],
        len_to: usize,
        send_message_type: WebSocketSendMessageType,
    ) -> Result<(), FramerError<E>> {
        let payload_len = min(self.write_buf.len(), len_to);
        let from = &frame_buf[self.frame_cursor..self.frame_cursor + payload_len];
        let len = self
            .websocket
            .write(send_message_type, true, from, self.write_buf)
            .map_err(FramerError::WebSocket)?;
        stream
            .write_all(&self.write_buf[..len])
            .map_err(FramerError::Io)?;
        Ok(())
    }
}

// ************************************************************************************************
// **************************************** TESTS *************************************************
// ************************************************************************************************

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;
    use crate::{WebSocketClient, WebSocketOpCode, WebSocketServer};

    struct DummyStream {
        pub read_buf: Vec<u8>, // starts off populated
        pub read_cursor: usize,
        pub write_buf: Vec<u8>, // starts off empty
    }

    impl DummyStream {
        pub fn new(read_buf: Vec<u8>) -> Self {
            Self {
                read_buf,
                read_cursor: 0,
                write_buf: Vec::new(),
            }
        }
    }

    impl<E> Stream<E> for DummyStream {
        fn read(&mut self, buf: &mut [u8]) -> Result<usize, E> {
            let len = buf.len().min(self.read_buf.len() - self.read_cursor);
            buf[..len].copy_from_slice(&self.read_buf[self.read_cursor..self.read_cursor + len]);
            self.read_cursor += len;
            Ok(len)
        }

        fn write_all(&mut self, buf: &[u8]) -> Result<(), E> {
            self.write_buf.extend_from_slice(buf);
            Ok(())
        }
    }

    #[test]
    fn fragmented_frames() {
        let mut read_buf = vec![0; 1024];
        let mut write_buf = vec![0; 1024];
        let mut read_cursor = 0;
        let mut ws_client = WebSocketClient::new_client(rand::thread_rng());
        ws_client.state = WebSocketState::Open;
        let mut client_framer = Framer::new(
            &mut read_buf,
            &mut read_cursor,
            &mut write_buf,
            &mut ws_client,
        );

        let mut frame_buf = vec![0; 1024];
        let frames = get_fragmented_frames();
        let mut stream = DummyStream::new(frames);
        let frame = client_framer
            .read::<()>(&mut stream, &mut frame_buf)
            .unwrap();
        match frame {
            ReadResult::Text(x) => {
                assert_eq!(x, "hello world!")
            }
            _ => panic!("expected text frame"),
        };
    }

    #[test]
    fn fragmented_frames_with_control_frames() {
        let mut read_buf = vec![0; 1024];
        let mut write_buf = vec![0; 1024];
        let mut read_cursor = 0;
        let mut ws_client = WebSocketClient::new_client(rand::thread_rng());
        ws_client.state = WebSocketState::Open;
        let mut client_framer = Framer::new(
            &mut read_buf,
            &mut read_cursor,
            &mut write_buf,
            &mut ws_client,
        );

        let mut frame_buf = vec![0; 1024];
        let frames = get_fragmented_frames_with_ping();
        let mut stream = DummyStream::new(frames);
        let frame = client_framer
            .read::<()>(&mut stream, &mut frame_buf)
            .unwrap();
        match frame {
            ReadResult::Text(x) => {
                assert_eq!(x, "hello world!")
            }
            _ => panic!("expected text frame"),
        };
    }

    fn get_fragmented_frames() -> Vec<u8> {
        // returns a buffer with 3 websocket frames.
        // A fragmented text frame
        //   followed by a text continuation frame
        //   followed by a final text continuation frame
        // "hello" + " world" + "!"
        let mut messages = Vec::new();
        let mut scratch = vec![0u8; 1024];
        let mut ws_server = WebSocketServer::new_server();
        let len = ws_server
            .write_frame(
                "hello".as_bytes(),
                &mut scratch,
                WebSocketOpCode::TextFrame,
                false,
            )
            .unwrap();
        messages.extend_from_slice(&scratch[..len]);
        let len = ws_server
            .write_frame(
                " world".as_bytes(),
                &mut scratch,
                WebSocketOpCode::ContinuationFrame,
                false,
            )
            .unwrap();
        messages.extend_from_slice(&scratch[..len]);

        let len = ws_server
            .write_frame(
                "!".as_bytes(),
                &mut scratch,
                WebSocketOpCode::ContinuationFrame,
                true,
            )
            .unwrap();
        messages.extend_from_slice(&scratch[..len]);
        messages
    }

    fn get_fragmented_frames_with_ping() -> Vec<u8> {
        // returns a buffer with 3 websocket frames.
        // A fragmented text frame
        //   followed by a Ping control message
        //   followed by a final text continuation frame
        // "hello" + Ping + " world!"
        let mut messages = Vec::new();
        let mut scratch = vec![0u8; 1024];
        let mut ws_server = WebSocketServer::new_server();
        let len = ws_server
            .write_frame(
                "hello".as_bytes(),
                &mut scratch,
                WebSocketOpCode::TextFrame,
                false,
            )
            .unwrap();
        messages.extend_from_slice(&scratch[..len]);
        let len = ws_server
            .write_frame(b"", &mut scratch, WebSocketOpCode::Ping, true)
            .unwrap();
        messages.extend_from_slice(&scratch[..len]);
        let len = ws_server
            .write_frame(
                " world!".as_bytes(),
                &mut scratch,
                WebSocketOpCode::ContinuationFrame,
                true,
            )
            .unwrap();
        messages.extend_from_slice(&scratch[..len]);
        messages
    }
}
