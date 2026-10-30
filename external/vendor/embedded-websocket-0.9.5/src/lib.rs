//! # Embedded Websocket
//!
//! `embedded_websocket` facilitates the encoding and decoding of websocket frames and can be used
//! for both clients and servers. The library is intended to be used in constrained memory
//! environments like embedded microcontrollers which cannot reference the rust standard library.
//! It will work with arbitrarily small buffers regardless of websocket frame size as long as the
//! websocket header can be read (2 - 14 bytes depending on the payload size and masking).
//! Since the library is essentially an encoder or decoder of byte slices, the developer is free to
//! use whatever transport mechanism they chose. The examples in the source repository use the
//! TcpStream from the standard library.

// support for websockets without using the standard library
#![cfg_attr(not(feature = "std"), no_std)]

use byteorder::{BigEndian, ByteOrder};
use core::{cmp, result, str};
use heapless::{String, Vec};
use rand_core::RngCore;
use sha1::{Digest, Sha1};

mod http;
pub mod random;
pub use self::http::{read_http_header, WebSocketContext};
pub use self::random::EmptyRng;

// support for working with discrete websocket frames when using IO streams
// start here!!
pub mod framer;
pub mod framer_async;
const MASK_KEY_LEN: usize = 4;

/// Result returning a websocket specific error if encountered
pub type Result<T> = result::Result<T, Error>;

/// A fixed length 24-character string used to hold a websocket key for the opening handshake
pub type WebSocketKey = String<24>;

/// A maximum sized 24-character string used to store a sub protocol (e.g. `chat`)
pub type WebSocketSubProtocol = String<24>;

/// Websocket send message type used when sending a websocket frame
#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum WebSocketSendMessageType {
    /// A UTF8 encoded text string
    Text = 1,
    /// Binary data
    Binary = 2,
    /// An unsolicited ping message
    Ping = 9,
    /// A pong message in response to a ping message
    Pong = 10,
    /// A close message in response to a close message from the other party. Used to complete a
    /// closing handshake. If initiate a close handshake use the `close` function
    CloseReply = 11,
}

impl WebSocketSendMessageType {
    fn to_op_code(self) -> WebSocketOpCode {
        match self {
            WebSocketSendMessageType::Text => WebSocketOpCode::TextFrame,
            WebSocketSendMessageType::Binary => WebSocketOpCode::BinaryFrame,
            WebSocketSendMessageType::Ping => WebSocketOpCode::Ping,
            WebSocketSendMessageType::Pong => WebSocketOpCode::Pong,
            WebSocketSendMessageType::CloseReply => WebSocketOpCode::ConnectionClose,
        }
    }
}

/// Websocket receive message type use when reading a websocket frame
#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum WebSocketReceiveMessageType {
    /// A UTF8 encoded text string
    Text = 1,
    /// Binary data
    Binary = 2,
    /// Signals that the close handshake is complete
    CloseCompleted = 7,
    /// Signals that the other party has initiated the close handshake. If you receive this message
    /// you should respond with a `WebSocketSendMessageType::CloseReply` with the same payload as
    /// close message
    CloseMustReply = 8,
    /// A ping message that you should respond to with a `WebSocketSendMessageType::Pong` message
    /// including the same payload as the ping
    Ping = 9,
    /// A pong message in response to a ping message
    Pong = 10,
}

/// Websocket close status code as per the rfc6455 websocket spec
#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum WebSocketCloseStatusCode {
    /// Normal closure (1000), meaning that the purpose for which the connection was established
    /// has been fulfilled
    NormalClosure,
    /// Endpoint unavailable (1001) indicates that an endpoint is "going away", such as a server
    /// going down or a browser having navigated away from a page
    EndpointUnavailable,
    /// Protocol error (1002) indicates that an endpoint is terminating the connection due
    /// to a protocol error.
    ProtocolError,
    /// Invalid message type (1003) indicates that an endpoint is terminating the connection
    /// because it has received a type of data it cannot accept (e.g., an endpoint that
    /// understands only text data MAY send this if it receives a binary message)
    InvalidMessageType,
    /// Reserved (1004) for future use
    Reserved,
    /// Empty (1005) indicates that no status code was present
    Empty,
    /// Invalid payload data (1007) indicates that an endpoint is terminating the connection
    /// because it has received data within a message that was not consistent with the type of
    /// the message (e.g., non-UTF-8 data within a text message)
    InvalidPayloadData,
    /// Policy violation (1008) indicates that an endpoint is terminating the connection because
    /// it has received a message that violates its policy. This is a generic status code that
    /// can be returned when there is no other more suitable status code
    PolicyViolation,
    /// Message too big (1009) indicates that an endpoint is terminating the connection because
    /// it has received a message that is too big for it to process
    MessageTooBig,
    /// Mandatory extension (1010) indicates that an endpoint (client) is terminating the
    /// connection because it has expected the server to negotiate one or more extension, but
    /// the server didn't return them in the response message of the WebSocket handshake
    MandatoryExtension,
    /// Internal server error (1011) indicates that a server is terminating the connection because
    /// it encountered an unexpected condition that prevented it from fulfilling the request
    InternalServerError,
    /// TLS handshake (1015) connection was closed due to a failure to perform a TLS handshake
    TlsHandshake,
    /// Custom close code
    Custom(u16),
}

impl WebSocketCloseStatusCode {
    fn from_u16(value: u16) -> WebSocketCloseStatusCode {
        match value {
            1000 => WebSocketCloseStatusCode::NormalClosure,
            1001 => WebSocketCloseStatusCode::EndpointUnavailable,
            1002 => WebSocketCloseStatusCode::ProtocolError,
            1003 => WebSocketCloseStatusCode::InvalidMessageType,
            1004 => WebSocketCloseStatusCode::Reserved,
            1005 => WebSocketCloseStatusCode::Empty,
            1007 => WebSocketCloseStatusCode::InvalidPayloadData,
            1008 => WebSocketCloseStatusCode::PolicyViolation,
            1009 => WebSocketCloseStatusCode::MessageTooBig,
            1010 => WebSocketCloseStatusCode::MandatoryExtension,
            1011 => WebSocketCloseStatusCode::InternalServerError,
            1015 => WebSocketCloseStatusCode::TlsHandshake,
            _ => WebSocketCloseStatusCode::Custom(value),
        }
    }

    fn to_u16(self) -> u16 {
        match self {
            WebSocketCloseStatusCode::NormalClosure => 1000,
            WebSocketCloseStatusCode::EndpointUnavailable => 1001,
            WebSocketCloseStatusCode::ProtocolError => 1002,
            WebSocketCloseStatusCode::InvalidMessageType => 1003,
            WebSocketCloseStatusCode::Reserved => 1004,
            WebSocketCloseStatusCode::Empty => 1005,
            WebSocketCloseStatusCode::InvalidPayloadData => 1007,
            WebSocketCloseStatusCode::PolicyViolation => 1008,
            WebSocketCloseStatusCode::MessageTooBig => 1009,
            WebSocketCloseStatusCode::MandatoryExtension => 1010,
            WebSocketCloseStatusCode::InternalServerError => 1011,
            WebSocketCloseStatusCode::TlsHandshake => 1015,
            WebSocketCloseStatusCode::Custom(value) => value,
        }
    }
}

/// The state of the websocket
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum WebSocketState {
    /// The websocket has been created with `new_client()` or `new_server()`
    None = 0,
    /// The client has created an opening handshake
    Connecting = 1,
    /// The server has completed the opening handshake via server_accept() or, likewise, the
    /// client has completed the opening handshake via client_accept(). The user is free to call
    /// `write()`, `read()` or `close()` on the websocket
    Open = 2,
    /// The `close()` function has been called
    CloseSent = 3,
    /// A Close websocket frame has been received
    CloseReceived = 4,
    /// The close handshake has been completed
    Closed = 5,
    /// The server or client opening handshake failed
    Aborted = 6,
}

/// Websocket specific errors
#[derive(PartialEq, Eq, Debug)]
pub enum Error {
    /// Websocket frame has an invalid opcode
    InvalidOpCode,
    InvalidFrameLength,
    InvalidCloseStatusCode,
    WebSocketNotOpen,
    WebsocketAlreadyOpen,
    Utf8Error,
    Unknown,
    HttpHeader(httparse::Error),
    HttpHeaderNoPath,
    HttpHeaderIncomplete,
    WriteToBufferTooSmall,
    ReadFrameIncomplete,
    HttpResponseCodeInvalid(Option<u16>),
    AcceptStringInvalid,
    ConvertInfallible,
    RandCore,
    UnexpectedContinuationFrame,
}

impl From<httparse::Error> for Error {
    fn from(err: httparse::Error) -> Error {
        Error::HttpHeader(err)
    }
}

impl From<str::Utf8Error> for Error {
    fn from(_: str::Utf8Error) -> Error {
        Error::Utf8Error
    }
}

impl From<core::convert::Infallible> for Error {
    fn from(_: core::convert::Infallible) -> Error {
        Error::ConvertInfallible
    }
}

impl From<()> for Error {
    fn from(_: ()) -> Error {
        Error::Unknown
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::HttpHeader(error) => write!(f, "bad http header {error}"),
            Error::HttpResponseCodeInvalid(Some(code)) => write!(f, "bad http response ({code})"),
            _ => write!(f, "{:?}", self),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        if let Self::HttpHeader(error) = self {
            Some(error)
        } else {
            None
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum WebSocketOpCode {
    ContinuationFrame = 0,
    TextFrame = 1,
    BinaryFrame = 2,
    ConnectionClose = 8,
    Ping = 9,
    Pong = 10,
}

impl WebSocketOpCode {
    fn to_message_type(self) -> Result<WebSocketReceiveMessageType> {
        match self {
            WebSocketOpCode::TextFrame => Ok(WebSocketReceiveMessageType::Text),
            WebSocketOpCode::BinaryFrame => Ok(WebSocketReceiveMessageType::Binary),
            _ => Err(Error::InvalidOpCode),
        }
    }
}

/// The metadata result of a `read` function call of a websocket
#[derive(Debug)]
pub struct WebSocketReadResult {
    /// Number of bytes read from the `from` buffer
    pub len_from: usize,
    /// Number of bytes written to the `to` buffer
    pub len_to: usize,
    /// End of message flag is `true` if the `to` buffer contains an entire websocket frame
    /// payload otherwise `false` if the user must continue calling the read function to get the
    /// rest of the payload
    pub end_of_message: bool,
    /// Close status code (as per the websocket spec) if the message type is `CloseMustReply` or
    /// `CloseCompleted`. If a close status is specified then a UTF8 encoded string could also
    /// appear in the frame payload giving more detailed information about why the websocket was
    /// closed.
    pub close_status: Option<WebSocketCloseStatusCode>,
    /// The websocket frame type
    pub message_type: WebSocketReceiveMessageType,
}

/// Websocket options used by a websocket client to initiate an opening handshake with a
/// websocket server
pub struct WebSocketOptions<'a> {
    /// The request uri (e.g. `/chat?id=123`) of the GET method used to identify the endpoint of the
    /// websocket connection. This allows multiple domains to be served by a single server.
    /// This could also be used to send identifiable information about the client
    pub path: &'a str,
    /// The hostname (e.g. `server.example.com`) is used so that both the client and the server
    /// can verify that they agree on which host is in use
    pub host: &'a str,
    /// The origin (e.g. `http://example.com`) is used to protect against unauthorized
    /// cross-origin use of a WebSocket server by scripts using the WebSocket API in a web
    /// browser. This field is usually only set by browser clients but servers may require it
    /// so it has been exposed here.
    pub origin: &'a str,
    /// A list of requested sub protocols in order of preference. The server should return the
    /// first sub protocol it supports or none at all. A sub protocol can be anything agreed
    /// between the server and client
    pub sub_protocols: Option<&'a [&'a str]>,
    /// Any additional headers the server may require that are not part of the websocket
    /// spec. These should be fully formed http headers without the `\r\n` (e.g. `MyHeader: foo`)
    pub additional_headers: Option<&'a [&'a str]>,
}

/// Used to return a sized type from `WebSocket::new_server()`
pub type WebSocketServer = WebSocket<EmptyRng, Server>;

/// Used to return a sized type from `WebSocketClient::new_client()`
pub type WebSocketClient<T> = WebSocket<T, Client>;

// Simple Typestate pattern for preventing panics and allowing reuse of underlying
// read/read_frame/etc..
pub enum Server {}
pub enum Client {}

pub trait WebSocketType {}
impl WebSocketType for Server {}
impl WebSocketType for Client {}

/// Websocket client and server implementation
pub struct WebSocket<T, S: WebSocketType>
where
    T: RngCore,
{
    is_client: bool,
    rng: T,
    continuation_frame_op_code: Option<WebSocketOpCode>,
    is_write_continuation: bool,
    pub state: WebSocketState,
    continuation_read: Option<ContinuationRead>,
    marker: core::marker::PhantomData<S>,
}

impl<T, Type> WebSocket<T, Type>
where
    T: RngCore,
    Type: WebSocketType,
{
    /// Creates a new websocket client by passing in a required random number generator
    ///
    /// # Examples
    /// ```
    /// use embedded_websocket as ws;
    /// use rand;
    /// let mut ws_client = ws::WebSocketClient::new_client(rand::thread_rng());
    ///
    /// assert_eq!(ws::WebSocketState::None, ws_client.state);
    /// ```
    pub fn new_client(rng: T) -> WebSocketClient<T> {
        WebSocket {
            is_client: true,
            rng,
            continuation_frame_op_code: None,
            is_write_continuation: false,
            state: WebSocketState::None,
            continuation_read: None,
            marker: core::marker::PhantomData::<Client>,
        }
    }

    /// Creates a new websocket server. Note that you must use the `WebSocketServer` type and
    /// not the generic `WebSocket` type for this call or you will get a `'type annotations needed'`
    /// compilation error.
    ///
    /// # Examples
    /// ```
    /// use embedded_websocket as ws;
    /// let mut ws_server = ws::WebSocketServer::new_server();
    ///
    /// assert_eq!(ws::WebSocketState::None, ws_server.state);
    /// ```
    pub fn new_server() -> WebSocketServer {
        let rng = EmptyRng::new();
        WebSocket {
            is_client: false,
            rng,
            continuation_frame_op_code: None,
            is_write_continuation: false,
            state: WebSocketState::None,
            continuation_read: None,
            marker: core::marker::PhantomData::<Server>,
        }
    }
}

impl<T> WebSocket<T, Server>
where
    T: RngCore,
{
    /// Used by the server to accept an incoming client connection and build a websocket upgrade
    /// http response string. The client http header should be read with the `read_http_header`
    /// function and the result should be passed to this function.
    /// Websocket state will change from None -> Open if successful, otherwise None -> Aborted
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_websocket as ws;
    /// let mut buffer: [u8; 1000] = [0; 1000];
    /// let mut ws_server = ws::WebSocketServer::new_server();
    /// let ws_key = ws::WebSocketKey::from("Z7OY1UwHOx/nkSz38kfPwg==");
    /// let sub_protocol = ws::WebSocketSubProtocol::from("chat");
    /// let len = ws_server
    ///     .server_accept(&ws_key, Some(&sub_protocol), &mut buffer)
    ///     .unwrap();
    /// let response = std::str::from_utf8(&buffer[..len]).unwrap();
    ///
    /// assert_eq!("HTTP/1.1 101 Switching Protocols\r\nConnection: Upgrade\r\nUpgrade: websocket\r\nSec-WebSocket-Protocol: chat\r\nSec-WebSocket-Accept: ptPnPeDOTo6khJlzmLhOZSh2tAY=\r\n\r\n", response);
    /// ```
    ///
    /// # Errors
    /// There should be no way for a user provided input to return the errors listed below as the
    /// input is already constrained.
    /// * The http response is built with a stack allocated 1KB buffer and it *should be impossible*
    ///   for it to return an  `Unknown` error if that buffer is too small. However, this is better
    ///   than a panic and it will do so if the response header is too large to fit in the buffer
    /// * This function can return an `Utf8Error` if there was an error with the generation of the
    ///   accept string. This should also be impossible but an error is preferable to a panic
    /// * Returns `WebsocketAlreadyOpen` if called on a websocket that is already open
    pub fn server_accept(
        &mut self,
        sec_websocket_key: &WebSocketKey,
        sec_websocket_protocol: Option<&WebSocketSubProtocol>,
        to: &mut [u8],
    ) -> Result<usize> {
        if self.state == WebSocketState::Open {
            return Err(Error::WebsocketAlreadyOpen);
        }

        match http::build_connect_handshake_response(sec_websocket_key, sec_websocket_protocol, to)
        {
            Ok(http_response_len) => {
                self.state = WebSocketState::Open;
                Ok(http_response_len)
            }
            Err(e) => {
                self.state = WebSocketState::Aborted;
                Err(e)
            }
        }
    }
}

impl<T> WebSocket<T, Client>
where
    T: RngCore,
{
    /// Used by the client to initiate a websocket opening handshake
    ///
    /// # Examples
    /// ```
    /// use embedded_websocket as ws;
    /// let mut buffer: [u8; 2000] = [0; 2000];
    /// let mut ws_client = ws::WebSocketClient::new_client(rand::thread_rng());
    /// let sub_protocols = ["chat", "superchat"];
    /// let websocket_options = ws::WebSocketOptions {
    ///     path: "/chat",
    ///     host: "localhost",
    ///     origin: "http://localhost",
    ///     sub_protocols: Some(&sub_protocols),
    ///     additional_headers: None,
    /// };
    ///
    /// let (len, web_socket_key) = ws_client.client_connect(&websocket_options, &mut buffer).unwrap();
    ///
    /// let actual_http = std::str::from_utf8(&buffer[..len]).unwrap();
    /// let mut expected_http = String::new();
    /// expected_http.push_str("GET /chat HTTP/1.1\r\nHost: localhost\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: ");
    /// expected_http.push_str(web_socket_key.as_str());
    /// expected_http.push_str("\r\nOrigin: http://localhost\r\nSec-WebSocket-Protocol: chat, superchat\r\nSec-WebSocket-Version: 13\r\n\r\n");
    /// assert_eq!(expected_http.as_str(), actual_http);
    /// ```
    ///
    /// # Errors
    /// * The http response is built with a stack allocated 1KB buffer and will return an `Unknown` error
    ///   if that buffer is too small. This would happen is the user supplied too many
    ///   additional headers or the sub-protocol string is too large
    /// * This function can return an `Utf8Error` if there was an error with the generation of the
    ///   accept string. This should be impossible but an error is preferable to a panic
    /// * Returns `WebsocketAlreadyOpen` if called on a websocket that is already open
    pub fn client_connect(
        &mut self,
        websocket_options: &WebSocketOptions,
        to: &mut [u8],
    ) -> Result<(usize, WebSocketKey)> {
        if self.state == WebSocketState::Open {
            return Err(Error::WebsocketAlreadyOpen);
        }

        match http::build_connect_handshake_request(websocket_options, &mut self.rng, to) {
            Ok((request_len, sec_websocket_key)) => {
                self.state = WebSocketState::Connecting;
                Ok((request_len, sec_websocket_key))
            }
            Err(e) => Err(e),
        }
    }

    /// Used by a websocket client for checking the server response to an opening handshake
    /// (sent using the client_connect function). If the client requested one or more sub protocols
    /// the server will choose one (or none) and you get that in the result
    /// # Examples
    /// ```
    /// use embedded_websocket as ws;
    /// let mut ws_client = ws::WebSocketClient::new_client(rand::thread_rng());
    /// let ws_key = ws::WebSocketKey::from("Z7OY1UwHOx/nkSz38kfPwg==");
    /// let server_response_html = "HTTP/1.1 101 Switching Protocols\r\nConnection: Upgrade\r\nUpgrade: websocket\r\nSec-WebSocket-Protocol: chat\r\nSec-WebSocket-Accept: ptPnPeDOTo6khJlzmLhOZSh2tAY=\r\n\r\n";    ///
    /// let (len, sub_protocol) = ws_client.client_accept(&ws_key, server_response_html.as_bytes())
    ///     .unwrap();
    ///
    /// assert_eq!(159, len);
    /// assert_eq!("chat", sub_protocol.unwrap());
    /// ```
    /// # Errors
    /// * Returns `HttpResponseCodeInvalid` if the HTTP response code is not `101 Switching Protocols`
    /// * Returns `AcceptStringInvalid` if the web server failed to return a valid accept string
    /// * Returns `HttpHeader(Version)` or some other varient if the HTTP response is not well formed
    /// * Returns `WebsocketAlreadyOpen` if called on a websocket that is already open
    pub fn client_accept(
        &mut self,
        sec_websocket_key: &WebSocketKey,
        from: &[u8],
    ) -> Result<(usize, Option<WebSocketSubProtocol>)> {
        if self.state == WebSocketState::Open {
            return Err(Error::WebsocketAlreadyOpen);
        }

        match http::read_server_connect_handshake_response(sec_websocket_key, from) {
            Ok((len, sec_websocket_protocol)) => {
                self.state = WebSocketState::Open;
                Ok((len, sec_websocket_protocol))
            }
            Err(Error::HttpHeaderIncomplete) => Err(Error::HttpHeaderIncomplete),
            Err(e) => {
                self.state = WebSocketState::Aborted;
                Err(e)
            }
        }
    }
}

impl<T, Type> WebSocket<T, Type>
where
    T: RngCore,
    Type: WebSocketType,
{
    /// Reads the payload from a websocket frame in buffer `from` into a buffer `to` and returns
    /// metadata about the frame. Since this function is designed to be called in a memory
    /// constrained system we may not read the entire payload in one go. In each of the scenarios
    /// below the `read_result.end_of_message` flag would be `false`:
    /// * The payload is fragmented into multiple websocket frames (as per the websocket spec)
    /// * The `from` buffer does not hold the entire websocket frame. For example if only part of
    ///   the frame was read or if the `from` buffer is too small to hold an entire websocket frame
    /// * The `to` buffer is too small to hold the entire websocket frame payload
    ///
    /// If the function returns `read_result.end_of_message` `false` then the next
    /// call to the function should not include data that has already been passed into the function.
    /// The websocket *remembers* the websocket frame header and is able to process the rest of the
    /// payload correctly. If the `from` buffer contains multiple websocket frames then only one of
    /// them will be returned at a time and the user must make multiple calls to the function by
    /// taking note of `read_result.len_from` which tells you how many bytes were read from the
    /// `from` buffer
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_websocket as ws;
    /// //                    h   e   l   l   o
    /// let buffer1 = [129,5,104,101,108,108,111];
    /// let mut buffer2: [u8; 128] = [0; 128];
    /// let mut ws_client = ws::WebSocketClient::new_client(rand::thread_rng());
    /// ws_client.state = ws::WebSocketState::Open; // skip the opening handshake
    /// let ws_result = ws_client.read(&buffer1, &mut buffer2).unwrap();
    ///
    /// assert_eq!("hello".as_bytes(), &buffer2[..ws_result.len_to]);
    /// ```
    /// # Errors
    /// * Returns `WebSocketNotOpen` when the websocket is not open when this function is called
    /// * Returns `InvalidOpCode` if the websocket frame contains an invalid opcode
    /// * Returns `UnexpectedContinuationFrame` if we receive a continuation frame without first
    ///   receiving a non-continuation frame with an opcode describing the payload
    /// * Returns `ReadFrameIncomplete` if the `from` buffer does not contain a full websocket
    ///   header (typically 2-14 bytes depending on the payload)
    /// * Returns `InvalidFrameLength` if the frame length cannot be decoded
    ///
    pub fn read(&mut self, from: &[u8], to: &mut [u8]) -> Result<WebSocketReadResult> {
        if self.state == WebSocketState::Open || self.state == WebSocketState::CloseSent {
            let frame = self.read_frame(from, to)?;

            match frame.op_code {
                WebSocketOpCode::Ping => Ok(frame.to_readresult(WebSocketReceiveMessageType::Ping)),
                WebSocketOpCode::Pong => Ok(frame.to_readresult(WebSocketReceiveMessageType::Pong)),
                WebSocketOpCode::TextFrame => {
                    Ok(frame.to_readresult(WebSocketReceiveMessageType::Text))
                }
                WebSocketOpCode::BinaryFrame => {
                    Ok(frame.to_readresult(WebSocketReceiveMessageType::Binary))
                }
                WebSocketOpCode::ConnectionClose => match self.state {
                    WebSocketState::CloseSent => {
                        self.state = WebSocketState::Closed;
                        Ok(frame.to_readresult(WebSocketReceiveMessageType::CloseCompleted))
                    }
                    _ => {
                        self.state = WebSocketState::CloseReceived;
                        Ok(frame.to_readresult(WebSocketReceiveMessageType::CloseMustReply))
                    }
                },
                WebSocketOpCode::ContinuationFrame => match self.continuation_frame_op_code {
                    Some(cf_op_code) => Ok(frame.to_readresult(cf_op_code.to_message_type()?)),
                    None => Err(Error::UnexpectedContinuationFrame),
                },
            }
        } else {
            Err(Error::WebSocketNotOpen)
        }
    }

    /// Writes the payload in `from` to a websocket frame in `to`
    /// * message_type - The type of message to send: Text, Binary or CloseReply
    /// * end_of_message - False to fragment a frame into multiple smaller frames. The last frame
    ///   should set this to true
    /// * from - The buffer containing the payload to encode
    /// * to - The the buffer to save the websocket encoded payload to.
    ///   Returns the number of bytes written to the `to` buffer
    /// # Examples
    ///
    /// ```
    /// use embedded_websocket as ws;
    /// let mut buffer: [u8; 1000] = [0; 1000];
    /// let mut ws_server = ws::WebSocketServer::new_server();
    /// ws_server.state = ws::WebSocketState::Open; // skip the opening handshake
    /// let len = ws_server.write(ws::WebSocketSendMessageType::Text, true, "hello".as_bytes(),
    ///     &mut buffer).unwrap();
    ///
    /// //                     h   e   l   l   o
    /// let expected = [129,5,104,101,108,108,111];
    /// assert_eq!(&expected, &buffer[..len]);
    /// ```
    /// # Errors
    /// * Returns `WebSocketNotOpen` when the websocket is not open when this function is called
    /// * Returns `WriteToBufferTooSmall` when the `to` buffer is too small to fit the websocket
    ///   frame header (2-14 bytes) plus the payload. Consider fragmenting the messages by making
    ///   multiple write calls with `end_of_message` set to `false` and the final call set to `true`
    pub fn write(
        &mut self,
        message_type: WebSocketSendMessageType,
        end_of_message: bool,
        from: &[u8],
        to: &mut [u8],
    ) -> Result<usize> {
        if self.state == WebSocketState::Open || self.state == WebSocketState::CloseReceived {
            let mut op_code = message_type.to_op_code();
            if op_code == WebSocketOpCode::ConnectionClose {
                self.state = WebSocketState::Closed
            } else if self.is_write_continuation {
                op_code = WebSocketOpCode::ContinuationFrame;
            }

            self.is_write_continuation = !end_of_message;
            self.write_frame(from, to, op_code, end_of_message)
        } else {
            Err(Error::WebSocketNotOpen)
        }
    }

    /// Initiates a close handshake.
    /// Both the client and server may initiate a close handshake. If successful the function
    /// changes the websocket state from Open -> CloseSent
    /// # Errors
    /// * Returns `WebSocketNotOpen` when the websocket is not open when this function is called
    /// * Returns `WriteToBufferTooSmall` when the `to` buffer is too small to fit the websocket
    ///   frame header (2-14 bytes) plus the payload. Consider sending a smaller status_description
    pub fn close(
        &mut self,
        close_status: WebSocketCloseStatusCode,
        status_description: Option<&str>,
        to: &mut [u8],
    ) -> Result<usize> {
        if self.state == WebSocketState::Open {
            self.state = WebSocketState::CloseSent;
            if let Some(status_description) = status_description {
                let mut from_buffer: Vec<u8, 256> = Vec::new();
                from_buffer.extend_from_slice(&close_status.to_u16().to_be_bytes())?;

                // restrict the max size of the status_description
                let len = if status_description.len() < 254 {
                    status_description.len()
                } else {
                    254
                };

                from_buffer.extend_from_slice(&status_description.as_bytes()[..len])?;
                self.write_frame(&from_buffer, to, WebSocketOpCode::ConnectionClose, true)
            } else {
                let mut from_buffer: [u8; 2] = [0; 2];
                BigEndian::write_u16(&mut from_buffer, close_status.to_u16());
                self.write_frame(&from_buffer, to, WebSocketOpCode::ConnectionClose, true)
            }
        } else {
            Err(Error::WebSocketNotOpen)
        }
    }

    fn read_frame(&mut self, from_buffer: &[u8], to_buffer: &mut [u8]) -> Result<WebSocketFrame> {
        match &mut self.continuation_read {
            Some(continuation_read) => {
                let result = read_continuation(continuation_read, from_buffer, to_buffer);
                if result.is_fin_bit_set {
                    self.continuation_read = None;
                    self.continuation_frame_op_code = None;
                }
                Ok(result)
            }
            None => {
                let (mut result, continuation_read) = read_frame(from_buffer, to_buffer)?;

                // handle fragmented messages
                match result.op_code {
                    WebSocketOpCode::BinaryFrame | WebSocketOpCode::TextFrame => {
                        // set the continuation frame op code if this is a fragmented message
                        self.continuation_frame_op_code = if result.is_fin_bit_set {
                            None
                        } else {
                            Some(result.op_code)
                        };
                    }
                    WebSocketOpCode::ContinuationFrame => {
                        // override the op code we get from the result with our continuation frame opcode if it exists
                        if let Some(continuation_frame_op_code) = self.continuation_frame_op_code {
                            result.op_code = continuation_frame_op_code;
                        }
                    }
                    _ => {
                        // control frames should not affect the continuation frame mechanics
                    }
                }

                self.continuation_read = continuation_read;
                Ok(result)
            }
        }
    }

    fn write_frame(
        &mut self,
        from_buffer: &[u8],
        to_buffer: &mut [u8],
        op_code: WebSocketOpCode,
        end_of_message: bool,
    ) -> Result<usize> {
        let fin_bit_set_as_byte: u8 = if end_of_message { 0x80 } else { 0x00 };
        let byte1: u8 = fin_bit_set_as_byte | op_code as u8;
        let count = from_buffer.len();
        const BYTE_HEADER_SIZE: usize = 2;
        const SHORT_HEADER_SIZE: usize = 4;
        const LONG_HEADER_SIZE: usize = 10;
        const MASK_KEY_SIZE: usize = 4;
        let header_size;
        let mask_bit_set_as_byte = if self.is_client { 0x80 } else { 0x00 };
        let payload_len = from_buffer.len() + if self.is_client { MASK_KEY_SIZE } else { 0 };

        // write header followed by the payload
        // header size depends on how large the payload is
        if count < 126 {
            if payload_len + BYTE_HEADER_SIZE > to_buffer.len() {
                return Err(Error::WriteToBufferTooSmall);
            }
            to_buffer[0] = byte1;
            to_buffer[1] = mask_bit_set_as_byte | count as u8;
            header_size = BYTE_HEADER_SIZE;
        } else if count < 65535 {
            if payload_len + SHORT_HEADER_SIZE > to_buffer.len() {
                return Err(Error::WriteToBufferTooSmall);
            }
            to_buffer[0] = byte1;
            to_buffer[1] = mask_bit_set_as_byte | 126;
            BigEndian::write_u16(&mut to_buffer[2..], count as u16);
            header_size = SHORT_HEADER_SIZE;
        } else {
            if payload_len + LONG_HEADER_SIZE > to_buffer.len() {
                return Err(Error::WriteToBufferTooSmall);
            }
            to_buffer[0] = byte1;
            to_buffer[1] = mask_bit_set_as_byte | 127;
            BigEndian::write_u64(&mut to_buffer[2..], count as u64);
            header_size = LONG_HEADER_SIZE;
        }

        // sent by client - need to mask the data
        // we need to mask the bytes to prevent web server caching
        if self.is_client {
            let mut mask_key = [0; MASK_KEY_SIZE];
            self.rng.fill_bytes(&mut mask_key); // clients always have an rng instance
            to_buffer[header_size..header_size + MASK_KEY_SIZE].copy_from_slice(&mask_key);
            let to_buffer_start = header_size + MASK_KEY_SIZE;

            // apply the mask key to every byte in the payload. This is a hot function
            for (i, (from, to)) in from_buffer[..count]
                .iter()
                .zip(&mut to_buffer[to_buffer_start..to_buffer_start + count])
                .enumerate()
            {
                *to = *from ^ mask_key[i % MASK_KEY_SIZE];
            }

            Ok(to_buffer_start + count)
        } else {
            to_buffer[header_size..header_size + count].copy_from_slice(&from_buffer[..count]);
            Ok(header_size + count)
        }
    }
}

// Continuation read is used when we cannot fit the entire websocket frame into the supplied buffer
struct ContinuationRead {
    op_code: WebSocketOpCode,
    count: usize,
    is_fin_bit_set: bool,
    mask_key: Option<[u8; 4]>,
}

struct WebSocketFrame {
    is_fin_bit_set: bool,
    op_code: WebSocketOpCode,
    num_bytes_to: usize,
    num_bytes_from: usize,
    close_status: Option<WebSocketCloseStatusCode>,
}

impl WebSocketFrame {
    fn to_readresult(&self, message_type: WebSocketReceiveMessageType) -> WebSocketReadResult {
        WebSocketReadResult {
            len_from: self.num_bytes_from,
            len_to: self.num_bytes_to,
            end_of_message: self.is_fin_bit_set,
            close_status: self.close_status,
            message_type,
        }
    }
}

fn min(num1: usize, num2: usize, num3: usize) -> usize {
    cmp::min(cmp::min(num1, num2), num3)
}

fn read_into_buffer(
    mask_key: &mut Option<[u8; 4]>,
    from_buffer: &[u8],
    to_buffer: &mut [u8],
    len: usize,
) -> usize {
    // if we are trying to read more than number of bytes in either buffer
    let len_to_read = min(len, to_buffer.len(), from_buffer.len());

    match mask_key {
        Some(mask_key) => {
            // apply the mask key to every byte in the payload. This is a hot function.
            for (i, (from, to)) in from_buffer[..len_to_read].iter().zip(to_buffer).enumerate() {
                *to = *from ^ mask_key[i % MASK_KEY_LEN];
            }
            mask_key.rotate_left(len_to_read % MASK_KEY_LEN);
        }
        None => {
            to_buffer[..len_to_read].copy_from_slice(&from_buffer[..len_to_read]);
        }
    }

    len_to_read
}

fn read_continuation(
    continuation_read: &mut ContinuationRead,
    from_buffer: &[u8],
    to_buffer: &mut [u8],
) -> WebSocketFrame {
    let len_read = read_into_buffer(
        &mut continuation_read.mask_key,
        from_buffer,
        to_buffer,
        continuation_read.count,
    );

    let is_complete = len_read == continuation_read.count;

    let frame = match continuation_read.op_code {
        WebSocketOpCode::ConnectionClose => decode_close_frame(to_buffer, len_read, len_read),
        _ => WebSocketFrame {
            num_bytes_from: len_read,
            num_bytes_to: len_read,
            op_code: continuation_read.op_code,
            close_status: None,
            is_fin_bit_set: if is_complete {
                continuation_read.is_fin_bit_set
            } else {
                false
            },
        },
    };

    continuation_read.count -= len_read;
    frame
}

fn read_frame(
    from_buffer: &[u8],
    to_buffer: &mut [u8],
) -> Result<(WebSocketFrame, Option<ContinuationRead>)> {
    if from_buffer.len() < 2 {
        return Err(Error::ReadFrameIncomplete);
    }

    let byte1 = from_buffer[0];
    let byte2 = from_buffer[1];

    // process first byte
    const FIN_BIT_FLAG: u8 = 0x80;
    const OP_CODE_FLAG: u8 = 0x0F;
    let is_fin_bit_set = (byte1 & FIN_BIT_FLAG) == FIN_BIT_FLAG;
    let op_code = get_op_code(byte1 & OP_CODE_FLAG)?;

    // process second byte
    const MASK_FLAG: u8 = 0x80;
    let is_mask_bit_set = (byte2 & MASK_FLAG) == MASK_FLAG;
    let (len, mut num_bytes_read) = read_length(byte2, &from_buffer[2..])?;

    num_bytes_read += 2;
    let from_buffer = &from_buffer[num_bytes_read..];

    // reads the mask key from the payload if the is_mask_bit_set flag is set
    let mut mask_key = if is_mask_bit_set {
        if from_buffer.len() < MASK_KEY_LEN {
            return Err(Error::ReadFrameIncomplete);
        }
        let mut mask_key: [u8; MASK_KEY_LEN] = [0; MASK_KEY_LEN];
        mask_key.copy_from_slice(&from_buffer[..MASK_KEY_LEN]);
        num_bytes_read += MASK_KEY_LEN;
        Some(mask_key)
    } else {
        None
    };

    let len_read = if is_mask_bit_set {
        // start after the mask key
        let from_buffer = &from_buffer[MASK_KEY_LEN..];
        read_into_buffer(&mut mask_key, from_buffer, to_buffer, len)
    } else {
        read_into_buffer(&mut mask_key, from_buffer, to_buffer, len)
    };

    let has_continuation = len_read < len;
    num_bytes_read += len_read;

    let frame = match op_code {
        WebSocketOpCode::ConnectionClose => decode_close_frame(to_buffer, num_bytes_read, len_read),
        _ => WebSocketFrame {
            num_bytes_from: num_bytes_read,
            num_bytes_to: len_read,
            op_code,
            close_status: None,
            is_fin_bit_set: if has_continuation {
                false
            } else {
                is_fin_bit_set
            },
        },
    };

    if has_continuation {
        let continuation_read = Some(ContinuationRead {
            op_code,
            count: len - len_read,
            is_fin_bit_set,
            mask_key,
        });
        Ok((frame, continuation_read))
    } else {
        Ok((frame, None))
    }
}

fn get_op_code(val: u8) -> Result<WebSocketOpCode> {
    match val {
        0 => Ok(WebSocketOpCode::ContinuationFrame),
        1 => Ok(WebSocketOpCode::TextFrame),
        2 => Ok(WebSocketOpCode::BinaryFrame),
        8 => Ok(WebSocketOpCode::ConnectionClose),
        9 => Ok(WebSocketOpCode::Ping),
        10 => Ok(WebSocketOpCode::Pong),
        _ => Err(Error::InvalidOpCode),
    }
}

// returns (len, how_many_bytes_were_read)
fn read_length(byte2: u8, from_buffer: &[u8]) -> Result<(usize, usize)> {
    let len = byte2 & 0x7F;

    if len < 126 {
        // for messages smaller than 126 bytes
        return Ok((len as usize, 0));
    } else if len == 126 {
        // for messages smaller than 64KB
        if from_buffer.len() < 2 {
            return Err(Error::ReadFrameIncomplete);
        }
        let mut buf: [u8; 2] = [0; 2];
        buf.copy_from_slice(&from_buffer[..2]);
        return Ok((BigEndian::read_u16(&buf) as usize, 2));
    } else if len == 127 {
        // for messages larger than 64KB
        if from_buffer.len() < 8 {
            return Err(Error::ReadFrameIncomplete);
        }
        let mut buf: [u8; 8] = [0; 8];
        buf.copy_from_slice(&from_buffer[..8]);
        return Ok((BigEndian::read_u64(&buf) as usize, 8));
    }

    Err(Error::InvalidFrameLength)
}

fn decode_close_frame(buffer: &mut [u8], num_bytes_read: usize, len: usize) -> WebSocketFrame {
    if len >= 2 {
        // NOTE: for now, don't read the close status description
        let code = BigEndian::read_u16(buffer);
        let close_status_code = WebSocketCloseStatusCode::from_u16(code);

        return WebSocketFrame {
            num_bytes_from: num_bytes_read,
            num_bytes_to: len,
            op_code: WebSocketOpCode::ConnectionClose,
            close_status: Some(close_status_code),
            is_fin_bit_set: true,
        };
    }

    build_client_disconnected_frame(num_bytes_read)
}

fn build_client_disconnected_frame(num_bytes_from: usize) -> WebSocketFrame {
    WebSocketFrame {
        num_bytes_from,
        num_bytes_to: 0,
        op_code: WebSocketOpCode::ConnectionClose,
        close_status: Some(WebSocketCloseStatusCode::InternalServerError),
        is_fin_bit_set: true,
    }
}

// ************************************************************************************************
// **************************************** TESTS *************************************************
// ************************************************************************************************

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;

    #[test]
    fn opening_handshake() {
        let client_request = "GET /chat HTTP/1.1
Host: localhost:5000
User-Agent: Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:62.0) Gecko/20100101 Firefox/62.0
Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8
Accept-Language: en-US,en;q=0.5
Accept-Encoding: gzip, deflate
Sec-WebSocket-Version: 13
Origin: http://localhost:5000
Sec-WebSocket-Extensions: permessage-deflate
Sec-WebSocket-Key: Z7OY1UwHOx/nkSz38kfPwg==
Sec-WebSocket-Protocol: chat
DNT: 1
Connection: keep-alive, Upgrade
Pragma: no-cache
Cache-Control: no-cache
Upgrade: websocket

";

        let mut headers = [httparse::EMPTY_HEADER; 16];
        let mut request = httparse::Request::new(&mut headers);
        request.parse(client_request.as_bytes()).unwrap();
        let headers = headers.iter().map(|f| (f.name, f.value));
        let web_socket_context = read_http_header(headers).unwrap().unwrap();
        assert_eq!(
            "Z7OY1UwHOx/nkSz38kfPwg==",
            web_socket_context.sec_websocket_key
        );
        assert_eq!(
            "chat",
            web_socket_context
                .sec_websocket_protocol_list
                .get(0)
                .unwrap()
                .as_str()
        );
        let mut web_socket = WebSocketServer::new_server();

        let mut ws_buffer: [u8; 3000] = [0; 3000];
        let size = web_socket
            .server_accept(&web_socket_context.sec_websocket_key, None, &mut ws_buffer)
            .unwrap();
        let response = std::str::from_utf8(&ws_buffer[..size]).unwrap();
        let client_response_expected = "HTTP/1.1 101 Switching Protocols\r\nConnection: Upgrade\r\nUpgrade: websocket\r\nSec-WebSocket-Accept: ptPnPeDOTo6khJlzmLhOZSh2tAY=\r\n\r\n";
        assert_eq!(client_response_expected, response);
    }

    #[test]
    fn server_write_frame() {
        let mut buffer: [u8; 1000] = [0; 1000];
        let mut ws_server = WebSocketServer::new_server();
        let len = ws_server
            .write_frame(
                "hello".as_bytes(),
                &mut buffer,
                WebSocketOpCode::TextFrame,
                true,
            )
            .unwrap();
        let expected = [129, 5, 104, 101, 108, 108, 111];
        assert_eq!(&expected, &buffer[..len]);
    }

    #[test]
    fn server_accept_should_write_sub_protocol() {
        let mut buffer: [u8; 1000] = [0; 1000];
        let mut ws_server = WebSocketServer::new_server();
        let ws_key = WebSocketKey::from("Z7OY1UwHOx/nkSz38kfPwg==");
        let sub_protocol = WebSocketSubProtocol::from("chat");
        let size = ws_server
            .server_accept(&ws_key, Some(&sub_protocol), &mut buffer)
            .unwrap();
        let response = std::str::from_utf8(&buffer[..size]).unwrap();
        assert_eq!("HTTP/1.1 101 Switching Protocols\r\nConnection: Upgrade\r\nUpgrade: websocket\r\nSec-WebSocket-Protocol: chat\r\nSec-WebSocket-Accept: ptPnPeDOTo6khJlzmLhOZSh2tAY=\r\n\r\n", response);
    }

    #[test]
    fn closing_handshake() {
        let mut buffer1: [u8; 500] = [0; 500];
        let mut buffer2: [u8; 500] = [0; 500];

        let mut rng = rand::thread_rng();

        let mut ws_client = WebSocketClient::new_client(&mut rng);
        ws_client.state = WebSocketState::Open;

        let mut ws_server = WebSocketServer::new_server();
        ws_server.state = WebSocketState::Open;

        // client sends a close (initiates the close handshake)
        ws_client
            .close(WebSocketCloseStatusCode::NormalClosure, None, &mut buffer1)
            .unwrap();

        // check that the client receives the close message
        let ws_result = ws_server.read(&buffer1, &mut buffer2).unwrap();
        assert_eq!(
            WebSocketReceiveMessageType::CloseMustReply,
            ws_result.message_type
        );

        // server MUST respond to complete the handshake
        ws_server
            .write(
                WebSocketSendMessageType::CloseReply,
                true,
                &buffer2[..ws_result.len_to],
                &mut buffer1,
            )
            .unwrap();
        assert_eq!(WebSocketState::Closed, ws_server.state);

        // check that the client receives the close message from the server
        let ws_result = ws_client.read(&buffer1, &mut buffer2).unwrap();
        assert_eq!(WebSocketState::Closed, ws_client.state);

        assert_eq!(
            WebSocketReceiveMessageType::CloseCompleted,
            ws_result.message_type
        );
    }

    #[test]
    fn send_message_from_client_to_server() {
        let mut buffer1: [u8; 1000] = [0; 1000];
        let mut buffer2: [u8; 1000] = [0; 1000];

        // how to create a client
        let mut ws_client = WebSocketClient::new_client(rand::thread_rng());

        ws_client.state = WebSocketState::Open;
        let mut ws_server = WebSocketServer::new_server();
        ws_server.state = WebSocketState::Open;

        // client sends a Text message
        let hello = "hello";
        let num_bytes = ws_client
            .write(
                WebSocketSendMessageType::Text,
                true,
                &hello.as_bytes(),
                &mut buffer1,
            )
            .unwrap();

        // check that the Server receives the Text message
        let ws_result = ws_server.read(&buffer1[..num_bytes], &mut buffer2).unwrap();
        assert_eq!(WebSocketReceiveMessageType::Text, ws_result.message_type);
        let received = std::str::from_utf8(&buffer2[..ws_result.len_to]).unwrap();
        assert_eq!(hello, received);
    }

    #[test]
    fn send_message_from_server_to_client() {
        let mut buffer1: [u8; 1000] = [0; 1000];
        let mut buffer2: [u8; 1000] = [0; 1000];

        let mut ws_client = WebSocketClient::new_client(rand::thread_rng());
        ws_client.state = WebSocketState::Open;
        let mut ws_server = WebSocketServer::new_server();
        ws_server.state = WebSocketState::Open;

        // server sends a Text message
        let hello = "hello";
        let num_bytes = ws_server
            .write(
                WebSocketSendMessageType::Text,
                true,
                &hello.as_bytes(),
                &mut buffer1,
            )
            .unwrap();

        // check that the client receives the Text message
        let ws_result = ws_client.read(&buffer1[..num_bytes], &mut buffer2).unwrap();
        assert_eq!(WebSocketReceiveMessageType::Text, ws_result.message_type);
        let received = std::str::from_utf8(&buffer2[..ws_result.len_to]).unwrap();
        assert_eq!(hello, received);
    }

    #[test]
    fn receive_buffer_too_small() {
        let mut buffer1: [u8; 1000] = [0; 1000];
        let mut buffer2: [u8; 1000] = [0; 1000];

        let mut ws_client = WebSocketClient::new_client(rand::thread_rng());
        ws_client.state = WebSocketState::Open;
        let mut ws_server = WebSocketServer::new_server();
        ws_server.state = WebSocketState::Open;

        let hello = "hello";
        ws_server
            .write(
                WebSocketSendMessageType::Text,
                true,
                &hello.as_bytes(),
                &mut buffer1,
            )
            .unwrap();

        match ws_client.read(&buffer1[..1], &mut buffer2) {
            Err(Error::ReadFrameIncomplete) => {
                // test passes
            }
            _ => {
                assert_eq!(true, false);
            }
        }
    }

    #[test]
    fn receive_large_frame_with_small_receive_buffer() {
        let mut buffer1: [u8; 1000] = [0; 1000];
        let mut buffer2: [u8; 1000] = [0; 1000];

        let mut ws_client = WebSocketClient::new_client(rand::thread_rng());
        ws_client.state = WebSocketState::Open;
        let mut ws_server = WebSocketServer::new_server();
        ws_server.state = WebSocketState::Open;

        let hello = "hello";
        ws_server
            .write(
                WebSocketSendMessageType::Text,
                true,
                &hello.as_bytes(),
                &mut buffer1,
            )
            .unwrap();

        let ws_result = ws_client.read(&buffer1[..2], &mut buffer2).unwrap();
        assert_eq!(0, ws_result.len_to);
        assert_eq!(false, ws_result.end_of_message);
        let ws_result = ws_client.read(&buffer1[2..3], &mut buffer2).unwrap();
        assert_eq!(1, ws_result.len_to);
        assert_eq!(
            "h",
            std::str::from_utf8(&buffer2[..ws_result.len_to]).unwrap()
        );
        assert_eq!(false, ws_result.end_of_message);
        let ws_result = ws_client.read(&buffer1[3..], &mut buffer2).unwrap();
        assert_eq!(4, ws_result.len_to);
        assert_eq!(
            "ello",
            std::str::from_utf8(&buffer2[..ws_result.len_to]).unwrap()
        );
        assert_eq!(true, ws_result.end_of_message);
    }

    #[test]
    fn send_large_frame() {
        let buffer1 = [0u8; 15944];
        let mut buffer2 = [0u8; 64000];
        let mut buffer3 = [0u8; 64000];

        let mut ws_client = WebSocketClient::new_client(rand::thread_rng());
        ws_client.state = WebSocketState::Open;

        ws_client
            .write(
                WebSocketSendMessageType::Binary,
                true,
                &buffer1,
                &mut buffer2,
            )
            .unwrap();

        let ws_result = ws_client.read(&buffer2, &mut buffer3).unwrap();
        assert_eq!(true, ws_result.end_of_message);
        assert_eq!(buffer1.len(), ws_result.len_to);
    }

    #[test]
    fn receive_large_frame_multi_read() {
        let mut buffer1 = [0_u8; 1000];
        let mut buffer2 = [0_u8; 1000];

        let mut ws_client = WebSocketClient::new_client(rand::thread_rng());
        ws_client.state = WebSocketState::Open;
        let mut ws_server = WebSocketServer::new_server();
        ws_server.state = WebSocketState::Open;

        let message = "Hello, world. This is a long message that takes multiple reads";
        ws_server
            .write(
                WebSocketSendMessageType::Text,
                true,
                &message.as_bytes(),
                &mut buffer1,
            )
            .unwrap();

        let mut buffer2_cursor = 0;
        let ws_result = ws_client.read(&buffer1[..40], &mut buffer2).unwrap();
        assert_eq!(false, ws_result.end_of_message);
        buffer2_cursor += ws_result.len_to;
        let ws_result = ws_client
            .read(
                &buffer1[ws_result.len_from..],
                &mut buffer2[buffer2_cursor..],
            )
            .unwrap();
        assert_eq!(true, ws_result.end_of_message);
        buffer2_cursor += ws_result.len_to;

        assert_eq!(
            message,
            std::str::from_utf8(&buffer2[..buffer2_cursor]).unwrap()
        );
    }

    #[test]
    fn multiple_messages_in_receive_buffer() {
        let mut buffer1 = [0_u8; 1000];
        let mut buffer2 = [0_u8; 1000];

        let mut ws_client = WebSocketClient::new_client(rand::thread_rng());
        ws_client.state = WebSocketState::Open;
        let mut ws_server = WebSocketServer::new_server();
        ws_server.state = WebSocketState::Open;

        let message1 = "Hello, world.";
        let len = ws_client
            .write(
                WebSocketSendMessageType::Text,
                true,
                &message1.as_bytes(),
                &mut buffer1,
            )
            .unwrap();
        let message2 = "This is another message.";
        ws_client
            .write(
                WebSocketSendMessageType::Text,
                true,
                &message2.as_bytes(),
                &mut buffer1[len..],
            )
            .unwrap();

        let mut buffer1_cursor = 0;
        let mut buffer2_cursor = 0;
        let ws_result = ws_server
            .read(&buffer1[buffer1_cursor..], &mut buffer2)
            .unwrap();
        assert_eq!(true, ws_result.end_of_message);
        buffer1_cursor += ws_result.len_from;
        buffer2_cursor += ws_result.len_to;
        let ws_result = ws_server
            .read(&buffer1[buffer1_cursor..], &mut buffer2[buffer2_cursor..])
            .unwrap();
        assert_eq!(true, ws_result.end_of_message);
        assert_eq!(
            message1,
            std::str::from_utf8(&buffer2[..buffer2_cursor]).unwrap()
        );

        assert_eq!(
            message2,
            std::str::from_utf8(&buffer2[buffer2_cursor..buffer2_cursor + ws_result.len_to])
                .unwrap()
        );
    }

    #[test]
    fn receive_large_frame_with_small_send_buffer() {
        let mut buffer1: [u8; 1000] = [0; 1000];
        let mut buffer2: [u8; 1000] = [0; 1000];

        let mut ws_client = WebSocketClient::new_client(rand::thread_rng());
        ws_client.state = WebSocketState::Open;
        let mut ws_server = WebSocketServer::new_server();
        ws_server.state = WebSocketState::Open;

        let hello = "hello";
        ws_server
            .write(
                WebSocketSendMessageType::Text,
                true,
                &hello.as_bytes(),
                &mut buffer1,
            )
            .unwrap();

        let ws_result = ws_client.read(&buffer1, &mut buffer2[..1]).unwrap();
        assert_eq!(1, ws_result.len_to);
        assert_eq!(
            "h",
            std::str::from_utf8(&buffer2[..ws_result.len_to]).unwrap()
        );
        assert_eq!(false, ws_result.end_of_message);
        let ws_result = ws_client
            .read(&buffer1[ws_result.len_from..], &mut buffer2[..4])
            .unwrap();
        assert_eq!(4, ws_result.len_to);
        assert_eq!(
            "ello",
            std::str::from_utf8(&buffer2[..ws_result.len_to]).unwrap()
        );
        assert_eq!(true, ws_result.end_of_message);
    }

    #[test]
    fn send_two_frame_message() {
        let mut buffer1: [u8; 1000] = [0; 1000];
        let mut buffer2: [u8; 1000] = [0; 1000];
        // let mut rng = rand::thread_rng();

        let mut ws_client = WebSocketClient::new_client(rand::thread_rng());
        ws_client.state = WebSocketState::Open;
        let mut ws_server = WebSocketServer::new_server();
        ws_server.state = WebSocketState::Open;

        // client sends a fragmented Text message
        let hello = "Hello, ";
        let num_bytes_hello = ws_server
            .write(
                WebSocketSendMessageType::Text,
                false,
                &hello.as_bytes(),
                &mut buffer1,
            )
            .unwrap();

        // client sends the remaining Text message
        let world = "World!";
        let num_bytes_world = ws_server
            .write(
                WebSocketSendMessageType::Text,
                true,
                &world.as_bytes(),
                &mut buffer1[num_bytes_hello..],
            )
            .unwrap();

        // check that the Server receives the entire Text message
        let ws_result1 = ws_client
            .read(&buffer1[..num_bytes_hello], &mut buffer2)
            .unwrap();
        assert_eq!(WebSocketReceiveMessageType::Text, ws_result1.message_type);
        assert_eq!(false, ws_result1.end_of_message);
        let ws_result2 = ws_client
            .read(
                &buffer1[num_bytes_hello..num_bytes_hello + num_bytes_world],
                &mut buffer2[ws_result1.len_to..],
            )
            .unwrap();
        assert_eq!(WebSocketReceiveMessageType::Text, ws_result2.message_type);
        assert_eq!(true, ws_result2.end_of_message);

        let received =
            std::str::from_utf8(&buffer2[..ws_result1.len_to + ws_result2.len_to]).unwrap();
        assert_eq!("Hello, World!", received);
    }

    #[test]
    fn send_multi_frame_message() {
        let mut buffer1: [u8; 1000] = [0; 1000];
        let mut buffer2: [u8; 1000] = [0; 1000];

        let mut ws_client = WebSocketClient::new_client(rand::thread_rng());
        ws_client.state = WebSocketState::Open;
        let mut ws_server = WebSocketServer::new_server();
        ws_server.state = WebSocketState::Open;

        // server sends the first fragmented Text frame
        let fragment1 = "fragment1";
        let fragment1_num_bytes = ws_server
            .write(
                WebSocketSendMessageType::Text,
                false,
                &fragment1.as_bytes(),
                &mut buffer1,
            )
            .unwrap();

        // send fragment2 as a continuation frame
        let fragment2 = "fragment2";
        let fragment2_num_bytes = ws_server
            .write(
                WebSocketSendMessageType::Text,
                false,
                &fragment2.as_bytes(),
                &mut buffer1[fragment1_num_bytes..],
            )
            .unwrap();

        // send fragment3 as a continuation frame and indicate that this is the last frame
        let fragment3 = "fragment3";
        let _fragment3_num_bytes = ws_server
            .write(
                WebSocketSendMessageType::Text,
                true,
                &fragment3.as_bytes(),
                &mut buffer1[fragment1_num_bytes + fragment2_num_bytes..],
            )
            .unwrap();

        // check that the client receives the "fragment1" Text message
        let ws_result = ws_client.read(&buffer1, &mut buffer2).unwrap();
        assert_eq!(WebSocketReceiveMessageType::Text, ws_result.message_type);
        let received = std::str::from_utf8(&buffer2[..ws_result.len_to]).unwrap();
        assert_eq!(fragment1, received);
        assert_eq!(ws_result.end_of_message, false);
        let mut read_cursor = ws_result.len_from;

        // check that the client receives the "fragment2" Text message
        let ws_result = ws_client
            .read(&buffer1[read_cursor..], &mut buffer2)
            .unwrap();
        assert_eq!(WebSocketReceiveMessageType::Text, ws_result.message_type);
        let received = std::str::from_utf8(&buffer2[..ws_result.len_to]).unwrap();
        assert_eq!(fragment2, received);
        assert_eq!(ws_result.end_of_message, false);
        read_cursor += ws_result.len_from;

        // check that the client receives the "fragment3" Text message
        let ws_result = ws_client
            .read(&buffer1[read_cursor..], &mut buffer2)
            .unwrap();
        assert_eq!(WebSocketReceiveMessageType::Text, ws_result.message_type);
        let received = std::str::from_utf8(&buffer2[..ws_result.len_to]).unwrap();
        assert_eq!(fragment3, received);
        assert_eq!(ws_result.end_of_message, true);

        // check the actual bytes in the write buffer for fragment1
        let (is_fin_bit_set, op_code) = read_first_byte(buffer1[0]);
        assert_eq!(is_fin_bit_set, false);
        assert_eq!(op_code, WebSocketOpCode::TextFrame);

        // check the actual bytes in the write buffer for fragment2
        let (is_fin_bit_set, op_code) = read_first_byte(buffer1[fragment1_num_bytes]);
        assert_eq!(is_fin_bit_set, false);
        assert_eq!(op_code, WebSocketOpCode::ContinuationFrame);

        // check the actual bytes in the write buffer for fragment3
        let (is_fin_bit_set, op_code) =
            read_first_byte(buffer1[fragment1_num_bytes + fragment2_num_bytes]);
        assert_eq!(is_fin_bit_set, true);
        assert_eq!(op_code, WebSocketOpCode::ContinuationFrame);
    }

    fn read_first_byte(byte: u8) -> (bool, WebSocketOpCode) {
        const FIN_BIT_FLAG: u8 = 0x80;
        const OP_CODE_FLAG: u8 = 0x0F;
        let is_fin_bit_set = (byte & FIN_BIT_FLAG) == FIN_BIT_FLAG;
        let op_code = get_op_code(byte & OP_CODE_FLAG).unwrap();
        (is_fin_bit_set, op_code)
    }
}
