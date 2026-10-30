// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use alloc::{string::String, vec::Vec};
use core::{convert::Infallible, fmt, str};
use embedded_io::{Read, Write};

const MAX_HEADERS: usize = 32;
const MAX_CHUNK_LINE_SIZE: usize = 128;
const MAX_TRAILER_SIZE: usize = 8 * 1024;
const READ_BUFFER_SIZE: usize = 1024;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scheme {
    Http,
    Https,
}

impl Scheme {
    pub const fn default_port(self) -> u16 {
        match self {
            Self::Http => 80,
            Self::Https => 443,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Method {
    Get,
    Post,
    Delete,
}

impl Method {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Get => "GET",
            Self::Post => "POST",
            Self::Delete => "DELETE",
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Header {
    pub name: String,
    pub value: String,
}

impl Header {
    pub fn new(name: impl Into<String>, value: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            value: value.into(),
        }
    }

    pub fn is_name(&self, name: &str) -> bool {
        self.name.eq_ignore_ascii_case(name)
    }
}

impl fmt::Debug for Header {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let value = if self.is_name("authorization") {
            "<redacted>"
        } else {
            &self.value
        };

        f.debug_struct("Header")
            .field("name", &self.name)
            .field("value", &value)
            .finish()
    }
}

/// A complete HTTP request at the socket boundary.
pub struct Request<'a> {
    pub method: Method,
    /// Endpoint path prefix, for example `/v1`.
    pub base_path: &'a str,
    /// Request path without a leading slash, for example `responses`.
    pub path: &'a str,
    /// Value for the HTTP `Host` header.
    pub host: &'a str,
    pub headers: &'a [Header],
    pub accept: &'a str,
    pub content_type: Option<&'a str>,
    pub bearer_token: Option<&'a str>,
    pub organization: Option<&'a str>,
    pub project: Option<&'a str>,
    /// `None` omits `Content-Length`; `Some(0)` sends `Content-Length: 0`.
    pub body_len: Option<usize>,
}

impl fmt::Debug for Request<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Request")
            .field("method", &self.method)
            .field("base_path", &self.base_path)
            .field("path", &self.path)
            .field("host", &self.host)
            .field("headers", &self.headers)
            .field("body_len", &self.body_len)
            .finish()
    }
}

#[derive(Debug)]
pub struct Response<B> {
    pub status: u16,
    pub headers: Vec<Header>,
    pub body: B,
}

impl<B> Response<B> {
    pub const fn is_success(&self) -> bool {
        self.status >= 200 && self.status < 300
    }
}

/// Supplies an already-connected blocking byte stream.
///
/// Implementations own DNS, TCP, timeouts, and optional TLS. The API and HTTP
/// layers only depend on synchronous `embedded_io::Read + Write` operations.
pub trait SocketTransport {
    type Error: embedded_io::Error;
    type Socket<'a>: Read<Error = Self::Error> + Write<Error = Self::Error>
    where
        Self: 'a;

    fn connect<'a>(
        &'a mut self,
        host: &str,
        port: u16,
        scheme: Scheme,
    ) -> Result<Self::Socket<'a>, Self::Error>;
}

/// A response body that can be consumed incrementally without async polling.
pub trait HttpBody {
    type Error;

    /// Returns `0` when the HTTP message body is complete.
    fn read(&mut self, buffer: &mut [u8]) -> Result<usize, Self::Error>;
}

#[derive(Debug)]
pub enum HttpError<E> {
    Transport(E),
    InvalidRequest,
    InvalidResponse,
    ConnectionClosed,
    HeaderTooLarge { limit: usize },
    TooManyHeaders,
    InvalidContentLength,
    UnsupportedTransferEncoding,
    InvalidChunk,
}

impl<E: fmt::Display> fmt::Display for HttpError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Transport(error) => write!(f, "socket error: {error}"),
            Self::InvalidRequest => f.write_str("invalid HTTP request"),
            Self::InvalidResponse => f.write_str("invalid HTTP response"),
            Self::ConnectionClosed => {
                f.write_str("connection closed before the HTTP message completed")
            }
            Self::HeaderTooLarge { limit } => {
                write!(f, "HTTP headers exceeded the configured {limit}-byte limit")
            }
            Self::TooManyHeaders => f.write_str("HTTP response contained too many headers"),
            Self::InvalidContentLength => f.write_str("invalid HTTP Content-Length header"),
            Self::UnsupportedTransferEncoding => f.write_str("unsupported HTTP Transfer-Encoding"),
            Self::InvalidChunk => f.write_str("invalid HTTP chunked body"),
        }
    }
}

#[cfg(feature = "std")]
impl<E> std::error::Error for HttpError<E> where E: std::error::Error + 'static {}

#[derive(Debug, Default)]
pub struct BufferedBody {
    bytes: Vec<u8>,
    offset: usize,
}

impl BufferedBody {
    pub fn new(bytes: impl Into<Vec<u8>>) -> Self {
        Self {
            bytes: bytes.into(),
            offset: 0,
        }
    }

    pub fn into_inner(self) -> Vec<u8> {
        self.bytes
    }
}

impl HttpBody for BufferedBody {
    type Error = Infallible;

    fn read(&mut self, buffer: &mut [u8]) -> Result<usize, Self::Error> {
        if buffer.is_empty() || self.offset == self.bytes.len() {
            return Ok(0);
        }

        let remaining = &self.bytes[self.offset..];
        let count = remaining.len().min(buffer.len());
        buffer[..count].copy_from_slice(&remaining[..count]);
        self.offset += count;
        Ok(count)
    }
}

#[derive(Debug, Clone, Copy)]
enum BodyFraming {
    Empty,
    ContentLength(usize),
    Chunked(ChunkState),
    UntilEof,
}

#[derive(Debug, Clone, Copy)]
enum ChunkState {
    Size,
    Data(usize),
    DataEnd,
    Trailers(usize),
    Done,
}

/// HTTP body decoder for fixed-length, chunked, and connection-delimited bodies.
#[derive(Debug)]
pub struct HttpResponseBody<S> {
    socket: S,
    prefix: Vec<u8>,
    prefix_offset: usize,
    framing: BodyFraming,
}

impl<S> HttpResponseBody<S> {
    pub fn into_inner(self) -> S {
        self.socket
    }
}

impl<S> HttpResponseBody<S>
where
    S: Read,
{
    fn read_raw(&mut self, buffer: &mut [u8]) -> Result<usize, HttpError<S::Error>> {
        if buffer.is_empty() {
            return Ok(0);
        }

        if self.prefix_offset < self.prefix.len() {
            let available = &self.prefix[self.prefix_offset..];
            let count = available.len().min(buffer.len());
            buffer[..count].copy_from_slice(&available[..count]);
            self.prefix_offset += count;
            return Ok(count);
        }

        self.socket.read(buffer).map_err(HttpError::Transport)
    }

    fn read_raw_exact(&mut self, buffer: &mut [u8]) -> Result<(), HttpError<S::Error>> {
        let mut offset = 0;
        while offset < buffer.len() {
            let count = self.read_raw(&mut buffer[offset..])?;
            if count == 0 {
                return Err(HttpError::ConnectionClosed);
            }
            offset += count;
        }
        Ok(())
    }

    fn read_crlf_line(&mut self, line: &mut [u8]) -> Result<usize, HttpError<S::Error>> {
        let mut len = 0;
        loop {
            let mut byte = [0u8; 1];
            self.read_raw_exact(&mut byte)?;
            if byte[0] == b'\n' {
                if len == 0 || line[len - 1] != b'\r' {
                    return Err(HttpError::InvalidChunk);
                }
                return Ok(len - 1);
            }
            if len == line.len() {
                return Err(HttpError::InvalidChunk);
            }
            line[len] = byte[0];
            len += 1;
        }
    }

    fn discard_crlf_line(&mut self, limit: usize) -> Result<usize, HttpError<S::Error>> {
        let mut len = 0;
        let mut previous = None;
        loop {
            let mut byte = [0u8; 1];
            self.read_raw_exact(&mut byte)?;
            if byte[0] == b'\n' {
                if previous != Some(b'\r') {
                    return Err(HttpError::InvalidChunk);
                }
                return Ok(len - 1);
            }
            if len == limit {
                return Err(HttpError::InvalidChunk);
            }
            previous = Some(byte[0]);
            len += 1;
        }
    }

    fn read_chunk_size(&mut self) -> Result<usize, HttpError<S::Error>> {
        let mut line = [0u8; MAX_CHUNK_LINE_SIZE];
        let len = self.read_crlf_line(&mut line)?;
        let size = line[..len]
            .split(|byte| *byte == b';')
            .next()
            .unwrap_or_default();
        let size = str::from_utf8(size)
            .map_err(|_| HttpError::InvalidChunk)?
            .trim();
        if size.is_empty() {
            return Err(HttpError::InvalidChunk);
        }
        usize::from_str_radix(size, 16).map_err(|_| HttpError::InvalidChunk)
    }

    fn read_chunked(&mut self, buffer: &mut [u8]) -> Result<usize, HttpError<S::Error>> {
        loop {
            match self.framing {
                BodyFraming::Chunked(ChunkState::Size) => {
                    let size = self.read_chunk_size()?;
                    self.framing = if size == 0 {
                        BodyFraming::Chunked(ChunkState::Trailers(0))
                    } else {
                        BodyFraming::Chunked(ChunkState::Data(size))
                    };
                }
                BodyFraming::Chunked(ChunkState::Data(remaining)) => {
                    let limit = buffer.len().min(remaining);
                    let count = self.read_raw(&mut buffer[..limit])?;
                    if count == 0 {
                        return Err(HttpError::ConnectionClosed);
                    }
                    self.framing = if count == remaining {
                        BodyFraming::Chunked(ChunkState::DataEnd)
                    } else {
                        BodyFraming::Chunked(ChunkState::Data(remaining - count))
                    };
                    return Ok(count);
                }
                BodyFraming::Chunked(ChunkState::DataEnd) => {
                    let mut crlf = [0u8; 2];
                    self.read_raw_exact(&mut crlf)?;
                    if crlf != *b"\r\n" {
                        return Err(HttpError::InvalidChunk);
                    }
                    self.framing = BodyFraming::Chunked(ChunkState::Size);
                }
                BodyFraming::Chunked(ChunkState::Trailers(total)) => {
                    let len = self.discard_crlf_line(MAX_TRAILER_SIZE)?;
                    let total = total.saturating_add(len + 2);
                    if total > MAX_TRAILER_SIZE {
                        return Err(HttpError::HeaderTooLarge {
                            limit: MAX_TRAILER_SIZE,
                        });
                    }
                    self.framing = if len == 0 {
                        BodyFraming::Chunked(ChunkState::Done)
                    } else {
                        BodyFraming::Chunked(ChunkState::Trailers(total))
                    };
                }
                BodyFraming::Chunked(ChunkState::Done) => return Ok(0),
                _ => return Err(HttpError::InvalidChunk),
            }
        }
    }
}

impl<S> HttpBody for HttpResponseBody<S>
where
    S: Read,
{
    type Error = HttpError<S::Error>;

    fn read(&mut self, buffer: &mut [u8]) -> Result<usize, Self::Error> {
        if buffer.is_empty() {
            return Ok(0);
        }

        match self.framing {
            BodyFraming::Empty => Ok(0),
            BodyFraming::ContentLength(0) => Ok(0),
            BodyFraming::ContentLength(remaining) => {
                let limit = buffer.len().min(remaining);
                let count = self.read_raw(&mut buffer[..limit])?;
                if count == 0 {
                    return Err(HttpError::ConnectionClosed);
                }
                self.framing = BodyFraming::ContentLength(remaining - count);
                Ok(count)
            }
            BodyFraming::Chunked(_) => self.read_chunked(buffer),
            BodyFraming::UntilEof => self.read_raw(buffer),
        }
    }
}

pub enum SendRequestError<E, B> {
    Http(HttpError<E>),
    Body(B),
}

/// Writes one HTTP/1.1 request and parses the response from a connected socket.
pub fn send_request_with_body<S, B, F>(
    mut socket: S,
    request: Request<'_>,
    max_header_size: usize,
    write_body: F,
) -> Result<Response<HttpResponseBody<S>>, SendRequestError<S::Error, B>>
where
    S: Read + Write,
    F: FnOnce(&mut S) -> Result<(), B>,
{
    write_request_head(&mut socket, &request).map_err(SendRequestError::Http)?;
    write_body(&mut socket).map_err(SendRequestError::Body)?;
    socket
        .flush()
        .map_err(|error| SendRequestError::Http(HttpError::Transport(error)))?;
    log_request_sent(&request);
    read_response(socket, max_header_size).map_err(SendRequestError::Http)
}

fn write_request_head<S>(socket: &mut S, request: &Request<'_>) -> Result<(), HttpError<S::Error>>
where
    S: Write,
{
    if (!request.base_path.is_empty() && !request.base_path.starts_with('/'))
        || contains_line_break(request.base_path)
        || contains_line_break(request.path)
        || request.host.is_empty()
        || contains_line_break(request.host)
    {
        return Err(HttpError::InvalidRequest);
    }

    write_bytes(socket, request.method.as_str().as_bytes())?;
    write_bytes(socket, b" ")?;
    write_target(socket, request.base_path, request.path)?;
    write_bytes(socket, b" HTTP/1.1\r\nHost: ")?;
    write_bytes(socket, request.host.as_bytes())?;
    write_bytes(socket, b"\r\nConnection: close\r\n")?;

    if let Some(body_len) = request.body_len {
        socket
            .write_fmt(format_args!("Content-Length: {body_len}\r\n"))
            .map_err(|error| match error {
                embedded_io::WriteFmtError::Other(error) => HttpError::Transport(error),
                embedded_io::WriteFmtError::FmtError => HttpError::InvalidRequest,
            })?;
    }

    for header in request.headers {
        validate_request_header(header)?;
        if !is_replaced_header(header, request) {
            write_header(socket, &header.name, &header.value)?;
        }
    }

    write_header(socket, "Accept", request.accept)?;
    if let Some(content_type) = request.content_type {
        write_header(socket, "Content-Type", content_type)?;
    }
    if let Some(api_key) = request.bearer_token {
        write_bytes(socket, b"Authorization: Bearer ")?;
        write_bytes(socket, api_key.as_bytes())?;
        write_bytes(socket, b"\r\n")?;
    }
    if let Some(organization) = request.organization {
        write_header(socket, "OpenAI-Organization", organization)?;
    }
    if let Some(project) = request.project {
        write_header(socket, "OpenAI-Project", project)?;
    }
    write_bytes(socket, b"\r\n")?;
    Ok(())
}

fn write_target<S>(socket: &mut S, base_path: &str, path: &str) -> Result<(), HttpError<S::Error>>
where
    S: Write,
{
    if base_path.is_empty() {
        write_bytes(socket, b"/")?;
        write_bytes(socket, path.as_bytes())?;
    } else {
        write_bytes(socket, base_path.as_bytes())?;
        if !path.is_empty() {
            write_bytes(socket, b"/")?;
            write_bytes(socket, path.as_bytes())?;
        }
    }
    Ok(())
}

fn write_header<S>(socket: &mut S, name: &str, value: &str) -> Result<(), HttpError<S::Error>>
where
    S: Write,
{
    write_bytes(socket, name.as_bytes())?;
    write_bytes(socket, b": ")?;
    write_bytes(socket, value.as_bytes())?;
    write_bytes(socket, b"\r\n")
}

fn validate_request_header<E>(header: &Header) -> Result<(), HttpError<E>> {
    if header.name.is_empty()
        || contains_line_break(&header.name)
        || contains_line_break(&header.value)
        || header.is_name("host")
        || header.is_name("connection")
        || header.is_name("content-length")
        || header.is_name("transfer-encoding")
    {
        return Err(HttpError::InvalidRequest);
    }
    Ok(())
}

fn is_replaced_header(header: &Header, request: &Request<'_>) -> bool {
    header.is_name("accept")
        || (request.content_type.is_some() && header.is_name("content-type"))
        || (request.bearer_token.is_some() && header.is_name("authorization"))
        || (request.organization.is_some() && header.is_name("openai-organization"))
        || (request.project.is_some() && header.is_name("openai-project"))
}

fn log_request_sent(request: &Request<'_>) {
    print!("[http] {} ", request.method.as_str());
    if request.base_path.is_empty() {
        print!("/");
        print!("{}", request.path);
    } else {
        print!("{}", request.base_path);
        if !request.path.is_empty() {
            print!("/{}", request.path);
        }
    }
    if let Some(body_len) = request.body_len {
        println!(" sent, waiting for response... ({body_len} bytes body)");
    } else {
        println!(" sent, waiting for response...");
    }
}

fn write_bytes<S>(socket: &mut S, bytes: &[u8]) -> Result<(), HttpError<S::Error>>
where
    S: Write,
{
    socket.write_all(bytes).map_err(HttpError::Transport)
}

fn read_response<S>(
    mut socket: S,
    max_header_size: usize,
) -> Result<Response<HttpResponseBody<S>>, HttpError<S::Error>>
where
    S: Read,
{
    let mut buffer = Vec::new();
    loop {
        if let Some(head) = parse_response_head(&buffer)? {
            if (100..200).contains(&head.status) {
                if head.status == 101 {
                    return Err(HttpError::InvalidResponse);
                }
                buffer.drain(..head.length);
                continue;
            }

            let prefix = buffer.split_off(head.length);
            let no_body = head.status == 204 || head.status == 304;
            let framing = if no_body {
                BodyFraming::Empty
            } else if head.chunked {
                BodyFraming::Chunked(ChunkState::Size)
            } else if let Some(length) = head.content_length {
                if prefix.len() > length {
                    return Err(HttpError::InvalidResponse);
                }
                BodyFraming::ContentLength(length)
            } else {
                BodyFraming::UntilEof
            };

            match framing {
                BodyFraming::Empty => {
                    println!(
                        "[http] response: {}, {} headers, no body",
                        head.status,
                        head.headers.len()
                    )
                }
                BodyFraming::ContentLength(length) => println!(
                    "[http] response: {}, {} headers, content-length: {}",
                    head.status,
                    head.headers.len(),
                    length
                ),
                BodyFraming::Chunked(_) => {
                    println!(
                        "[http] response: {}, {} headers, chunked",
                        head.status,
                        head.headers.len()
                    )
                }
                BodyFraming::UntilEof => {
                    println!(
                        "[http] response: {}, {} headers, until-eof",
                        head.status,
                        head.headers.len()
                    )
                }
            }

            return Ok(Response {
                status: head.status,
                headers: head.headers,
                body: HttpResponseBody {
                    socket,
                    prefix,
                    prefix_offset: 0,
                    framing,
                },
            });
        }

        if buffer.len() >= max_header_size {
            return Err(HttpError::HeaderTooLarge {
                limit: max_header_size,
            });
        }
        let mut chunk = [0u8; READ_BUFFER_SIZE];
        let capacity = (max_header_size - buffer.len()).min(chunk.len());
        let count = socket
            .read(&mut chunk[..capacity])
            .map_err(HttpError::Transport)?;
        if count == 0 {
            return Err(HttpError::ConnectionClosed);
        }
        buffer.extend_from_slice(&chunk[..count]);
    }
}

struct ParsedHead {
    length: usize,
    status: u16,
    headers: Vec<Header>,
    content_length: Option<usize>,
    chunked: bool,
}

fn parse_response_head<E>(buffer: &[u8]) -> Result<Option<ParsedHead>, HttpError<E>> {
    let mut raw_headers = [httparse::EMPTY_HEADER; MAX_HEADERS];
    let mut response = httparse::Response::new(&mut raw_headers);
    let length = match response.parse(buffer) {
        Ok(httparse::Status::Partial) => return Ok(None),
        Ok(httparse::Status::Complete(length)) => length,
        Err(httparse::Error::TooManyHeaders) => return Err(HttpError::TooManyHeaders),
        Err(_) => return Err(HttpError::InvalidResponse),
    };
    let status = response.code.ok_or(HttpError::InvalidResponse)?;
    let mut headers = Vec::new();
    let mut content_length = None;
    let mut chunked = false;

    for header in response.headers {
        let value = str::from_utf8(header.value).map_err(|_| HttpError::InvalidResponse)?;
        headers.push(Header::new(header.name, value));
        if header.name.eq_ignore_ascii_case("content-length") {
            let parsed = value
                .trim()
                .parse::<usize>()
                .map_err(|_| HttpError::InvalidContentLength)?;
            if content_length
                .replace(parsed)
                .is_some_and(|old| old != parsed)
            {
                return Err(HttpError::InvalidContentLength);
            }
        } else if header.name.eq_ignore_ascii_case("transfer-encoding") {
            for encoding in value.split(',').map(str::trim) {
                if encoding.eq_ignore_ascii_case("chunked") {
                    chunked = true;
                } else if !encoding.eq_ignore_ascii_case("identity") {
                    return Err(HttpError::UnsupportedTransferEncoding);
                }
            }
        }
    }

    Ok(Some(ParsedHead {
        length,
        status,
        headers,
        content_length,
        chunked,
    }))
}

fn contains_line_break(value: &str) -> bool {
    value.bytes().any(|byte| byte == b'\r' || byte == b'\n')
}
