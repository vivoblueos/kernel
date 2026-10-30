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

use alloc::{format, string::String, vec::Vec};
use core::fmt::Write;
use embedded_io::Write as _;
use serde::{de::DeserializeOwned, Serialize};

use crate::{
    api::{
        chat::{ChatCompletionRequest, ChatCompletionResponse},
        common::DeletionStatus,
        embeddings::{EmbeddingRequest, EmbeddingResponse},
        models::{Model, ModelList},
        responses::{
            CountTokensRequest, CountTokensResponse, CreateResponseRequest, ResponseObject,
        },
    },
    error::{ApiErrorEnvelope, ConfigError, Error},
    http::{
        self, Header, HttpBody, HttpError, HttpResponseBody, Method, Request, Response, Scheme,
        SocketTransport,
    },
    sse::ApiStream,
};

pub const DEFAULT_API_ENDPOINT: &str = "https://api.openai.com/v1";
const DEFAULT_MAX_RESPONSE_BODY_SIZE: usize = 1024 * 1024;
const DEFAULT_MAX_RESPONSE_HEADER_SIZE: usize = 16 * 1024;
const READ_BUFFER_SIZE: usize = 1024;

pub trait StreamingRequest: Serialize {
    fn stream_mut(&mut self) -> &mut Option<bool>;
}

impl<'a> StreamingRequest for ChatCompletionRequest<'a> {
    fn stream_mut(&mut self) -> &mut Option<bool> {
        &mut self.stream
    }
}

impl StreamingRequest for CreateResponseRequest {
    fn stream_mut(&mut self) -> &mut Option<bool> {
        &mut self.stream
    }
}

#[derive(Debug)]
pub struct ApiResponse<T> {
    pub status: u16,
    pub headers: Vec<Header>,
    pub data: T,
}

impl<T> ApiResponse<T> {
    pub fn into_inner(self) -> T {
        self.data
    }

    pub fn header(&self, name: &str) -> Option<&str> {
        self.headers
            .iter()
            .find(|header| header.is_name(name))
            .map(|header| header.value.as_str())
    }
}

#[derive(Debug, Clone)]
struct Endpoint {
    scheme: Scheme,
    host: String,
    port: u16,
    authority: String,
    base_path: String,
}

impl Endpoint {
    fn parse(endpoint: &str) -> Result<Self, ConfigError> {
        if endpoint.is_empty() {
            return Err(ConfigError::EmptyEndpoint);
        }
        if contains_line_break(endpoint) || endpoint.contains(['?', '#', '@']) {
            return Err(ConfigError::InvalidEndpoint);
        }

        let (scheme, rest) = endpoint
            .split_once("://")
            .ok_or(ConfigError::InvalidEndpoint)?;
        let scheme = match scheme {
            "http" => Scheme::Http,
            "https" => Scheme::Https,
            _ => return Err(ConfigError::InvalidEndpoint),
        };
        let (authority, path) = match rest.find('/') {
            Some(index) => (&rest[..index], &rest[index..]),
            None => (rest, ""),
        };
        if authority.is_empty() {
            return Err(ConfigError::InvalidEndpoint);
        }

        let (host, port) = parse_authority(authority, scheme.default_port())?;
        let mut base_path = String::from(path.trim_end_matches('/'));
        if base_path == "/" {
            base_path.clear();
        }

        Ok(Self {
            scheme,
            host,
            port,
            authority: String::from(authority),
            base_path,
        })
    }
}

pub struct ClientBuilder<T> {
    transport: T,
    endpoint: String,
    api_key: Option<String>,
    organization: Option<String>,
    project: Option<String>,
    headers: Vec<Header>,
    host_header: Option<String>,
    max_response_body_size: usize,
    max_response_header_size: usize,
}

impl<T> ClientBuilder<T> {
    pub fn new(transport: T) -> Self {
        Self {
            transport,
            endpoint: String::from(DEFAULT_API_ENDPOINT),
            api_key: None,
            organization: None,
            project: None,
            headers: Vec::new(),
            host_header: None,
            max_response_body_size: DEFAULT_MAX_RESPONSE_BODY_SIZE,
            max_response_header_size: DEFAULT_MAX_RESPONSE_HEADER_SIZE,
        }
    }

    pub fn with_api_key(mut self, api_key: impl Into<String>) -> Self {
        self.api_key = Some(api_key.into());
        self
    }

    pub fn with_endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.endpoint = endpoint.into();
        self
    }

    pub fn with_organization(mut self, organization: impl Into<String>) -> Self {
        self.organization = Some(organization.into());
        self
    }

    pub fn with_project(mut self, project: impl Into<String>) -> Self {
        self.project = Some(project.into());
        self
    }

    pub fn with_header(mut self, name: impl Into<String>, value: impl Into<String>) -> Self {
        upsert_header(&mut self.headers, Header::new(name, value));
        self
    }

    pub fn with_host_header(mut self, host: impl Into<String>) -> Self {
        self.host_header = Some(host.into());
        self
    }

    pub fn with_max_response_body_size(mut self, bytes: usize) -> Self {
        self.max_response_body_size = bytes;
        self
    }

    pub fn with_max_response_header_size(mut self, bytes: usize) -> Self {
        self.max_response_header_size = bytes;
        self
    }

    pub fn build(self) -> Result<Client<T>, ConfigError> {
        let endpoint = Endpoint::parse(self.endpoint.trim_end_matches('/'))?;

        if let Some(api_key) = &self.api_key {
            if contains_line_break(api_key) {
                return Err(ConfigError::InvalidApiKey);
            }
        }
        for header in &self.headers {
            validate_header(header)?;
        }
        if let Some(organization) = &self.organization {
            validate_header_value("OpenAI-Organization", organization)?;
        }
        if let Some(project) = &self.project {
            validate_header_value("OpenAI-Project", project)?;
        }

        Ok(Client {
            transport: self.transport,
            endpoint,
            api_key: self.api_key,
            organization: self.organization,
            project: self.project,
            headers: self.headers,
            host_header: self.host_header,
            max_response_body_size: self.max_response_body_size,
            max_response_header_size: self.max_response_header_size,
        })
    }
}

pub struct Client<T> {
    transport: T,
    endpoint: Endpoint,
    api_key: Option<String>,
    organization: Option<String>,
    project: Option<String>,
    headers: Vec<Header>,
    host_header: Option<String>,
    max_response_body_size: usize,
    max_response_header_size: usize,
}

impl<T> Client<T> {
    pub fn builder(transport: T) -> ClientBuilder<T> {
        ClientBuilder::new(transport)
    }

    pub fn new(transport: T, api_key: impl Into<String>) -> Result<Self, ConfigError> {
        Self::builder(transport).with_api_key(api_key).build()
    }

    pub fn endpoint(&self) -> String {
        let mut endpoint = format!(
            "{}://{}",
            match self.endpoint.scheme {
                Scheme::Http => "http",
                Scheme::Https => "https",
            },
            self.endpoint.authority
        );
        endpoint.push_str(&self.endpoint.base_path);
        endpoint
    }

    pub fn transport_mut(&mut self) -> &mut T {
        &mut self.transport
    }

    pub fn into_transport(self) -> T {
        self.transport
    }
}

impl<T: SocketTransport> Client<T> {
    pub fn get_json<R>(&mut self, path: &str) -> Result<ApiResponse<R>, Error<T::Error>>
    where
        R: DeserializeOwned,
    {
        let max_response_body_size = self.max_response_body_size;
        let response = self.send_http(Method::Get, path, None, false, None, |_| Ok(()))?;
        decode_json(response, max_response_body_size)
    }

    pub fn post_json<Q, R>(
        &mut self,
        path: &str,
        request: &Q,
    ) -> Result<ApiResponse<R>, Error<T::Error>>
    where
        Q: Serialize + ?Sized,
        R: DeserializeOwned,
    {
        let max_response_body_size = self.max_response_body_size;
        let response = self.send_json(Method::Post, path, request, false)?;
        decode_json(response, max_response_body_size)
    }

    pub fn delete_json<R>(&mut self, path: &str) -> Result<ApiResponse<R>, Error<T::Error>>
    where
        R: DeserializeOwned,
    {
        let max_response_body_size = self.max_response_body_size;
        let response = self.send_http(Method::Delete, path, None, false, None, |_| Ok(()))?;
        decode_json(response, max_response_body_size)
    }

    pub fn send_raw(
        &mut self,
        method: Method,
        path: &str,
        body: &[u8],
        content_type: Option<&str>,
    ) -> Result<ApiResponse<Vec<u8>>, Error<T::Error>> {
        self.send_buffered_with_content_type(method, path, body, content_type)
    }

    pub fn post_json_stream<'a, Q>(
        &'a mut self,
        path: &str,
        request: &mut Q,
    ) -> Result<ApiStream<HttpResponseBody<T::Socket<'a>>>, Error<T::Error>>
    where
        Q: StreamingRequest + ?Sized,
    {
        let max_response_body_size = self.max_response_body_size;
        let previous_stream = request.stream_mut().replace(true);
        let response = self.send_json(Method::Post, path, request, true);
        *request.stream_mut() = previous_stream;

        let response = response?;
        if !(200..300).contains(&response.status) {
            let status = response.status;
            let body = read_body(response.body, max_response_body_size)?;
            return Err(api_error(status, body));
        }
        Ok(ApiStream::new(
            response.status,
            response.headers,
            response.body,
        ))
    }

    pub fn create_response(
        &mut self,
        request: &CreateResponseRequest,
    ) -> Result<ApiResponse<ResponseObject>, Error<T::Error>> {
        self.post_json("responses", request)
    }

    pub fn create_response_stream<'a>(
        &'a mut self,
        request: &mut CreateResponseRequest,
    ) -> Result<ApiStream<HttpResponseBody<T::Socket<'a>>>, Error<T::Error>> {
        self.post_json_stream("responses", request)
    }

    pub fn retrieve_response(
        &mut self,
        response_id: &str,
    ) -> Result<ApiResponse<ResponseObject>, Error<T::Error>> {
        self.get_json(&format!("responses/{}", encode_path_segment(response_id)))
    }

    pub fn delete_response(
        &mut self,
        response_id: &str,
    ) -> Result<ApiResponse<DeletionStatus>, Error<T::Error>> {
        self.delete_json(&format!("responses/{}", encode_path_segment(response_id)))
    }

    pub fn cancel_response(
        &mut self,
        response_id: &str,
    ) -> Result<ApiResponse<ResponseObject>, Error<T::Error>> {
        self.post_json(
            &format!("responses/{}/cancel", encode_path_segment(response_id)),
            &serde_json::json!({}),
        )
    }

    pub fn count_response_input_tokens(
        &mut self,
        request: &CountTokensRequest,
    ) -> Result<ApiResponse<CountTokensResponse>, Error<T::Error>> {
        self.post_json("responses/input_tokens", request)
    }

    pub fn chat_completion(
        &mut self,
        request: &ChatCompletionRequest<'_>,
    ) -> Result<ApiResponse<ChatCompletionResponse>, Error<T::Error>> {
        self.post_json("chat/completions", request)
    }

    pub fn chat_completion_stream<'a>(
        &'a mut self,
        request: &mut ChatCompletionRequest<'_>,
    ) -> Result<ApiStream<HttpResponseBody<T::Socket<'a>>>, Error<T::Error>> {
        self.post_json_stream("chat/completions", request)
    }

    pub fn create_embedding(
        &mut self,
        request: &EmbeddingRequest,
    ) -> Result<ApiResponse<EmbeddingResponse>, Error<T::Error>> {
        self.post_json("embeddings", request)
    }

    pub fn list_models(&mut self) -> Result<ApiResponse<ModelList>, Error<T::Error>> {
        self.get_json("models")
    }

    pub fn retrieve_model(
        &mut self,
        model_id: &str,
    ) -> Result<ApiResponse<Model>, Error<T::Error>> {
        self.get_json(&format!("models/{}", encode_path_segment(model_id)))
    }

    fn send_buffered(
        &mut self,
        method: Method,
        path: &str,
        body: &[u8],
        is_json: bool,
    ) -> Result<ApiResponse<Vec<u8>>, Error<T::Error>> {
        self.send_buffered_with_content_type(
            method,
            path,
            body,
            is_json.then_some("application/json"),
        )
    }

    fn send_buffered_with_content_type(
        &mut self,
        method: Method,
        path: &str,
        body: &[u8],
        content_type: Option<&str>,
    ) -> Result<ApiResponse<Vec<u8>>, Error<T::Error>> {
        let max_response_body_size = self.max_response_body_size;
        let body_len = (method == Method::Post || content_type.is_some() || !body.is_empty())
            .then_some(body.len());
        let response = self.send_http(method, path, content_type, false, body_len, |socket| {
            socket
                .write_all(body)
                .map_err(|error| Error::Http(HttpError::Transport(error)))
        })?;
        let status = response.status;
        let headers = response.headers;
        let body = read_body(response.body, max_response_body_size)?;
        if !(200..300).contains(&status) {
            return Err(api_error(status, body));
        }
        Ok(ApiResponse {
            status,
            headers,
            data: body,
        })
    }

    fn send_json<'a, Q>(
        &'a mut self,
        method: Method,
        path: &str,
        request: &Q,
        stream: bool,
    ) -> Result<Response<HttpResponseBody<T::Socket<'a>>>, Error<T::Error>>
    where
        Q: Serialize + ?Sized,
    {
        let body_len = json_body_len(request)?;
        self.send_http(
            method,
            path,
            Some("application/json"),
            stream,
            Some(body_len),
            |socket| write_json(socket, request),
        )
    }

    fn send_http<'a, F>(
        &'a mut self,
        method: Method,
        path: &str,
        content_type: Option<&str>,
        stream: bool,
        body_len: Option<usize>,
        write_body: F,
    ) -> Result<Response<HttpResponseBody<T::Socket<'a>>>, Error<T::Error>>
    where
        F: FnOnce(&mut T::Socket<'a>) -> Result<(), Error<T::Error>>,
    {
        if contains_line_break(path) {
            return Err(Error::InvalidPath);
        }
        let path = path.trim_start_matches('/');
        let Client {
            transport,
            endpoint,
            api_key,
            organization,
            project,
            headers,
            host_header,
            max_response_header_size,
            ..
        } = self;
        let socket = transport
            .connect(endpoint.host.as_str(), endpoint.port, endpoint.scheme)
            .map_err(|error| Error::Http(HttpError::Transport(error)))?;
        let request = Request {
            method,
            base_path: endpoint.base_path.as_str(),
            path,
            host: host_header
                .as_deref()
                .unwrap_or(endpoint.authority.as_str()),
            headers,
            accept: if stream {
                "text/event-stream"
            } else {
                "application/json"
            },
            content_type,
            bearer_token: api_key.as_deref(),
            organization: organization.as_deref(),
            project: project.as_deref(),
            body_len,
        };
        match http::send_request_with_body(socket, request, *max_response_header_size, write_body) {
            Ok(response) => Ok(response),
            Err(http::SendRequestError::Http(error)) => Err(Error::Http(error)),
            Err(http::SendRequestError::Body(error)) => Err(error),
        }
    }
}

fn json_body_len<Q: Serialize + ?Sized, E>(request: &Q) -> Result<usize, Error<E>> {
    let mut writer = CountingWriter::default();
    serde_json::to_writer(&mut writer, request).map_err(Error::Serialize)?;
    if writer.overflowed {
        return Err(Error::Serialize(
            <serde_json::Error as serde::ser::Error>::custom("request JSON exceeds usize"),
        ));
    }
    Ok(writer.len)
}

fn write_json<S, Q, E>(socket: &mut S, request: &Q) -> Result<(), Error<E>>
where
    S: embedded_io::Write<Error = E>,
    Q: Serialize + ?Sized,
{
    let mut writer = JsonSocketWriter::new(socket);
    let serialization = serde_json::to_writer(&mut writer, request);
    if let Some(error) = writer.error {
        return Err(Error::Http(HttpError::Transport(error)));
    }
    serialization.map_err(Error::Serialize)
}

#[derive(Default)]
struct CountingWriter {
    len: usize,
    overflowed: bool,
}

impl std::io::Write for CountingWriter {
    fn write(&mut self, buffer: &[u8]) -> std::io::Result<usize> {
        match self.len.checked_add(buffer.len()) {
            Some(len) => self.len = len,
            None => self.overflowed = true,
        }
        Ok(buffer.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

struct JsonSocketWriter<'a, S: embedded_io::Write> {
    socket: &'a mut S,
    error: Option<S::Error>,
}

impl<'a, S: embedded_io::Write> JsonSocketWriter<'a, S> {
    fn new(socket: &'a mut S) -> Self {
        Self {
            socket,
            error: None,
        }
    }
}

impl<S: embedded_io::Write> std::io::Write for JsonSocketWriter<'_, S> {
    fn write(&mut self, buffer: &[u8]) -> std::io::Result<usize> {
        if self.error.is_none() {
            if let Err(error) = self.socket.write_all(buffer) {
                self.error = Some(error);
            }
        }
        Ok(buffer.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn read_body<B, E>(mut body: B, limit: usize) -> Result<Vec<u8>, Error<E>>
where
    B: HttpBody<Error = HttpError<E>>,
{
    let mut output = Vec::new();
    let mut chunk = [0u8; READ_BUFFER_SIZE];
    let mut next_milestone = 4096usize;
    loop {
        let count = body.read(&mut chunk).map_err(Error::Http)?;
        if count == 0 {
            println!("[http] body complete: {} bytes", output.len());
            return Ok(output);
        }
        if output.len().saturating_add(count) > limit {
            return Err(Error::ResponseTooLarge { limit });
        }
        output.extend_from_slice(&chunk[..count]);
        if output.len() >= next_milestone {
            println!("[http] body: {} bytes received...", output.len());
            next_milestone = output.len() + 4096;
        }
    }
}

fn decode_json<T, B, E>(response: Response<B>, limit: usize) -> Result<ApiResponse<T>, Error<E>>
where
    T: DeserializeOwned,
    B: HttpBody<Error = HttpError<E>>,
{
    let Response {
        status,
        headers,
        body,
    } = response;
    let mut reader = JsonBodyReader::new(body, limit);
    let data = serde_json::from_reader(&mut reader);
    if let Some(error) = reader.error.take() {
        return Err(Error::Http(error));
    }
    if reader.exceeded_limit {
        return Err(Error::ResponseTooLarge { limit });
    }
    match data {
        Ok(data) => Ok(ApiResponse {
            status,
            headers,
            data,
        }),
        Err(source) => Err(Error::Deserialize {
            source,
            body_len: reader.body_len,
        }),
    }
}

struct JsonBodyReader<B: HttpBody> {
    body: B,
    limit: usize,
    body_len: usize,
    error: Option<B::Error>,
    exceeded_limit: bool,
}

impl<B: HttpBody> JsonBodyReader<B> {
    fn new(body: B, limit: usize) -> Self {
        Self {
            body,
            limit,
            body_len: 0,
            error: None,
            exceeded_limit: false,
        }
    }
}

impl<B: HttpBody> std::io::Read for JsonBodyReader<B> {
    fn read(&mut self, buffer: &mut [u8]) -> std::io::Result<usize> {
        if buffer.is_empty() || self.error.is_some() || self.exceeded_limit {
            return Ok(0);
        }
        if self.body_len == self.limit {
            let mut byte = [0u8; 1];
            match self.body.read(&mut byte) {
                Ok(0) => return Ok(0),
                Ok(_) => {
                    self.exceeded_limit = true;
                    return Ok(0);
                }
                Err(error) => {
                    self.error = Some(error);
                    return Ok(0);
                }
            }
        }

        let max = (self.limit - self.body_len).min(buffer.len());
        match self.body.read(&mut buffer[..max]) {
            Ok(count) => {
                self.body_len += count;
                Ok(count)
            }
            Err(error) => {
                self.error = Some(error);
                Ok(0)
            }
        }
    }
}

fn api_error<E>(status: u16, body: Vec<u8>) -> Error<E> {
    let error = serde_json::from_slice::<ApiErrorEnvelope>(&body)
        .ok()
        .map(|envelope| envelope.error);
    Error::Api {
        status,
        error,
        body,
    }
}

fn parse_authority(authority: &str, default_port: u16) -> Result<(String, u16), ConfigError> {
    if authority.starts_with('[') {
        let end = authority.find(']').ok_or(ConfigError::InvalidEndpoint)?;
        let host = &authority[1..end];
        let suffix = &authority[end + 1..];
        let port = if suffix.is_empty() {
            default_port
        } else {
            suffix
                .strip_prefix(':')
                .ok_or(ConfigError::InvalidEndpoint)?
                .parse()
                .map_err(|_| ConfigError::InvalidEndpoint)?
        };
        if host.is_empty() {
            return Err(ConfigError::InvalidEndpoint);
        }
        return Ok((String::from(host), port));
    }

    let (host, port) = match authority.rsplit_once(':') {
        Some((host, port)) if !host.contains(':') => (
            host,
            port.parse().map_err(|_| ConfigError::InvalidEndpoint)?,
        ),
        _ => (authority, default_port),
    };
    if host.is_empty() || host.bytes().any(|byte| byte.is_ascii_whitespace()) {
        return Err(ConfigError::InvalidEndpoint);
    }
    Ok((String::from(host), port))
}

fn validate_header(header: &Header) -> Result<(), ConfigError> {
    validate_header_value(&header.name, &header.value)
}

fn validate_header_value(name: &str, value: &str) -> Result<(), ConfigError> {
    if name.is_empty()
        || !name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
    {
        return Err(ConfigError::InvalidHeaderName(String::from(name)));
    }
    if contains_line_break(value) {
        return Err(ConfigError::InvalidHeaderValue(String::from(name)));
    }
    Ok(())
}

fn contains_line_break(value: &str) -> bool {
    value.bytes().any(|byte| byte == b'\r' || byte == b'\n')
}

fn upsert_header(headers: &mut Vec<Header>, new_header: Header) {
    if let Some(header) = headers
        .iter_mut()
        .find(|header| header.is_name(&new_header.name))
    {
        *header = new_header;
    } else {
        headers.push(new_header);
    }
}

fn encode_path_segment(segment: &str) -> String {
    let mut encoded = String::new();
    for byte in segment.bytes() {
        if byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'.' | b'_' | b'~') {
            encoded.push(char::from(byte));
        } else {
            let _ = write!(&mut encoded, "%{byte:02X}");
        }
    }
    encoded
}
