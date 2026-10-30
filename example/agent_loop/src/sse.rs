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
use core::{fmt, str};
use serde::de::DeserializeOwned;

use crate::http::{Header, HttpBody};

const DEFAULT_MAX_EVENT_SIZE: usize = 64 * 1024;
const READ_BUFFER_SIZE: usize = 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SseEvent {
    pub event: Option<String>,
    pub data: String,
    pub id: Option<String>,
    pub retry: Option<u64>,
}

#[derive(Debug)]
pub enum SseJson<T> {
    Data { event: Option<String>, data: T },
    Done,
}

#[derive(Debug)]
pub enum StreamError<E> {
    Transport(E),
    InvalidUtf8,
    InvalidJson(serde_json::Error),
    EventTooLarge { limit: usize },
}

impl<E: fmt::Display> fmt::Display for StreamError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Transport(error) => write!(f, "transport error while reading stream: {error}"),
            Self::InvalidUtf8 => f.write_str("SSE stream contained invalid UTF-8"),
            Self::InvalidJson(error) => write!(f, "SSE event contained invalid JSON: {error}"),
            Self::EventTooLarge { limit } => {
                write!(f, "SSE event exceeded the configured {limit}-byte limit")
            }
        }
    }
}

#[cfg(feature = "std")]
impl<E> std::error::Error for StreamError<E> where E: std::error::Error + 'static {}

#[derive(Debug)]
pub struct ApiStream<B> {
    pub status: u16,
    pub headers: Vec<Header>,
    events: SseStream<B>,
}

impl<B> ApiStream<B> {
    pub(crate) fn new(status: u16, headers: Vec<Header>, body: B) -> Self {
        Self {
            status,
            headers,
            events: SseStream::new(body),
        }
    }

    pub fn events_mut(&mut self) -> &mut SseStream<B> {
        &mut self.events
    }

    pub fn into_events(self) -> SseStream<B> {
        self.events
    }
}

impl<B: HttpBody> ApiStream<B> {
    pub fn next_event(&mut self) -> Result<Option<SseEvent>, StreamError<B::Error>> {
        self.events.next_event()
    }

    pub fn next_json<T>(&mut self) -> Result<Option<SseJson<T>>, StreamError<B::Error>>
    where
        T: DeserializeOwned,
    {
        self.events.next_json()
    }
}

#[derive(Debug)]
pub struct SseStream<B> {
    body: B,
    buffer: Vec<u8>,
    eof: bool,
    max_event_size: usize,
}

impl<B> SseStream<B> {
    pub fn new(body: B) -> Self {
        Self {
            body,
            buffer: Vec::new(),
            eof: false,
            max_event_size: DEFAULT_MAX_EVENT_SIZE,
        }
    }

    pub fn with_max_event_size(mut self, max_event_size: usize) -> Self {
        self.max_event_size = max_event_size;
        self
    }

    pub fn into_inner(self) -> B {
        self.body
    }
}

impl<B: HttpBody> SseStream<B> {
    pub fn next_event(&mut self) -> Result<Option<SseEvent>, StreamError<B::Error>> {
        loop {
            if let Some((index, delimiter_len)) = find_delimiter(&self.buffer) {
                if index > self.max_event_size {
                    return Err(StreamError::EventTooLarge {
                        limit: self.max_event_size,
                    });
                }
                let event = parse_event(&self.buffer[..index])?;
                self.buffer.drain(..index + delimiter_len);
                if let Some(event) = event {
                    return Ok(Some(event));
                }
                continue;
            }

            if self.eof {
                if self.buffer.is_empty() {
                    return Ok(None);
                }
                if self.buffer.len() > self.max_event_size {
                    return Err(StreamError::EventTooLarge {
                        limit: self.max_event_size,
                    });
                }

                let event = core::mem::take(&mut self.buffer);
                return parse_event(&event);
            }

            if self.buffer.len() > self.max_event_size {
                return Err(StreamError::EventTooLarge {
                    limit: self.max_event_size,
                });
            }

            let mut chunk = [0u8; READ_BUFFER_SIZE];
            let count = self.body.read(&mut chunk).map_err(StreamError::Transport)?;
            if count == 0 {
                self.eof = true;
            } else {
                self.buffer.extend_from_slice(&chunk[..count]);
            }
        }
    }

    pub fn next_json<T>(&mut self) -> Result<Option<SseJson<T>>, StreamError<B::Error>>
    where
        T: DeserializeOwned,
    {
        let Some(event) = self.next_event()? else {
            return Ok(None);
        };

        if event.data.trim() == "[DONE]" {
            return Ok(Some(SseJson::Done));
        }

        let data = serde_json::from_str(&event.data).map_err(StreamError::InvalidJson)?;
        Ok(Some(SseJson::Data {
            event: event.event,
            data,
        }))
    }
}

fn find_delimiter(buffer: &[u8]) -> Option<(usize, usize)> {
    let mut index = 0;
    while index + 1 < buffer.len() {
        if buffer[index] == b'\n' && buffer[index + 1] == b'\n' {
            return Some((index, 2));
        }
        if index + 3 < buffer.len() && &buffer[index..index + 4] == b"\r\n\r\n" {
            return Some((index, 4));
        }
        index += 1;
    }
    None
}

fn parse_event<E>(bytes: &[u8]) -> Result<Option<SseEvent>, StreamError<E>> {
    let text = str::from_utf8(bytes).map_err(|_| StreamError::InvalidUtf8)?;
    let mut event = None;
    let mut data = String::new();
    let mut id = None;
    let mut retry = None;

    for raw_line in text.split('\n') {
        let line = raw_line.strip_suffix('\r').unwrap_or(raw_line);
        if line.is_empty() || line.starts_with(':') {
            continue;
        }

        let (field, value) = match line.split_once(':') {
            Some((field, value)) => (field, value.strip_prefix(' ').unwrap_or(value)),
            None => (line, ""),
        };

        match field {
            "event" => event = Some(String::from(value)),
            "data" => {
                if !data.is_empty() {
                    data.push('\n');
                }
                data.push_str(value);
            }
            "id" => id = Some(String::from(value)),
            "retry" => retry = value.parse().ok(),
            _ => {}
        }
    }

    if event.is_none() && data.is_empty() && id.is_none() && retry.is_none() {
        return Ok(None);
    }

    Ok(Some(SseEvent {
        event,
        data,
        id,
        retry,
    }))
}
