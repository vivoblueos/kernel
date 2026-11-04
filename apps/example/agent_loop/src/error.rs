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
use core::fmt;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::http::HttpError;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct ApiError {
    pub message: String,
    #[serde(rename = "type", default)]
    pub kind: Option<String>,
    #[serde(default)]
    pub param: Option<Value>,
    #[serde(default)]
    pub code: Option<Value>,
}

#[derive(Debug, Deserialize)]
pub(crate) struct ApiErrorEnvelope {
    pub error: ApiError,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConfigError {
    EmptyEndpoint,
    InvalidEndpoint,
    InvalidApiKey,
    InvalidHeaderName(String),
    InvalidHeaderValue(String),
}

impl fmt::Display for ConfigError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyEndpoint => f.write_str("API endpoint cannot be empty"),
            Self::InvalidEndpoint => f.write_str("API endpoint contains an invalid character"),
            Self::InvalidApiKey => f.write_str("API key contains an invalid character"),
            Self::InvalidHeaderName(name) => write!(f, "invalid HTTP header name: {name}"),
            Self::InvalidHeaderValue(name) => {
                write!(f, "HTTP header {name} contains an invalid value")
            }
        }
    }
}

#[derive(Debug)]
pub enum Error<E> {
    Http(HttpError<E>),
    Serialize(serde_json::Error),
    Deserialize {
        source: serde_json::Error,
        body_len: usize,
    },
    Api {
        status: u16,
        error: Option<ApiError>,
        body: Vec<u8>,
    },
    ResponseTooLarge {
        limit: usize,
    },
    InvalidPath,
}

impl<E: fmt::Display> fmt::Display for Error<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Http(error) => write!(f, "HTTP error: {error}"),
            Self::Serialize(error) => write!(f, "failed to serialize request JSON: {error}"),
            Self::Deserialize { source, .. } => {
                write!(f, "failed to deserialize response JSON: {source}")
            }
            Self::Api {
                status,
                error: Some(error),
                ..
            } => write!(f, "OpenAI API returned HTTP {status}: {}", error.message),
            Self::Api {
                status,
                error: None,
                body,
            } => match core::str::from_utf8(body) {
                Ok(body) if !body.is_empty() => {
                    write!(f, "OpenAI API returned HTTP {status}: {body}")
                }
                _ => write!(f, "OpenAI API returned HTTP {status}"),
            },
            Self::ResponseTooLarge { limit } => {
                write!(
                    f,
                    "response body exceeded the configured {limit}-byte limit"
                )
            }
            Self::InvalidPath => f.write_str("request path contains an invalid character"),
        }
    }
}

impl std::error::Error for ConfigError {}

impl<E> std::error::Error for Error<E> where E: std::error::Error + 'static {}
