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

use embedded_io::Error;
use serde_json::Value;
use std::{fmt, println};

use crate::{
    api::chat::{
        ChatCompletionRequest, ChatContent, ChatMessage, MessageRole, ToolChoice, ToolChoiceMode,
    },
    caps::CapabilityRegistry,
    client::Client,
    tls::{AgentError, EmbeddedTlsTransport},
};

/// A simple monotonic clock using librs::clock_gettime with CLOCK_MONOTONIC.
///
/// This replaces std::time::Instant because the Rust std library's Instant::now()
/// calls libc::clock_gettime() with CLOCK_MONOTONIC=4 (from the newlib libc crate),
/// but the BlueOS kernel expects CLOCK_MONOTONIC=1, causing EINVAL.
struct BlueInstant {
    ns: i64,
}

impl BlueInstant {
    fn now() -> Self {
        let mut ts = libc::timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        // Use the correct CLOCK_MONOTONIC=1 that the BlueOS kernel understands.
        const CLOCK_MONOTONIC: libc::clockid_t = 1;
        let ret =
            unsafe { librs::time::clock_gettime(CLOCK_MONOTONIC, &mut ts as *mut libc::timespec) };
        assert_eq!(ret, 0, "clock_gettime(CLOCK_MONOTONIC) failed");
        Self {
            ns: ts.tv_sec as i64 * 1_000_000_000 + ts.tv_nsec as i64,
        }
    }

    fn elapsed(&self) -> core::time::Duration {
        let now = Self::now();
        let diff = now.ns - self.ns;
        core::time::Duration::from_nanos(diff as u64)
    }
}

const MAX_TOOL_ROUNDS: usize = 8;
const MAX_REASONING_SNIPPET_BYTES: usize = 150;
const MAX_HISTORY_MESSAGES: usize = 24;

pub enum AgentLoopError {
    IoError,
    Api(crate::error::Error<AgentError>),
    InvalidResponse,
}

impl fmt::Display for AgentLoopError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IoError => f.write_str("agent I/O error"),
            Self::Api(error) => write!(f, "{error}"),
            Self::InvalidResponse => f.write_str("model returned an invalid response"),
        }
    }
}

pub struct AgentSession {
    /// Whether to prefer using /v1/chat/completions instead of /v1/responses the newer one
    prefer_chat_completions: bool,
    messages: Vec<ChatMessage>,
}

impl AgentSession {
    pub fn new(prefer_chat_completions: bool) -> Self {
        Self {
            prefer_chat_completions,
            messages: Vec::new(),
        }
    }

    pub fn run_turn<'a>(
        &'a mut self,
        client: &mut Client<EmbeddedTlsTransport>,
        model: &str,
        registry: &CapabilityRegistry,
        prompt: &str,
    ) -> Result<&'a str, AgentLoopError> {
        if self.prefer_chat_completions {
            self.run_turn_with_chat(client, model, registry, prompt)
        } else {
            todo!("Implement run_turn_with_responses for /v1/responses endpoint");
        }
    }

    fn run_turn_with_chat<'a>(
        &'a mut self,
        client: &mut Client<EmbeddedTlsTransport>,
        model: &str,
        registry: &CapabilityRegistry,
        prompt: &str,
    ) -> Result<&'a str, AgentLoopError> {
        self.messages.push(ChatMessage::user(prompt));

        for round in 1..=MAX_TOOL_ROUNDS {
            let mut request = ChatCompletionRequest::new(model, self.messages.as_slice());
            request.tools = Some(registry.tools.as_slice());
            request.tool_choice = Some(ToolChoice::Mode(ToolChoiceMode::Auto));
            request.parallel_tool_calls = Some(false);

            let response = match client.chat_completion(&request) {
                Ok(response) => response.data,
                Err(error) => {
                    if is_not_found_error(&error) {
                        return Err(AgentLoopError::InvalidResponse);
                    }
                    return Err(AgentLoopError::Api(error));
                }
            };
            let message = response
                .choices
                .into_iter()
                .next()
                .ok_or(AgentLoopError::InvalidResponse)?
                .message;

            if let Some(tool_calls) = message.tool_calls {
                if !tool_calls.is_empty() {
                    if let Some((snippet, truncated)) = message
                        .reasoning_content
                        .as_deref()
                        .and_then(reasoning_snippet)
                    {
                        if truncated {
                            println!("🦞 [Round {round}] {snippet}...");
                        } else {
                            println!("🦞 [Round {round}] {snippet}");
                        }
                    }

                    let mut assistant_message = ChatMessage::assistant("");
                    assistant_message.content = message.content.map(Into::into);
                    let tool_call_count = tool_calls.len();
                    assistant_message.tool_calls = Some(tool_calls);
                    let assistant_message_index = self.messages.len();
                    self.messages.push(assistant_message);

                    for tool_call_index in 0..tool_call_count {
                        let (tool_call_id, output) = {
                            let tool_call = &self.messages[assistant_message_index]
                                .tool_calls
                                .as_ref()
                                .expect("assistant tool calls must be present")[tool_call_index];
                            let result = execute_tool_call(
                                registry,
                                &tool_call.function.name,
                                &tool_call.function.arguments,
                            );
                            let output = serde_json::to_string(&result)
                                .map_err(|_| AgentLoopError::IoError)?;
                            (tool_call.id.clone(), output)
                        };
                        self.messages.push(ChatMessage::tool(tool_call_id, output));
                    }
                    continue;
                }
            }

            if let Some(reply) = message.content {
                if !reply.is_empty() {
                    self.messages.push(ChatMessage::assistant(reply));
                    self.trim_history();
                    return match self
                        .messages
                        .last()
                        .and_then(|message| message.content.as_ref())
                    {
                        Some(ChatContent::Text(reply)) => Ok(reply),
                        _ => unreachable!("assistant reply must be text"),
                    };
                }
            }

            return Err(AgentLoopError::IoError);
        }

        Err(AgentLoopError::IoError)
    }

    fn trim_history(&mut self) {
        while self.messages.len() > MAX_HISTORY_MESSAGES {
            let Some(next_turn_start) = self
                .messages
                .iter()
                .enumerate()
                .skip(1)
                .find_map(|(index, message)| (message.role == MessageRole::User).then_some(index))
            else {
                break;
            };
            self.messages.drain(..next_turn_start);
        }
    }
}

fn is_not_found_error(error: &crate::error::Error<AgentError>) -> bool {
    matches!(error, crate::error::Error::Api { status: 404, .. })
}

fn reasoning_snippet(reasoning: &str) -> Option<(&str, bool)> {
    let reasoning = reasoning.trim();
    if reasoning.is_empty() {
        return None;
    }

    let mut end = reasoning.len().min(MAX_REASONING_SNIPPET_BYTES);
    while !reasoning.is_char_boundary(end) {
        end -= 1;
    }
    Some((&reasoning[..end], end < reasoning.len()))
}

fn execute_tool_call(registry: &CapabilityRegistry, name: &str, arguments: &str) -> Value {
    println!("tool> {name} args={arguments}");
    let started_at = BlueInstant::now();
    let result = registry.execute(name, arguments);
    let elapsed_ms = started_at.elapsed().as_millis();
    let code = result.get("code").and_then(Value::as_str).unwrap_or("ok");
    println!("tool< {name} code={code} elapsed_ms={elapsed_ms} result={result}");
    result
}
