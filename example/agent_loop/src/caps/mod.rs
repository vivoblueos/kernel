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

mod led;

use std::error::Error;

use crate::caps::led::LedCaps;
use crate::caps::led::LedProgramArgs;
use serde::Deserialize;
use serde_json::{json, Value};

const CAPABILITIES_JSON_LEN: usize = include_bytes!("../../capabilities.json").len();

#[used]
#[unsafe(link_section = ".agent_capabilities")]
pub static CAPABILITIES_JSON: [u8; CAPABILITIES_JSON_LEN] =
    *include_bytes!("../../capabilities.json");

#[derive(Debug, Deserialize)]
pub struct CapabilitiesFile {
    capabilities: Vec<CapabilityDefinition>,
}

#[derive(Debug, Deserialize)]
pub struct CapabilityDefinition {
    name: String,
    description: String,
    handler: String,
    parameters: Value,
}

#[derive(Clone, Copy)]
pub enum CapabilityHandler {
    LedProgram,
}

impl CapabilityHandler {
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "led_program" => Some(Self::LedProgram),
            _ => None,
        }
    }
}

pub struct CapabilityRegistry {
    pub tools: Vec<Value>,
    handlers: Vec<CapabilityHandler>,
}

impl CapabilityRegistry {
    pub fn load() -> Result<Self, Box<dyn Error>> {
        let caps: CapabilitiesFile = serde_json::from_slice(&CAPABILITIES_JSON)?;
        let capability_count = caps.capabilities.len();
        let mut handlers = Vec::with_capacity(capability_count);
        let mut tools: Vec<Value> = Vec::with_capacity(capability_count);

        for capability in caps.capabilities {
            if tools
                .iter()
                .any(|tool| tool_name(tool) == Some(capability.name.as_str()))
            {
                return Err(format!("duplicate capability name: {}", capability.name).into());
            }
            let handler = CapabilityHandler::from_name(&capability.handler)
                .ok_or_else(|| format!("unknown handler: {}", capability.handler))?;
            handlers.push(handler);
            tools.push(json!({
                "type": "function",
                "function": {
                    "name": capability.name,
                    "description": capability.description,
                    "parameters": capability.parameters,
                },
            }));
        }

        Ok(Self { tools, handlers })
    }

    pub fn execute(&self, name: &str, arguments: &str) -> Value {
        let Some(handler) = self
            .tools
            .iter()
            .zip(&self.handlers)
            .find_map(|(tool, handler)| (tool_name(tool) == Some(name)).then_some(*handler))
        else {
            return error_result(
                "unknown_capability",
                format!("capability '{name}' is not registered"),
            );
        };

        match handler {
            CapabilityHandler::LedProgram => {
                // Ok(())
                // todo!()
                LedCaps::new().run_program(serde_json::from_str(arguments).unwrap_or_else(|_| {
                    LedProgramArgs::Steps {
                        steps: vec![],
                        repeat: Some(1),
                    }
                }))
            }
        }
    }
}

fn tool_name(tool: &Value) -> Option<&str> {
    tool.get("function")?.get("name")?.as_str()
}

pub fn error_result(code: &str, message: String) -> Value {
    json!({
        "ok": false,
        "code": code,
        "message": message
    })
}
