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

extern crate alloc;
extern crate esp_radio_sys;
extern crate librs;
extern crate rsrt;

mod agent_loop;
mod api;
mod caps;
mod client;
mod error;
mod http;
mod sse;
mod tls;
mod wifi;

use alloc::string::ToString;
use std::{env, io::Write as _, print, thread};

use api::chat::{ChatCompletionRequest, ChatContent, ChatMessage};
use tls::EmbeddedTlsTransport;

use crate::{agent_loop::AgentSession, caps::CapabilityRegistry};

fn main() -> std::io::Result<()> {
    println!("Hello, agent_loop!");
    wifi::connect_wifi();
    main_loop();
    Ok(())
}

fn main_loop() {
    let api_key = env::var("OPENAI_API_KEY").expect("Please set OPENAI_API_KEY");
    let endpoint =
        env::var("OPENAI_API_BASE").unwrap_or_else(|_| String::from("https://14.116.174.67"));
    let model = env::var("OPENAI_MODEL").unwrap_or_else(|_| String::from("deepseek-chat"));

    let registry = CapabilityRegistry::load().unwrap();

    let mut client =
        match client::Client::builder(EmbeddedTlsTransport::new().with_sni("api.deepseek.com"))
            .with_endpoint(endpoint)
            .with_host_header("api.deepseek.com")
            .with_api_key(api_key)
            .with_max_response_body_size(100 * 1024)
            .build()
        {
            Ok(c) => c,
            Err(e) => {
                eprintln!("client build failed: {e}");
                return;
            }
        };

    let mut session = AgentSession::new(true);

    loop {
        print!("you> ");
        let _ = std::io::stdout().flush();

        let mut input = String::new();
        if std::io::stdin().read_line(&mut input).unwrap_or(0) == 0 {
            break;
        }
        let input = input.trim();
        if input == "/quit" || input == "/exit" {
            break;
        }
        if input.is_empty() {
            continue;
        }

        match session.run_turn(&mut client, &model, &registry, input) {
            Ok(reply) => println!("assistant> {reply}"),
            Err(error) => eprintln!("request failed: {error}"),
        }
    }
}
