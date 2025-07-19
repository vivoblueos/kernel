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

extern crate librs;
extern crate rsrt;

use std::io::{Read, Write};
use std::net::TcpStream;

fn main() -> std::io::Result<()> {
    let server_addr = "10.58.54.123:3000";
    println!("\n=== Net Tcp Stream Example Enter ===");

    match TcpStream::connect(server_addr) {
        Ok(mut stream) => {
            println!("Connect Server success");

            if let Err(e) = stream.write_all(b"Hello, Server! from net app") {
                println!("send fail: {}", e);
            } else {
                println!("send success ");
                let mut buffer = [0; 1024];
                match stream.read(&mut buffer) {
                    Ok(size) => {
                        let response = String::from_utf8_lossy(&buffer[..size]);
                        println!("recv msg from server : {}", response);
                    }
                    Err(e) => println!("recv fail: {}", e),
                }
            }
        }
        Err(e) => println!("connect fail: {}", e),
    }

    println!("\n=== Net Tcp Stream Example Exit ===");
    Ok(())
}
