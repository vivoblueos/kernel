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

pub fn command(args: &[&str]) -> Result<(), String> {
    if args.is_empty() {
        return Err("Usage: printf string<%s, %d, %f> [arg...]".to_string());
    }
    let full_input = args.join(" ");
    let (format_str, arguments) = split_format_and_args(&full_input)?;
    match format_string(&format_str, arguments.as_slice()) {
        Ok(s) => println!("Formatted: {}", s),
        Err(e) => println!("Error: {}", e),
    }
    Ok(())
}

fn split_format_and_args(input: &str) -> Result<(String, Vec<String>), String> {
    let mut chars = input.chars();
    let mut format_str = String::new();
    let mut arguments = String::new();
    let mut in_quotes = false;
    let mut args = false;
    for c in chars {
        match c {
            '"' if !in_quotes && !args => {
                in_quotes = true;
            }
            '"' if in_quotes && !args => {
                args = true;
            }
            _ if in_quotes && !args => format_str.push(c),
            _ if args => arguments.push(c),
            _ => {}
        }
    }
    let args_vec: Vec<String> = arguments
        .split_whitespace()
        .map(|s| s.to_string())
        .collect();
    Ok((format_str, args_vec))
}

fn format_string(format_str: &str, arguments: &[String]) -> Result<String, String> {
    let mut result = String::new();
    let mut arg_index = 0;
    let mut chars = format_str.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '%' {
            let specifier = chars.next().ok_or("Incomplete format specifier")?;
            if arg_index >= arguments.len() {
                return Err(format!("Missing argument for %{}", specifier));
            }

            match specifier {
                'd' | 'i' => {
                    if arguments[arg_index].parse::<i64>().is_err() {
                        return Err(format!(
                            "Expected integer for %{}, got '{}'",
                            specifier, arguments[arg_index]
                        ));
                    }
                    result.push_str(&arguments[arg_index]);
                }
                'f' => {
                    if arguments[arg_index].parse::<f64>().is_err() {
                        return Err(format!(
                            "Expected float for %{}, got '{}'",
                            specifier, arguments[arg_index]
                        ));
                    }
                    result.push_str(&arguments[arg_index]);
                }
                's' => result.push_str(&arguments[arg_index]),
                '%' => result.push('%'),
                _ => return Err(format!("Unsupported format specifier: %{}", specifier)),
            }
            arg_index += 1;
        } else {
            result.push(c);
        }
    }

    if arg_index < arguments.len() {
        return Err(format!(
            "Too many arguments: expected {}, got {}",
            arg_index,
            arguments.len()
        ));
    }

    Ok(result)
}
