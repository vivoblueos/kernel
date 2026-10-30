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

use serde::Deserialize;
use serde_json::{json, Value};
use std::fs::{File, OpenOptions};
use std::io::Write as _;

use crate::caps::error_result;

const DEFAULT_MORSE_UNIT_MS: u64 = 200;

/// Character-device paths exposed by `boards/seeed_xiao_esp32c3::init_gpio`.
const LED_BLUE_DEVICE: &str = "/dev/led_b";
const LED_RED_DEVICE: &str = "/dev/led_r";

/// The board drives both LED GPIOs to `High` while registering them (see
/// `boards/seeed_xiao_esp32c3/mod.rs::init_gpio`), which we treat as the
/// inactive state. The LEDs are therefore active-low: writing `0` lights the
/// LED and `1` turns it off. Flip these two constants for an active-high board.
const LED_ON: &[u8] = b"1";
const LED_OFF: &[u8] = b"0";

#[derive(Debug, Deserialize)]
pub struct LedStep {
    state: String,
    #[serde(default)]
    color: Option<String>,
    #[serde(default)]
    hold_ms: Option<u64>,
}

#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum LedProgramArgs {
    Steps {
        steps: Vec<LedStep>,
        #[serde(default)]
        repeat: Option<u32>,
    },
    Morse {
        text: String,
        #[serde(default)]
        unit_ms: Option<u64>,
        #[serde(default)]
        repeat: Option<u32>,
    },
}

/// Handle over the two physical LED channels.
///
/// Both fields are `None` when the character devices cannot be opened (e.g. the
/// kernel did not register them). In that case the program runs in a simulated
/// mode that still tracks and reports state, but does not touch hardware.
struct LedChannels {
    blue: Option<File>,
    red: Option<File>,
}

impl LedChannels {
    fn open() -> Self {
        let blue = OpenOptions::new().write(true).open(LED_BLUE_DEVICE).ok();
        let red = OpenOptions::new().write(true).open(LED_RED_DEVICE).ok();
        Self { blue, red }
    }

    /// True when at least one physical LED is driven by this handle.
    fn is_hardware(&self) -> bool {
        self.blue.is_some() || self.red.is_some()
    }

    fn write_blue(&mut self, on: bool) {
        if let Some(file) = self.blue.as_mut() {
            let _ = file.write_all(if on { LED_ON } else { LED_OFF });
        }
    }

    fn write_red(&mut self, on: bool) {
        if let Some(file) = self.red.as_mut() {
            let _ = file.write_all(if on { LED_ON } else { LED_OFF });
        }
    }

    fn off(&mut self) {
        self.write_blue(false);
        self.write_red(false);
    }
}

pub struct LedCaps {
    is_on: bool,
    color: Option<String>,
    channels: LedChannels,
}

impl LedCaps {
    pub fn new() -> Self {
        let mut channels = LedChannels::open();
        // Establish a known starting state regardless of boot polarity.
        channels.off();
        Self {
            is_on: false,
            color: None,
            channels,
        }
    }

    pub fn run_program(&mut self, args: LedProgramArgs) -> Value {
        match args {
            LedProgramArgs::Steps { steps, repeat } => self.run_steps(steps, repeat.unwrap_or(1)),
            LedProgramArgs::Morse {
                text,
                unit_ms,
                repeat,
            } => self.blink_morse(
                &text,
                unit_ms.unwrap_or(DEFAULT_MORSE_UNIT_MS),
                repeat.unwrap_or(1),
            ),
        }
    }

    fn run_steps(&mut self, steps: Vec<LedStep>, repeat: u32) -> Value {
        if steps.is_empty() {
            return error_result("invalid_args", String::from("steps cannot be empty"));
        }
        if repeat == 0 {
            return error_result("invalid_args", String::from("repeat must be >= 1"));
        }

        for round in 0..repeat {
            println!(
                "led> program mode=steps round={}/{} step_count={} hardware={}",
                round + 1,
                repeat,
                steps.len(),
                self.channels.is_hardware(),
            );
            for (index, step) in steps.iter().enumerate() {
                let on = match parse_led_state(&step.state) {
                    Ok(state) => state,
                    Err(error) => return error_result("invalid_args", error),
                };
                if let Err(error) = self.apply(on, step.color.as_deref()) {
                    return error_result("unsupported_color", error);
                }
                println!(
                    "led> step {}/{} state={} color={} hold_ms={}",
                    index + 1,
                    steps.len(),
                    step.state,
                    step.color.as_deref().unwrap_or("(inherit)"),
                    step.hold_ms.unwrap_or(0),
                );
                if let Some(hold_ms) = step.hold_ms {
                    sleep_ms(hold_ms);
                }
            }
        }

        json!({
            "ok": true,
            "action": "led_program",
            "mode": "steps",
            "repeat": repeat,
            "step_count": steps.len(),
            "hardware": self.channels.is_hardware(),
            "final_state": if self.is_on {"on"} else {"off"},
            "final_color": self.color
        })
    }

    fn blink_morse(&mut self, text: &str, unit_ms: u64, repeat: u32) -> Value {
        if unit_ms == 0 {
            return error_result("invalid_args", String::from("unit_ms must be >= 1"));
        }
        if repeat == 0 {
            return error_result("invalid_args", String::from("repeat must be >= 1"));
        }
        let uppercase = text.to_ascii_uppercase();
        let chars: Vec<char> = uppercase.chars().collect();

        for round in 0..repeat {
            println!(
                "led> program mode=morse round={}/{} text={} hardware={}",
                round + 1,
                repeat,
                text,
                self.channels.is_hardware(),
            );
            for (char_index, ch) in chars.iter().enumerate() {
                if *ch == ' ' {
                    println!("led> morse char={} value=<space>", char_index + 1);
                    self.apply(false, None).ok();
                    sleep_ms(unit_ms * 7);
                    continue;
                }

                let Some(code) = morse_code(*ch) else {
                    return error_result(
                        "unsupported_char",
                        format!("character '{ch}' is not supported by morse encoder"),
                    );
                };

                println!(
                    "led> morse char={} value={} code={}",
                    char_index + 1,
                    ch,
                    code
                );

                for (symbol_index, symbol) in code.chars().enumerate() {
                    // Morse symbols are rendered in white (both LEDs on).
                    if let Err(error) = self.apply(true, Some("white")) {
                        return error_result("unsupported_color", error);
                    }
                    let hold = if symbol == '-' { unit_ms * 3 } else { unit_ms };
                    sleep_ms(hold);

                    self.apply(false, None).ok();
                    if symbol_index + 1 < code.len() {
                        sleep_ms(unit_ms);
                    }
                }

                if char_index + 1 < chars.len() {
                    sleep_ms(unit_ms * 3);
                }
            }
        }

        json!({
            "ok": true,
            "action": "led_program",
            "mode": "morse",
            "text": text,
            "unit_ms": unit_ms,
            "repeat": repeat,
            "hardware": self.channels.is_hardware(),
            "final_state": if self.is_on {"on"} else {"off"}
        })
    }

    /// Validate `color` and drive the LED channels accordingly, then update the
    /// cached state. Returns an error message when the color cannot be rendered
    /// by the two-LED (red + blue) hardware.
    fn apply(&mut self, on: bool, color: Option<&str>) -> Result<(), String> {
        if on {
            let (red, blue) = color_channels(color)?;
            self.channels.write_red(red);
            self.channels.write_blue(blue);
        } else {
            self.channels.off();
        }
        self.is_on = on;
        self.color = color.map(|c| c.to_ascii_lowercase());
        Ok(())
    }
}

/// Parse the human-readable step state into a boolean level.
fn parse_led_state(state: &str) -> Result<bool, String> {
    match state.to_ascii_lowercase().as_str() {
        "on" => Ok(true),
        "off" => Ok(false),
        _ => Err(format!("invalid state '{state}'; expected 'on' or 'off'")),
    }
}

/// Map a color name to (red, blue) channel levels.
///
/// Only colors expressible with the red + blue LEDs are accepted; anything else
/// is rejected so callers learn the hardware limit rather than silently getting
/// the wrong color.
fn color_channels(color: Option<&str>) -> Result<(bool, bool), String> {
    match color.map(|c| c.to_ascii_lowercase()).as_deref() {
        None | Some("white") => Ok((true, true)),
        Some("red") => Ok((true, false)),
        Some("blue") => Ok((false, true)),
        Some("purple" | "magenta" | "violet" | "pink") => Ok((true, true)),
        Some(other) => Err(format!(
            "unsupported color '{other}'; supported: red, blue, white, purple, magenta, violet, pink"
        )),
    }
}

/// ITU Morse code for A-Z and 0-9. Returns `None` for unsupported characters.
fn morse_code(ch: char) -> Option<&'static str> {
    Some(match ch {
        'A' => ".-",
        'B' => "-...",
        'C' => "-.-.",
        'D' => "-..",
        'E' => ".",
        'F' => "..-.",
        'G' => "--.",
        'H' => "....",
        'I' => "..",
        'J' => ".---",
        'K' => "-.-",
        'L' => ".-..",
        'M' => "--",
        'N' => "-.",
        'O' => "---",
        'P' => ".--.",
        'Q' => "--.-",
        'R' => ".-.",
        'S' => "...",
        'T' => "-",
        'U' => "..-",
        'V' => "...-",
        'W' => ".--",
        'X' => "-..-",
        'Y' => "-.--",
        'Z' => "--..",
        '0' => "-----",
        '1' => ".----",
        '2' => "..---",
        '3' => "...--",
        '4' => "....-",
        '5' => ".....",
        '6' => "-....",
        '7' => "--...",
        '8' => "---..",
        '9' => "----.",
        _ => return None,
    })
}

/// `librs::time::msleep` is the reliable delay primitive on BlueOS; the Rust
/// std library's `thread::sleep`/`Instant` resolve `CLOCK_MONOTONIC` to the
/// wrong constant and return `EINVAL` (see `agent_loop/mod.rs`).
fn sleep_ms(ms: u64) {
    let _ = librs::time::msleep(ms as u32);
}
