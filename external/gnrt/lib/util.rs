// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

//! Process, path, and template helpers for crate synchronization.

use crate::gn_condition::GnConditionHelper;
use crate::sync_state::tool_path;
use anyhow::{ensure, Context, Result};
use handlebars::{handlebars_helper, JsonTruthy};
use serde::Serialize;
use std::io::Write;
use std::{
    fs,
    path::{Path, PathBuf},
    process,
};

/// Resolves the compiler independently of vendored crates' rustup configuration.
///
/// The query supplies its own target; other compiler arguments are preserved.
///
/// # Errors
///
/// Returns an error for malformed commands, missing compilers, or failed
/// rustup lookups.
pub fn rustc_command(compiler: &str) -> Result<process::Command> {
    let words = shlex::split(compiler).context("invalid Rust compiler command quoting")?;
    let program = words.first().context("Rust compiler command is empty")?;
    let mut executable = match tool_path(program) {
        Ok(path) => path,
        // Toolchains install cargo and rustc into the same bin directory, so a
        // cargo located via override covers a rustc missing from PATH.
        Err(error) if program == "rustc" => rustc_next_to_cargo().ok_or(error)?,
        Err(error) => return Err(error),
    }
    .canonicalize()?;
    let mut args = Vec::new();
    let mut words = words.iter().skip(1);
    while let Some(arg) = words.next() {
        // The query supplies the target; keep flags that affect its cfg values.
        if arg == "--target" {
            let target = words.next().context("--target requires a value")?;
            ensure!(
                !target.is_empty() && !target.starts_with('-'),
                "--target requires a value"
            );
        } else if let Some(target) = arg.strip_prefix("--target=") {
            ensure!(!target.is_empty(), "--target requires a value");
        } else {
            args.push(arg.clone());
        }
    }
    if executable.file_name().and_then(|name| name.to_str()) == Some("rustup") {
        let toolchain = strip_rustup_routing(&mut args);
        let mut rustup = process::Command::new(&executable);
        if let Some(toolchain) = toolchain {
            rustup.args(["--toolchain", &toolchain]);
        }
        let output = rustup.args(["which", "rustc"]).output()?;
        check_exit_ok(&output, "resolving rustc through rustup")?;
        let path = String::from_utf8(output.stdout).context("rustup returned a non-UTF-8 path")?;
        executable = std::fs::canonicalize(path.trim())?;
    }
    let mut command = process::Command::new(executable);
    command.args(args);
    Ok(command)
}

/// Returns rustc installed beside cargo, or `None` when cargo cannot be located.
fn rustc_next_to_cargo() -> Option<PathBuf> {
    let cargo = tool_path("cargo").ok()?;
    let rustc = cargo.parent()?.join("rustc");
    rustc.is_file().then_some(rustc)
}

/// Strips rustup routing words from `args` and returns the selected toolchain.
///
/// Consumes the leading `+toolchain` or `run <toolchain>` selector and the
/// proxied `rustc` word so the resolved compiler receives only real flags.
fn strip_rustup_routing(args: &mut Vec<String>) -> Option<String> {
    let take = match args.first().map(String::as_str) {
        Some(first) if first.starts_with('+') => 1,
        Some("run") if args.len() >= 3 => 2,
        _ => 0,
    };
    let toolchain = if take > 0 {
        // The selector is `+toolchain` (one word) or `run <toolchain>` (two).
        let selector: Vec<String> = args.drain(..take).collect();
        Some(match take {
            2 => selector[1].clone(),
            _ => selector[0][1..].to_owned(),
        })
    } else {
        None
    };
    if args.first().is_some_and(|arg| arg == "rustc") {
        args.remove(0);
    }
    toolchain
}

fn check_exit_ok(output: &process::Output, description: &str) -> Result<()> {
    ensure!(
        output.status.success(),
        "{description} failed with {}: {}",
        exit_code_text(&output.status),
        String::from_utf8_lossy(&output.stderr)
    );
    Ok(())
}

/// Formats a child process exit status for diagnostics.
pub fn exit_code_text(status: &process::ExitStatus) -> String {
    match status.code() {
        Some(code) => format!("exit code {code}"),
        None => "no exit code".to_owned(),
    }
}

/// Creates a directory and any missing parent directories.
///
/// # Errors
///
/// Returns an error if the directory cannot be created.
pub fn create_dirs_if_needed(path: &Path) -> Result<()> {
    fs::create_dir_all(path).with_context(|| format!("creating {}", path.display()))
}

/// Formats GN arguments without evaluating them.
///
/// # Errors
///
/// Returns an error if GN cannot be run or the arguments are invalid.
pub fn normalize_gn_args(args: &[String]) -> Result<String> {
    crate::sync_state::normalize_args(args)
}

/// Joins a root-relative GN path label such as `//kernel/Cargo.lock` to the
/// checkout root.
///
/// # Errors
///
/// Returns an error if `label` is not a root-relative GN path.
pub fn gn_path_label_to_path(root: &Path, label: &str) -> Result<PathBuf> {
    let relative = label
        .strip_prefix("//")
        .with_context(|| format!("path {label} is not a root-relative GN path"))?;
    Ok(root.join(relative))
}

/// Loads GN templates into a strict Handlebars registry.
///
/// Registers GN condition rendering, string escaping, and value helpers.
///
/// # Errors
///
/// Returns an error if a template path is not UTF-8 or a template cannot be
/// read or parsed.
pub fn init_handlebars_with_template_paths(
    template_paths: &[&Path],
) -> Result<handlebars::Handlebars<'static>> {
    let mut registry = handlebars::Handlebars::new();
    registry.set_strict_mode(true);
    registry.register_escape_fn(handlebars::no_escape);
    // GN expressions are emitted verbatim; only quoted strings use gn_escape.
    handlebars_helper!(gn_escape: |value: String| {
        value.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', " ")
    });
    handlebars_helper!(eq: |a: String, b: String| a == b);
    handlebars_helper!(any: |a: Json, b: Json| a.is_truthy(false) || b.is_truthy(false));
    registry.register_helper("gn_condition", Box::new(GnConditionHelper));
    registry.register_helper("gn_escape", Box::new(gn_escape));
    registry.register_helper("eq", Box::new(eq));
    registry.register_helper("any", Box::new(any));
    for path in template_paths {
        let name = path.to_str().context("template path is not UTF-8")?;
        registry
            .register_template_file(name, path)
            .with_context(|| format!("loading template {}", path.display()))?;
    }
    Ok(registry)
}

/// Renders a registered template into an output file.
///
/// # Errors
///
/// Returns an error if the template path is not UTF-8, rendering fails, or the
/// output file cannot be created or written.
pub fn render_handlebars(
    registry: &handlebars::Handlebars,
    template_path: &Path,
    data: &impl Serialize,
    output_path: &Path,
) -> Result<()> {
    let name = template_path
        .to_str()
        .context("template path is not UTF-8")?;
    let output = fs::File::create(output_path)
        .with_context(|| format!("creating {}", output_path.display()))?;
    let mut writer = std::io::BufWriter::new(output);
    registry
        .render_to_write(name, data, &mut writer)
        .with_context(|| format!("rendering template {}", template_path.display()))?;
    writer
        .flush()
        .with_context(|| format!("writing {}", output_path.display()))
}

/// Formats a generated GN file with the configured GN executable.
///
/// # Errors
///
/// Returns an error if GN cannot be found, cannot start, or rejects the file.
pub fn format_gn_file(path: &Path) -> Result<()> {
    let output = process::Command::new(tool_path("gn")?)
        .arg("format")
        .arg(path)
        .output()
        .with_context(|| format!("starting gn format for {}", path.display()))?;
    ensure!(
        output.status.success(),
        "gn format failed for {}: {}\n{}",
        path.display(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    Ok(())
}
