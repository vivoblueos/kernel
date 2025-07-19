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

pub mod cat;
pub mod cd;
pub mod cmp;
pub mod cp;
pub mod echo;
pub mod free;
pub mod help;
pub mod ls;
pub mod mkdir;
pub mod mount;
pub mod printf;
pub mod ps;
pub mod pwd;
pub mod rmdir;
pub mod touch;
pub mod truncate;
pub mod umount;

extern crate phf;
use self::phf::{phf_map, Map};
pub type CommandHandler = fn(&[&str]) -> Result<(), String>;

pub struct CommandInfo {
    pub handler: CommandHandler,
    pub description: &'static str,
}

pub static COMMANDS: Map<&'static str, CommandInfo> = phf_map! {
    "cat" => CommandInfo {
        handler: cat::command,
        description: "Concatenate file(s) to standard output, usage: cat [<path> [<path> [<path> ...]]]",
    },
    "cd" => CommandInfo {
        handler: cd::command,
        description: "Switch current directory, usage: cd <directory>",
    },
    "cmp" => CommandInfo {
        handler: cmp::command,
        description: "Compare two files byte by byte, usage: cmp <path1> <path2>",
    },
    "cp" => CommandInfo {
        handler: cp::command,
        description: "Copy source to dest, usage: cp <source file> <destination file/dir>",
    },
    "echo" => CommandInfo {
        handler: echo::command,
        description: "Write arguments to the standard output, usage: echo [parameters...] / [>] [file]",
    },
    "free" => CommandInfo {
        handler: free::command,
        description: "Display the amount of free and used memory in the system, usage: free",
    },
    "help" => CommandInfo {
        handler: help::command,
        description: "Use help [command] view help for a specific command",
    },
    "ls" => CommandInfo {
        handler: ls::command,
        description: "List directory contents, usage: ls [-a] [-l] [directory]",
    },
    "mkdir" => CommandInfo {
        handler: mkdir::command,
        description: "Create directory, usage: mkdir [OPTION] <path>",
    },
    "printf" => CommandInfo {
        handler: printf::command,
        description: "Formats and prints args under control of the format, usage: printf string<%s, %d, %f> [arg...]",
    },
    "ps" => CommandInfo {
        handler: ps::command,
        description: "Displays the status of the current process, usage:  ps <-heap> <pid1 pid2 ...>",
    },
    "pwd" => CommandInfo {
        handler: pwd::command,
        description: "Print the current working directory",
    },
    "rmdir" => CommandInfo {
        handler: rmdir::command,
        description: "rmdir, Usage: rmdir <path1> <path2>",
    },
    "touch" => CommandInfo {
        handler: touch::command,
        description: "Update the access and modification times of each file to the current time, usage: touch <file>",
    },
    "truncate" => CommandInfo {
        handler: truncate::command,
        description: "Shrink or extend the size of each file, usage: truncate <file> <size>",
    },
    "mount" => CommandInfo {
        handler: mount::command,
        description: "Mount a filesystem, usage: mount <path> <fstype(only support tmpfs)>",
    },
    "umount" => CommandInfo {
        handler: umount::command,
        description: "Unmount filesystems, usage: umout <path>",
    },
};
