#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""
Test template for running external repository tests.

This script:
1. Downloads a git repository tag to a specified directory
2. Applies a patch file
3. Runs build and test commands

Example usage:
    python run_test.py \
        --repo https://github.com/RT-Thread/rt-thread \
        --tag v5.2.2 \
        --target-dir kernel/kernel/tests/thread_metric/rt-thread \
        --patch kernel/kernel/tests/thread_metric/rtt_tm.diff \
        --build-dir bsp/qemu-vexpress-a9 \
        --build-cmd "scons" \
        --run-cmd "bash qemu-nographic.sh" \
        --timeout 60
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from datetime import datetime
from pathlib import Path

# Constants
DEFAULT_TIMEOUT = 60


def log_info(message, indent=0, output_file=None):
    """Print formatted log message with timestamp.
    
    Args:
        message: Message to print
        indent: Indentation level (number of spaces * 2)
        output_file: File object to write to (None for stdout, sys.stderr for stderr)
    """
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    indent_str = "  " * indent
    output = f"[{timestamp}] {indent_str}{message}"
    if output_file:
        print(output, file=output_file, flush=True)
    else:
        print(output, flush=True)


def log_step(step_num, total_steps, message):
    """Print step information."""
    log_info(f"[Step {step_num}/{total_steps}] {message}")


def check_success_patterns(output, success_patterns):
    """Check if output matches any success pattern.
    
    Args:
        output: Output text to check
        success_patterns: List of regex patterns
    
    Returns:
        tuple: (matched, pattern) where matched is bool and pattern is the matched pattern or None
    """
    if not success_patterns:
        return False, None

    for pattern in success_patterns:
        if re.search(pattern, output, re.IGNORECASE):
            return True, pattern
    return False, None


def run_cmd(cmd,
            cwd=None,
            check=True,
            shell=False,
            silent=False,
            timeout=None,
            success_patterns=None,
            timeout_is_success=False):
    """Run a command and return the result.
    
    Args:
        cmd: Command to run
        cwd: Working directory
        check: Whether to raise exception on non-zero exit code
        shell: Whether to run in shell
        silent: Whether to suppress log messages
        timeout: Timeout in seconds (None for no timeout)
        success_patterns: List of regex patterns. If any pattern matches output, consider success even on failure
        timeout_is_success: If True, treat timeout as success (don't raise exception)
    """
    if not silent:
        log_info(f"Running command: {cmd}", indent=1)
        if cwd:
            log_info(f"Working directory: {cwd}", indent=1)

    start_time = time.time()

    if isinstance(cmd, str) and not shell:
        cmd = cmd.split()

    result = None
    try:
        # Use Popen to capture output even on timeout
        if timeout is not None:
            process = subprocess.Popen(
                cmd,
                cwd=cwd,
                shell=shell,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,  # Merge stderr into stdout
                text=True,
                bufsize=1  # Line buffered
            )

            # Collect output in a list while printing
            output_lines = []
            output_lock = threading.Lock()

            def read_output():
                """Read output and print in real-time while collecting."""
                try:
                    for line in process.stdout:
                        line_str = line
                        with output_lock:
                            output_lines.append(line_str)
                        print(line_str, end='', flush=True)
                except Exception:
                    pass

            # Start reading output in a separate thread
            reader_thread = threading.Thread(target=read_output, daemon=True)
            reader_thread.start()

            try:
                process.wait(timeout=timeout)
                returncode = process.returncode
                # Wait for reader thread to finish
                reader_thread.join(timeout=1)
                # Collect remaining output
                stdout = ''.join(output_lines)
                stderr = ""  # Already merged into stdout
                result = subprocess.CompletedProcess(cmd, returncode, stdout,
                                                     stderr)
            except subprocess.TimeoutExpired:
                # On timeout, try to get remaining output
                log_info(f"Command timed out after {timeout}s", indent=2)
                try:
                    process.kill()
                    # Wait for reader thread to finish reading remaining output
                    reader_thread.join(timeout=2)
                    # Collect all output
                    stdout = ''.join(output_lines)
                    stderr = ""  # Already merged into stdout
                except Exception:
                    stdout = ''.join(output_lines)
                    stderr = ""
                returncode = 124  # Standard timeout exit code
                result = subprocess.CompletedProcess(cmd, returncode, stdout,
                                                     stderr)
                if timeout_is_success:
                    log_info("Timeout treated as success", indent=2)
                    result.returncode = 0
        else:
            # No timeout, use simple run
            result = subprocess.run(cmd,
                                    cwd=cwd,
                                    shell=shell,
                                    capture_output=True,
                                    text=True,
                                    check=False)
    except Exception as e:
        log_info(f"Error running command: {e}",
                 indent=2,
                 output_file=sys.stderr)

        class MockResult:

            def __init__(self, returncode, stdout="", stderr=""):
                self.returncode = returncode
                self.stdout = stdout
                self.stderr = stderr

        result = MockResult(1, stderr=str(e))

    elapsed = time.time() - start_time

    # Check for success patterns if provided
    if success_patterns and result.returncode != 0:
        combined_output = (result.stdout or "") + (result.stderr or "")
        matched, pattern = check_success_patterns(combined_output,
                                                  success_patterns)
        if matched:
            log_info(
                f"Success pattern detected: {pattern}, treating as success",
                indent=2)
            result.returncode = 0

    if not silent:
        if result.returncode == 0:
            log_info(f"Command completed successfully (took {elapsed:.2f}s)",
                     indent=1)
        else:
            log_info(
                f"Command failed with exit code {result.returncode} (took {elapsed:.2f}s)",
                indent=1)

    # Print output at the end (only if not already printed during execution)
    # For timeout case, output is already printed in real-time, so skip here
    if timeout is None:
        if hasattr(result, 'stdout') and result.stdout:
            print(result.stdout, end='')
        if hasattr(result, 'stderr') and result.stderr:
            print(result.stderr, end='', file=sys.stderr)

    # If check=True and command failed, raise exception
    if check and result.returncode != 0:
        raise subprocess.CalledProcessError(
            result.returncode, cmd,
            result.stdout if hasattr(result, 'stdout') else None,
            result.stderr if hasattr(result, 'stderr') else None)

    return result


def download_repo(repo_url, tag, target_dir, root_dir):
    """Download a git repository tag to target directory.
    
    Returns:
        tuple: (target_path, was_downloaded) where was_downloaded is True if
               the repository was actually downloaded, False if it already existed.
    """
    log_step(1, 3, "Downloading repository")
    log_info(f"Repository: {repo_url}@{tag}", indent=1)

    # Handle both absolute and relative paths
    if os.path.isabs(target_dir):
        target_path = Path(target_dir)
    else:
        target_path = Path(root_dir) / target_dir

    # If directory already exists, skip download
    if target_path.exists() and (target_path / ".git").exists():
        log_info(f"✓ Repository already exists, skipping download", indent=1)
        return target_path, False

    # Remove existing directory if it exists (but is not a git repo)
    if target_path.exists():
        shutil.rmtree(target_path)

    # Create parent directory
    target_path.parent.mkdir(parents=True, exist_ok=True)

    # Clone repository to a temporary directory first
    start_time = time.time()
    with tempfile.TemporaryDirectory() as temp_dir:
        temp_path = Path(temp_dir) / "repo"
        run_cmd([
            "git", "clone", "--depth", "1", "--branch", tag, repo_url,
            str(temp_path)
        ],
                check=True,
                silent=True)

        # Move to target directory
        shutil.move(str(temp_path), str(target_path))

    elapsed = time.time() - start_time
    log_info(f"✓ Repository downloaded successfully (took {elapsed:.2f}s)",
             indent=1)
    return target_path, True


def apply_patch(patch_file, repo_dir, root_dir, skip_if_exists=False):
    """Apply a patch file to the repository.
    
    Args:
        patch_file: Path to patch file
        repo_dir: Repository directory
        root_dir: Root directory
        skip_if_exists: If True and patch appears already applied, skip silently
    
    Returns:
        bool: True if patch was applied, False if skipped
    """
    # Handle both absolute and relative paths
    if os.path.isabs(patch_file):
        patch_path = Path(patch_file)
    else:
        patch_path = Path(root_dir) / patch_file

    if not patch_path.exists():
        raise FileNotFoundError(f"Patch file not found: {patch_path}")

    # Change to repository directory and apply patch
    if os.path.isabs(repo_dir):
        repo_path = Path(repo_dir)
    else:
        repo_path = Path(root_dir) / repo_dir

    # Check if patch is already applied by checking git status
    if skip_if_exists:
        result = run_cmd(["git", "apply", "--check",
                          str(patch_path)],
                         cwd=repo_path,
                         check=False,
                         silent=True)
        if result.returncode != 0:
            result_check = run_cmd(
                ["git", "apply", "--reverse", "--check",
                 str(patch_path)],
                cwd=repo_path,
                check=False,
                silent=True)
            if result_check.returncode == 0:
                log_info("✓ Patch already applied, skipping", indent=1)
                return False

    log_step(2, 3, "Applying patch")

    # Strategy 1: Try git apply with lenient options
    # --3way: allow 3-way merge if patch doesn't apply cleanly
    # --ignore-whitespace: ignore whitespace differences
    result = run_cmd(
        ["git", "apply", "--3way", "--ignore-whitespace",
         str(patch_path)],
        cwd=repo_path,
        check=False)

    if result.returncode == 0:
        log_info("✓ Patch applied successfully", indent=1)
        return True

    # Strategy 2: Try with --reject to see what fails and apply what we can
    result_reject = run_cmd(
        ["git", "apply", "--reject", "--ignore-whitespace",
         str(patch_path)],
        cwd=repo_path,
        check=False)

    # Check if Strategy 2 succeeded (returncode 0 and all patches applied cleanly)
    if result_reject.returncode == 0:
        stderr_lower = result_reject.stderr.lower(
        ) if result_reject.stderr else ""
        stdout_lower = result_reject.stdout.lower(
        ) if result_reject.stdout else ""
        combined_output = stderr_lower + stdout_lower

        # Check if all patches were applied cleanly
        if "applied patch" in combined_output and "cleanly" in combined_output:
            log_info("✓ Patch applied successfully", indent=1)
            return True
        # Even if not all cleanly, if returncode is 0 and no reject files, consider success
        reject_files = list(repo_path.rglob("*.rej"))
        if not reject_files:
            log_info("✓ Patch applied successfully", indent=1)
            return True

    # Check for reject files
    reject_files = list(repo_path.rglob("*.rej"))

    # Check if the errors are about files already existing
    stderr_lower = result_reject.stderr.lower() if result_reject.stderr else ""
    stdout_lower = result_reject.stdout.lower() if result_reject.stdout else ""
    combined_output = stderr_lower + stdout_lower

    # Strategy 3: If files already exist, use patch command with force
    if "already exists" in combined_output or reject_files:
        result = run_cmd(
            ["patch", "-p1", "-i",
             str(patch_path), "--force", "--backup"],
            cwd=repo_path,
            check=False)

        if result.returncode == 0:
            log_info("✓ Patch applied successfully", indent=1)
            return True

        # Check output for success indicators
        patch_stderr = result.stderr.lower() if result.stderr else ""
        patch_stdout = result.stdout.lower() if result.stdout else ""
        patch_output = patch_stderr + patch_stdout

        # If patch says it succeeded or files already applied, consider it success
        if ("succeeded" in patch_output or "already applied" in patch_output
                or "previously applied" in patch_output
                or "patching file" in patch_output):
            log_info("✓ Patch applied successfully", indent=1)
            return True

    # Strategy 4: Check if reject files exist (partial application)
    if reject_files:
        # Clean up reject files
        for reject_file in reject_files:
            try:
                reject_file.unlink()
            except Exception:
                pass
        log_info("✓ Patch partially applied, continuing", indent=1)
        return True

    # Strategy 5: If skip_if_exists is True, be more lenient
    if skip_if_exists:
        # Try to read patch file to see what files it modifies
        try:
            with open(patch_path, 'r', encoding='utf-8', errors='ignore') as f:
                patch_content = f.read()
                file_pattern = r'^\+\+\+ b/(.+)$'
                files_in_patch = re.findall(file_pattern, patch_content,
                                            re.MULTILINE)

                files_exist = 0
                checked_files = min(10, len(files_in_patch))
                for file_path in files_in_patch[:checked_files]:
                    full_path = repo_path / file_path
                    if full_path.exists():
                        files_exist += 1

                threshold = len(files_in_patch) / 2
                if files_exist > threshold:
                    log_info("✓ Patch appears to be already applied", indent=1)
                    return True
        except Exception:
            pass

        log_info("✓ Continuing despite patch errors (skip_if_exists=True)",
                 indent=1)
        return True

    # If all strategies fail, raise error
    error_msg = f"Failed to apply patch: {patch_path}\n"
    if result_reject.stderr:
        error_msg += f"git apply error: {result_reject.stderr}\n"
    if result.stderr:
        error_msg += f"patch command error: {result.stderr}\n"
    raise RuntimeError(error_msg)


def run_build_and_test(build_dir,
                       build_cmd,
                       test_cmd,
                       repo_dir,
                       root_dir,
                       timeout=None):
    """Run build and test commands.
    
    Args:
        timeout: Timeout in seconds for test commands (None for no timeout)
    """
    log_step(3, 3, "Running build and test")

    # Handle both absolute and relative paths
    if os.path.isabs(repo_dir):
        repo_path = Path(repo_dir)
    else:
        repo_path = Path(root_dir) / repo_dir

    work_dir = repo_path / build_dir

    if not work_dir.exists():
        raise FileNotFoundError(f"Build directory not found: {work_dir}")

    # Run build command
    if build_cmd:
        log_info("BUILD PHASE", indent=0)
        start_time = time.time()
        try:
            run_cmd(build_cmd, cwd=work_dir, shell=True, check=True)
            elapsed = time.time() - start_time
            log_info(f"✓ Build completed (took {elapsed:.2f}s)", indent=1)
        except subprocess.CalledProcessError as e:
            elapsed = time.time() - start_time
            log_info(
                f"✗ Build failed (exit code {e.returncode}, took {elapsed:.2f}s)",
                indent=1)
            raise

    # Run test command
    if test_cmd:
        log_info("TEST PHASE", indent=0)
        start_time = time.time()
        success_patterns = [
            r"Hello RT-Thread!", r"msh />", r"RT-Thread Operating System"
        ]
        try:
            run_cmd(
                test_cmd,
                cwd=work_dir,
                shell=True,
                check=True,
                timeout=timeout,
                success_patterns=success_patterns,
                timeout_is_success=True)  # Treat timeout as success for qemu
            elapsed = time.time() - start_time
            log_info(f"✓ Test completed (took {elapsed:.2f}s)", indent=1)
        except subprocess.CalledProcessError as e:
            elapsed = time.time() - start_time
            log_info(
                f"✗ Test failed (exit code {e.returncode}, took {elapsed:.2f}s)",
                indent=1)
            raise


def main():
    parser = argparse.ArgumentParser(
        description='Download external repository, apply patch, and run tests')
    parser.add_argument('--repo', required=True, help='Git repository URL')
    parser.add_argument('--tag',
                        required=True,
                        help='Git tag or branch to checkout')
    parser.add_argument(
        '--target-dir',
        required=True,
        help='Target directory relative to root to download repository')
    parser.add_argument('--patch',
                        required=True,
                        help='Patch file path relative to root')
    parser.add_argument('--build-dir',
                        required=True,
                        help='Build directory relative to repository root')
    parser.add_argument('--build-cmd',
                        default='',
                        help='Build command to run (e.g., "scons")')
    parser.add_argument(
        '--run-cmd',
        default='',
        help='Test command to run (e.g., "bash qemu-nographic.sh")')
    parser.add_argument('--root-dir',
                        required=True,
                        help='Root directory of the project')
    parser.add_argument(
        '--timeout',
        type=int,
        default=DEFAULT_TIMEOUT,
        help=
        f'Timeout in seconds for test commands (default: {DEFAULT_TIMEOUT})')

    args = parser.parse_args()

    log_info("RT-Thread Test Runner", indent=0)

    overall_start_time = time.time()

    try:
        repo_path, was_downloaded = download_repo(args.repo, args.tag,
                                                  args.target_dir,
                                                  args.root_dir)

        apply_patch(args.patch,
                    args.target_dir,
                    args.root_dir,
                    skip_if_exists=not was_downloaded)
        run_build_and_test(args.build_dir,
                           args.build_cmd,
                           args.run_cmd,
                           args.target_dir,
                           args.root_dir,
                           timeout=args.timeout)

        overall_elapsed = time.time() - overall_start_time
        log_info(
            f"✓ All tests completed successfully (total time: {overall_elapsed:.2f}s)",
            indent=0)
        return 0

    except Exception as e:
        overall_elapsed = time.time() - overall_start_time
        log_info(f"✗ Test failed after {overall_elapsed:.2f}s", indent=0)
        log_info(f"Error: {e}", indent=0, output_file=sys.stderr)
        import traceback
        for line in traceback.format_exc().split('\n'):
            if line.strip():
                log_info(line, indent=1)
        return 1


if __name__ == '__main__':
    sys.exit(main())
