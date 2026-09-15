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

import os
import sys
import re
import subprocess
import shlex
import shutil
import tempfile
import logging
import argparse
import asyncio

LOGGER = logging.getLogger(__name__)
LOGGER.setLevel(logging.INFO)


class Rule(object):

    def __init__(self, pattern, action, priority=0):
        self.pattern = pattern
        self.action = action
        self.priority = priority


class AssertFailException(Exception):
    pass


class AssertSuccNotifier(Exception):
    pass


class Action(object):

    def __init__(self):
        pass

    def take(self, checker, line):
        pass


class CheckFail(Action):

    def take(self, checker, line):
        checker.add_fail_line(line)


class CheckSucc(Action):

    def take(self, checker, line):
        checker.add_succ_line(line)


class AssertFail(Action):

    def take(self, checker, line):
        checker.add_fail_line(line)
        raise AssertFailException()


class AssertSucc(Action):

    def take(self, checker, line):
        checker.add_succ_line(line)
        raise AssertSuccNotifier()


class Checker(object):

    def __init__(self, script, test_dir):
        self.script = os.path.abspath(script)
        self.timeout = 1 << 30
        self.total_timeout = 1 << 30
        self.rules = []
        self.succ_lines = []
        self.fail_lines = []
        self.counters = []
        self.test_dir = os.path.abspath(test_dir)

    def add_succ_line(self, line):
        self.succ_lines.append(line)
        return self

    def add_fail_line(self, line):
        self.fail_lines.append(line)
        return self

    def add_check_succ(self, pattern):
        self.add_rule(pattern, CheckSucc(), 0)
        return self

    def add_check_fail(self, pattern):
        self.add_rule(pattern, CheckFail(), 1)
        return self

    def add_assert_succ(self, pattern):
        self.add_rule(pattern, AssertSucc(), 2)
        return self

    def add_assert_fail(self, pattern):
        self.add_rule(pattern, AssertFail(), 3)
        return self

    def add_count(self, pattern, expected):
        self.counters.append([pattern, expected, 0])
        return self

    def add_rule(self, pattern, action, priority):
        self.rules.append(Rule(pattern, action, priority))
        return self

    def set_newline_timeout(self, timeout):
        self.timeout = timeout
        return self

    def set_total_timeout(self, timeout):
        self.total_timeout = timeout
        return self

    def count_matches(self, line):
        for counter in self.counters:
            if counter[0].search(line):
                counter[2] += 1

    def counts_satisfied(self):
        satisfied = True
        for pattern, expected, seen in self.counters:
            if seen != expected:
                LOGGER.error('Count mismatch: %r expected %d lines, saw %d',
                             pattern.pattern, expected, seen)
                satisfied = False
        return satisfied

    def check(self, line):
        self.count_matches(line)
        for rule in self.rules:
            m = rule.pattern.search(line)
            if m:
                rule.action.take(self, line)

    def run_and_check(self):
        self.rules.sort(key=lambda x: x.priority, reverse=True)
        # Create test directory if it doesn't exist
        os.makedirs(self.test_dir, exist_ok=True)
        return asyncio.run(self.go())

    async def go(self):
        process = await asyncio.create_subprocess_exec(
            self.script,
            cwd=self.test_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT)
        succ = False
        try:
            async with asyncio.timeout(delay=self.total_timeout):
                while True:
                    output_line = await asyncio.wait_for(
                        process.stdout.readline(), timeout=self.timeout)
                    if not output_line:
                        break
                    output_line = output_line.decode(errors='replace')
                    sys.stdout.write(output_line)
                    sys.stdout.flush()
                    try:
                        self.check(output_line)
                    except AssertFailException:
                        succ = False
                        break
                    except AssertSuccNotifier:
                        # The terminal success line arrived: every COUNT
                        # directive must have seen exactly its expected number
                        # of matching lines over the whole run.
                        succ = self.counts_satisfied()
                        break
        except asyncio.TimeoutError:
            LOGGER.error('Check Timeout')
            succ = False
        try:
            process.kill()
        except Exception:
            pass
        finally:
            await process.wait()
        LOGGER.info('Successful lines:')
        for line in self.succ_lines:
            LOGGER.info(line.strip())
        LOGGER.info('Failed lines:')
        for line in self.fail_lines:
            LOGGER.info(line.strip())
        if succ:
            LOGGER.info('Passed check')
            return 0
        LOGGER.info('Failed check')
        return -1


CHECK_FAIL = re.compile(r'^//\s*CHECK-FAIL:\s*(.*)$')
CHECK_SUCC = re.compile(r'^//\s*CHECK-SUCC:\s*(.*)$')
ASSERT_FAIL = re.compile(r'^//\s*ASSERT-FAIL:\s*(.*)$')
ASSERT_SUCC = re.compile(r'^//\s*ASSERT-SUCC:\s*(.*)$')
COUNT = re.compile(r'^//\s*COUNT:\s*(.*?)\s*==\s*(\d+)\s*$')
NEWLINE_TIMEOUT = re.compile(r'^//\s*NEWLINE-TIMEOUT:\s*(\d+)$')
TOTAL_TIMEOUT = re.compile(r'^//\s*TOTAL-TIMEOUT:\s*(\d+)$')


class DirectiveParser(object):

    def __init__(self, checker):
        self.checker = checker

    def parse(self, filename):
        with open(filename) as f:
            for line in f:
                m = CHECK_FAIL.match(line)
                if m:
                    self.checker.add_check_fail(re.compile(m.group(1)))
                    continue
                m = CHECK_SUCC.match(line)
                if m:
                    self.checker.add_check_succ(re.compile(m.group(1)))
                    continue
                m = ASSERT_FAIL.match(line)
                if m:
                    self.checker.add_assert_fail(re.compile(m.group(1)))
                    continue
                m = ASSERT_SUCC.match(line)
                if m:
                    self.checker.add_assert_succ(re.compile(m.group(1)))
                    continue
                m = COUNT.match(line)
                if m:
                    self.checker.add_count(re.compile(m.group(1)),
                                           int(m.group(2)))
                    continue
                m = NEWLINE_TIMEOUT.match(line)
                if m:
                    self.checker.set_newline_timeout(int(m.group(1)))
                    continue
                m = TOTAL_TIMEOUT.match(line)
                if m:
                    self.checker.set_total_timeout(int(m.group(1)))
                    continue
                break
        return True


def run_and_check(config):
    checker = Checker(config.s, config.t)
    directive_parser = DirectiveParser(checker)
    if not directive_parser.parse(config.check_file):
        return -1
    return checker.run_and_check()


def main():
    parser = argparse.ArgumentParser(
        description='QEMU checker for BlueOS kernel')
    parser.add_argument('-s', help='The qemu runner script', required=True)
    parser.add_argument('-t', help='The test directory', required=True)
    parser.add_argument(
        'check_file',
        help='File containing check directives',
    )

    config = parser.parse_args()
    return run_and_check(config)


if __name__ == '__main__':
    sys.exit(main())
