#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

"""Print each argument on its own line and exit 0.

Used by GN `action`s that only need to surface a message to the user (e.g. the
run_quickjs REPL launcher hint, or the "feature disabled" notice)."""

import sys


def main():
    for line in sys.argv[1:]:
        print(line)
    return 0


if __name__ == '__main__':
    sys.exit(main())
