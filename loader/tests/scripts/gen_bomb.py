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

import os
import sys
import re
import subprocess
import shlex
import shutil
import tempfile
import logging


def main():
    with open(sys.argv[1], 'r') as f:
        bomb = f.readline().rstrip()
    with open(sys.argv[2], 'r') as f:
        elf = f.readline().rstrip()
    out = sys.argv[3]
    return subprocess.call([bomb, elf, out])


if __name__ == '__main__':
    sys.exit(main())
