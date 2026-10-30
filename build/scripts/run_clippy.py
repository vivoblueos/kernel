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

import sys
import subprocess
import os

if __name__ == '__main__':
    rc = subprocess.call(['sh'] + sys.argv[1:])
    if rc != 0:
        sys.exit(rc)
    rspfile = sys.argv[1]
    prefix, _ = os.path.splitext(rspfile)
    with open(prefix + '.stamp', 'w') as f:
        pass
