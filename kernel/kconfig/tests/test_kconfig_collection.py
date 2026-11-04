#!/usr/bin/env python3
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
"""Verify nested Kconfig collection records its inputs and merged config."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

KCONFIG_ROOT = Path(__file__).resolve().parents[1]


class KconfigCollectionTest(unittest.TestCase):

    def test_collection_preserves_merge_order_and_tracks_sourced_files(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            kconfig = root / "Kconfig"
            sourced = root / "Kconfig.feature"
            parent = root / "parent.conf"
            app = root / "app.conf"
            kconfig.write_text(f'source "{sourced}"\n')
            sourced.write_text('config FEATURE\n    bool "Feature"\n')
            parent.write_text("# CONFIG_FEATURE is not set\n")
            app.write_text("CONFIG_FEATURE=y\n")
            result = subprocess.run([
                sys.executable,
                str(KCONFIG_ROOT / "src/generate_artifacts.py"), "--kconfig",
                str(kconfig), "--board", "none", "--build_type", "debug",
                "--output_dir",
                str(root / "gen"), "--defconfig_files", f"{parent},{app}",
                "--collect-inputs"
            ],
                                    cwd=root,
                                    text=True,
                                    capture_output=True,
                                    check=True)
            record = json.loads(result.stdout)
            self.assertEqual(set(record["inputs"]),
                             {str(p)
                              for p in (kconfig, sourced, parent, app)})
            config = Path(record["config"])
            self.assertTrue(config.is_absolute())
            self.assertIn("CONFIG_FEATURE=y", config.read_text())


if __name__ == "__main__":
    unittest.main()
