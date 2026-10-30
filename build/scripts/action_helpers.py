# Copyright 2023 The Chromium Authors
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.
"""Helper functions useful when writing scripts used by action() targets."""
import contextlib
import filecmp
import os
import pathlib
import posixpath
import shutil
import tempfile
from typing import Optional
from typing import Sequence


@contextlib.contextmanager
def atomic_output(path, mode='w+b', encoding=None, only_if_changed=True):
    """Prevent half-written files and dirty mtimes for unchanged files.
  Args:
    path: Path to the final output file, which will be written atomically.
    mode: The mode to open the file in (str).
    encoding: Encoding to use if using non-binary mode.
    only_if_changed: Whether to maintain the mtime if the file has not changed.
  Returns:
    A Context Manager that yields a NamedTemporaryFile instance. On exit, the
    manager will check if the file contents is different from the destination
    and if so, move it into place.
  Example:
    with action_helpers.atomic_output(output_path) as tmp_file:
      subprocess.check_call(['prog', '--output', tmp_file.name])
  """
    # Create in same directory to ensure same filesystem when moving.
    dirname = os.path.dirname(path) or '.'
    os.makedirs(dirname, exist_ok=True)
    if encoding is not None and mode == 'w+b':
        mode = 'w+'
    with tempfile.NamedTemporaryFile(mode,
                                     encoding=encoding,
                                     prefix=".tempfile.",
                                     suffix="." + os.path.basename(path),
                                     dir=dirname,
                                     delete=False) as f:
        try:
            yield f
            # File should be closed before comparison/move.
            f.close()
            if not (only_if_changed and os.path.exists(path)
                    and filecmp.cmp(f.name, path)):
                shutil.move(f.name, path)
        finally:
            f.close()
            if os.path.exists(f.name):
                os.unlink(f.name)
