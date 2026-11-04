#!/bin/bash
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
#
# Build and run the S-mode feasibility probe under QEMU.
#
# Must run inside the toolchain image (clang + qemu-system-riscv64):
#
#   docker run --rm -v "$PWD:/work" -w /work ghcr.io/vivoblueos/kernel:latest \
#     bash -lc 'tools/smode_probe/run.sh'
#
# Exit status is the probe's own verdict: 0 = every check passed.

set -euo pipefail

cd "$(dirname "$0")"

OUT="${OUT:-out}"
mkdir -p "$OUT"

# `-march=rv64ima` (no compressed encodings) so that "resume after the
# ecall" is always `mepc + 4` - the probe relies on that when it checks
# where the S-mode code resumes.
#
# The image's clang is an x86_64 host compiler, so the RISC-V target has to
# be named explicitly; there is no riscv64 GCC in the image.
CLANG="${CLANG:-clang}"
QEMU="${QEMU:-qemu-system-riscv64}"

"$CLANG" \
    --target=riscv64-unknown-elf \
    -march=rv64ima -mabi=lp64 -mcmodel=medany \
    -nostdlib -static \
    -Wl,-T,probe.ld -Wl,--build-id=none \
    -o "$OUT/smode_probe.elf" probe.S

# The probe ends by writing the sifive_test finisher register, which makes
# QEMU exit. The timeout is only a safety net in case the machine wedges
# before reaching that point. 60s rather than 30s because the Phase 1+2
# measurements arm a real timer and spin waiting for it.
set +e
timeout 60 "$QEMU" \
    -machine virt -m 128M -smp 1 -nographic -no-reboot \
    -bios none \
    -kernel "$OUT/smode_probe.elf" \
    2>&1 | tee "$OUT/smode_probe.log"
status="${PIPESTATUS[0]}"
set -e

# The verdict is the serial line: the message is what a reader checks, and
# it is reliable even if the finisher write did not stop QEMU.
#
# Six premises have to hold for the migration to be viable; each one prints
# its own line, so the log says exactly which of them failed.
#
# (A seventh check - whether the PLIC's S-mode context can be driven from
# S-mode - is deliberately not in this list: it decides *how* external
# interrupts get wired, not whether the migration is viable, so it reports
# its verdict in the log instead of failing the run.)
if grep -q "PROBE RESULT: PASS" "$OUT/smode_probe.log"; then
    echo "probe verdict: PASS"
    exit 0
fi
echo "probe verdict: FAIL (qemu exit status $status)"
echo "--- checks that did not report ---"
for line in \
    "S: ecall round-trip ok" \
    "S: stvec/sret delegated path ok" \
    "satp is effective" \
    "S: STIP delivered to S-mode" \
    "S: SBI set_timer closed the loop" \
    "S: satp switch window ok"; do
    grep -q "$line" "$OUT/smode_probe.log" \
        || echo "missing: $line"
done
exit 1
