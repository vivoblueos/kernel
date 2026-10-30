#!/bin/bash -e

cargo rustc --features map -- --test -C link-dead-code -Z profile -Z no-landing-pads

LCOVOPTS=(
  --gcov-tool llvm-gcov
  --rc lcov_branch_coverage=1
  --rc lcov_excl_line=assert
)
lcov "${LCOVOPTS[@]}" --capture --directory . --base-directory . \
  -o target/coverage/raw.lcov
lcov "${LCOVOPTS[@]}" --extract target/coverage/raw.lcov "$(pwd)/*" \
  -o target/coverage/raw_crate.lcov

genhtml --branch-coverage --demangle-cpp --legend \
  -o target/coverage/ \
  target/coverage/raw_crate.lcov
