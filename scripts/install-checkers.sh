#!/usr/bin/env bash
set -euo pipefail

# Tool pins are deliberate. Exporter source follows the v4.33 release line and is built
# with this project's exact toolchain. Comparator retains its own newer toolchain.
task_root=$(pwd)
mkdir -p .ci
git clone https://github.com/leanprover/lean4export.git .ci/lean4export
git -C .ci/lean4export checkout 15f6055e299ad5b89345e533cc2192f4cc00f659
cp lean-toolchain .ci/lean4export/lean-toolchain
(cd .ci/lean4export && lake build lean4export)

git clone https://github.com/leanprover/comparator.git .ci/comparator
git -C .ci/comparator checkout 2312244ac716564a61cc0bf4e107d9abf1757a61
(cd .ci/comparator && lake build comparator)

git clone https://github.com/robsimmons/nanoda_lib.git .ci/nanoda
git -C .ci/nanoda checkout 68d5ca9db226849b41a6fff59d796ff19d0a8840
(cd .ci/nanoda && cargo build --release --locked)

GOBIN="$task_root/.ci/bin" go install \
  github.com/zouuup/landrun/cmd/landrun@5ed4a3db3a4ad930d577215c6b9abaa19df7f99f

if [[ -n "${GITHUB_PATH:-}" ]]; then
  for tool_path in .ci/lean4export/.lake/build/bin .ci/comparator/.lake/build/bin \
      .ci/nanoda/target/release .ci/bin; do
    echo "$task_root/$tool_path" >> "$GITHUB_PATH"
  done
fi
