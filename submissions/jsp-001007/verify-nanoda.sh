#!/usr/bin/env bash
# Requires git, cargo, and the pinned Lean toolchain through elan.
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
check_dir="$(mktemp -d "${TMPDIR:-/tmp}/jsp-001007-check.XXXXXX")"
printf 'Checker workspace: %s\n' "$check_dir"
git clone https://github.com/leanprover/lean4export.git "$check_dir/export"
git -C "$check_dir/export" checkout --detach fd0d78eaa91750096cf519907b266efb1b26bf22
cp "$project_dir/lean-toolchain" "$check_dir/export/lean-toolchain"
(cd "$check_dir/export" && lake build)
git clone https://github.com/ammkrn/nanoda_lib.git "$check_dir/nanoda"
git -C "$check_dir/nanoda" checkout --detach 4c544ed4099c8227f07d5de77ad1e69fb0740a27
(cd "$check_dir/nanoda" && cargo build --release --locked)
cd "$project_dir"
lake build
lake env "$check_dir/export/.lake/build/bin/lean4export" Jsp.Jsp001007Conclusion -- \
  JSP001007.green44_counterexample JSP001007.not_green44_conjecture \
  > "$check_dir/jsp-001007-proof.ndjson"
cp evidence/nanoda-config.json "$check_dir/nanoda-config.json"
(cd "$check_dir" && ./nanoda/target/release/nanoda_bin nanoda-config.json)
printf 'Independent check succeeded; export retained in %s\n' "$check_dir"
