#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
submission_dir="$PWD"
proof_commit="46f55ea4192231736bd8ecbdfc5eec8b3104d018"
proof_repo="https://github.com/wentAInx/jsp-000971-erdos-1166.git"
proof_checkout="$(mktemp -d "${TMPDIR:-/tmp}/jsp000971-review.XXXXXX")"
printf 'Proof checkout: %s\n' "$proof_checkout"
git -C "$proof_checkout" init -q
git -C "$proof_checkout" remote add origin "$proof_repo"
git -C "$proof_checkout" fetch --depth=1 origin "$proof_commit"
git -C "$proof_checkout" checkout --detach FETCH_HEAD
test "$(git -C "$proof_checkout" rev-parse HEAD)" = "$proof_commit"
for module in Counting Checks MaximumCover LogTailNumerics ProbabilityAssembly DefinitionBridge RandomWalkCover MaximumLog Final; do
  cmp "$submission_dir/$module.lean" "$proof_checkout/$module.lean"
done
cd "$proof_checkout"
lake exe cache get
RUN_KERNEL_REPLAY=1 LEAN_NUM_THREADS=1 bash verify.sh
