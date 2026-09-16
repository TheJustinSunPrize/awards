#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
mapfile -d '' lean_sources < <(find . -path './.lake' -prune -o -type f -name '*.lean' -print0)
if [[ ${#lean_sources[@]} -eq 0 ]]; then
  echo 'no Lean source files found' >&2
  exit 1
fi
for token in sorry admit sorryAx native_decide unsafe; do
  if grep -HniE "(^|[^[:alnum:]_])${token}([^[:alnum:]_]|$)" "${lean_sources[@]}"; then
    echo "forbidden token: ${token}" >&2
    exit 1
  fi
done
lake build
lake env lean ErdosProblems/Erdos92.lean
lake env lean JSP000108.lean
