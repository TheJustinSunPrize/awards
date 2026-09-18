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
lake env lean JSP000884.lean

axioms_file=.verification-axioms.lean
trap 'rm -f -- "$axioms_file"' EXIT
cat >"$axioms_file" <<'EOF'
import JSP000884
#print axioms JSP000884.solution
#print axioms Erdos1064.erdos_1064
#print axioms Erdos1064.erdos_1064.variants.k2
#print axioms Erdos1064.erdos_1064.variants.general_function
EOF
axioms_output=$(lake env lean "$axioms_file")
printf '%s\n' "$axioms_output"
if grep -Eiq 'sorryAx|Lean\.ofReduceBool|unsafe' <<<"$axioms_output"; then
  echo 'forbidden axiom or evaluator escape in axiom report' >&2
  exit 1
fi
