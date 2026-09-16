#!/usr/bin/env bash
# Reproduce the JSP-001007 formalization check from a clean checkout.
set -euo pipefail
cd "$(dirname "$0")"
echo "==> toolchain: $(cat lean-toolchain)"
lake exe cache get
lake build
audit_file="$(mktemp)"
trap 'rm -f -- "$audit_file"' EXIT
lake env lean AxiomAudit.lean | tee "$audit_file"
python3 - "$audit_file" <<'PY'
import re
import sys
from pathlib import Path
text = Path(sys.argv[1]).read_text()
expected = {
    'JSP001007.counterexample_core', 'JSP001007.primeCount_lower',
    'JSP001007.clustering', 'JSP001007.green44_counterexample',
    'JSP001007.not_green44_conjecture',
}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
found = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text))
assert set(found) == expected, 'The final theorem audit is incomplete.'
for name, axioms in found.items():
    actual = {a.strip() for a in axioms.split(',') if a.strip()}
    assert actual <= allowed, f'Unexpected axioms in {name}: {actual - allowed}'
print('OK: all five theorem axiom audits passed')
PY
echo "==> searching for placeholders (must be empty)"
if grep -rnE '\b(sorry|admit|native_decide|axiom)\b' Jsp/*.lean Jsp.lean | grep -vE '^[^:]+:[0-9]+:[[:space:]]*(\*|--|/)'; then
  echo "FAIL: placeholder or extra axiom found"; exit 1
fi
echo "OK: no sorry/admit/native_decide/axiom"
