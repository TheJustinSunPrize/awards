#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"

mkdir -p evidence
lake env lean --version | tee evidence/toolchain.log
lake build 2>&1 | tee evidence/build.log
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
lake env leanchecker --fresh --verbose JSP301 2>&1 | tee evidence/kernel-replay.log

python3 - <<'PY'
from pathlib import Path
import re

expected = {
    'JSP000301.powerful_12167', 'JSP000301.powerful_12168',
    'JSP000301.not_isSquare_12167', 'JSP000301.not_isSquare_12168',
    'JSP000301.counterexample', 'JSP000301.claim_false',
}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
log = Path('evidence/axioms.log').read_text()
seen = set()
for theorem, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
    if theorem in expected:
        used = {x.strip() for x in axioms.split(',') if x.strip()}
        if not used <= allowed:
            raise SystemExit(f'Unexpected axioms for {theorem}: {sorted(used - allowed)}')
        seen.add(theorem)
if seen != expected:
    raise SystemExit(f'Missing axiom audit results: {sorted(expected - seen)}')
print('All six theorem axiom audits passed.')
PY

printf '%s\n' 'Local build, axiom audit, and fresh official-kernel replay passed.'
