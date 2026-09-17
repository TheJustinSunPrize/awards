#!/usr/bin/env python3
"""Verify the delivered files against SHA256SUMS; not a proof checker."""
import hashlib
from pathlib import Path
import sys
root=Path(__file__).resolve().parents[1]
errors=[]
count=0
for line in (root/'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ',1)
    p=(root/name).resolve()
    count+=1
    if not p.is_relative_to(root) or not p.is_file():
        errors.append(f'Missing or unsafe path: {name}')
    elif hashlib.sha256(p.read_bytes()).hexdigest()!=digest:
        errors.append(f'Hash mismatch: {name}')
if errors:
    print('\n'.join(errors),file=sys.stderr)
    raise SystemExit(1)
print(f'Integrity OK: {count} files. This does not check Lean proofs.')
