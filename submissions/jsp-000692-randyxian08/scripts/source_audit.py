#!/usr/bin/env python3
"""Source-only checks. PASS here never means Lean compiled the project."""
from __future__ import annotations
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    'Hypergraph', 'SplitGadget', 'AlonCore', 'AlonGeometry', 'Relabel',
    'AlonGrowth', 'LinearIntersection', 'Complete',
]
FORBIDDEN = re.compile(r'\b(?:sorry|admit|axiom|unsafe|native_decide|sorryAx)\b|Lean\.ofReduceBool')


def strip_comments_and_strings(text: str) -> str:
    result = []
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1; i += 2
            elif text.startswith('-/', i):
                depth -= 1; i += 2
            else:
                if text[i] == '\n': result.append('\n')
                i += 1
        elif string:
            if text[i] == '\\': i += 2
            elif text[i] == '"': string = False; i += 1
            else: i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        elif text.startswith('/-', i):
            depth = 1; i += 2
        elif text[i] == '"':
            string = True; i += 1
        else:
            result.append(text[i]); i += 1
    if depth or string:
        raise ValueError('unterminated block comment or string')
    return ''.join(result)


def theorem_names() -> list[str]:
    out = []
    for module in MODULES:
        source = strip_comments_and_strings((ROOT/f'JSP692/{module}.lean').read_text())
        out += ['JSP692.' + x for x in re.findall(r'\b(?:theorem|lemma)\s+([\w.]+)', source)]
    if len(out) != len(set(out)):
        raise ValueError('duplicate theorem name')
    return out


def check_delimiters(text: str):
    stack = []
    pairs = {')':'(', ']':'[', '}':'{', '⟩':'⟨'}
    for pos, char in enumerate(text):
        if char in '([{⟨': stack.append((char, pos))
        elif char in pairs:
            if not stack or stack[-1][0] != pairs[char]:
                raise ValueError(f'unmatched delimiter {char} at {pos}')
            stack.pop()
    if stack: raise ValueError(f'unclosed delimiters: {stack}')


def assemble() -> None:
    names = theorem_names()
    header = '''import Mathlib

/-!
JSP-000692 / Erdos 836: BOTH questions, on shared definitions.
COMPLETE CANDIDATE SOURCE; compilation status is in verification/status.json.
This standalone file is generated from the eight module files.
-/

'''
    bodies = []
    for m in MODULES:
        s = (ROOT/f'JSP692/{m}.lean').read_text()
        s = re.sub(r'^import .*\n', '', s, flags=re.M)
        bodies.append(f'/- ===== Module: {m} ===== -/\n' + s)
    audits = '\n'.join('#print axioms ' + n for n in names) + '\n'
    (ROOT/'JSP000692.lean').write_text(header + '\n'.join(bodies) + '\n' + audits)
    (ROOT/'Audit.lean').write_text('import JSP692\n\n' + audits)
    (ROOT/'Statement.lean').write_text('''import JSP692
#print JSP692.Uniform
#print JSP692.Intersecting
#print JSP692.Proper
#print JSP692.ThreeChromatic
#print JSP692.support
#print JSP692.QuadraticVertexBound
#print JSP692.LinearIntersectionAssertion
#check JSP692.jsp000692_complete
#check JSP692.jsp000692_complete_explicit
''')


def audit() -> dict:
    assemble()
    files = [ROOT/f'JSP692/{m}.lean' for m in MODULES]
    files += [ROOT/'JSP692.lean', ROOT/'Audit.lean', ROOT/'Statement.lean', ROOT/'JSP000692.lean']
    violations = []
    for path in files:
        text = strip_comments_and_strings(path.read_text())
        for match in FORBIDDEN.finditer(text):
            violations.append({'file': str(path.relative_to(ROOT)), 'token': match.group()})
        check_delimiters(text)
    names = theorem_names()
    report = {
        'status': 'PASS' if not violations else 'FAIL',
        'evidence_type': 'SOURCE_TEXT_ONLY_NOT_COMPILATION',
        'module_order': MODULES, 'theorems_requested_for_kernel_audit': names,
        'theorem_count': len(names),
        'module_source_lines': sum(len(p.read_text().splitlines()) for p in files[:len(MODULES)]),
        'standalone_source_lines': len((ROOT/'JSP000692.lean').read_text().splitlines()),
        'forbidden_tokens': violations,
        'delimiters_balanced': True,
        'sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
    }
    (ROOT/'verification').mkdir(exist_ok=True)
    (ROOT/'verification/source-audit.json').write_text(json.dumps(report, indent=2)+'\n')
    return report

if __name__ == '__main__':
    result = audit()
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['status'] == 'PASS' else 1)
