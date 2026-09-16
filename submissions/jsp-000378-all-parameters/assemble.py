#!/usr/bin/env python3
"""Deterministically assemble the reviewed modules without changing proof bodies."""
from pathlib import Path
import hashlib, json
root = Path(__file__).resolve().parent
order = ['Erdos466Definitions', 'Erdos466Arithmetic', 'Erdos466EndpointArithmetic', 'Erdos466Endpoint', 'Erdos466Construction', 'Erdos466General']
imports, bodies, manifest = [], [], []
for module in order:
    path = root / 'source-components' / (module + '.lean')
    raw = path.read_bytes()
    manifest.append({'file': str(path.relative_to(root)), 'sha256': hashlib.sha256(raw).hexdigest()})
    body = []
    for line in raw.decode().splitlines(keepends=True):
        if line.startswith('import '):
            dependency = line.strip().split(' ', 1)[1]
            if dependency not in order and dependency not in imports:
                imports.append(dependency)
        else:
            body.append(line)
    bodies.append('/- Component: ' + module + ' -/\n' + ''.join(body))
header = '''/-
JSP-000378 / Erdős 466: full separation-parameter classification.
Canonical self-contained source, assembled from the attributed components.
Graham's construction and the Graham--Rothschild--Straus obstruction are classical.
This artifact contributes a formalization extension; it does not claim new mathematics.
See ATTRIBUTION.md and LICENSE (Apache-2.0).
-/
'''
text = header + '\n'.join('import ' + d for d in imports) + '\n\n' + '\n\n'.join(bodies)
(root / 'Erdos466.lean').write_text(text)
(root / 'assembly.json').write_text(json.dumps({'imports': imports, 'inputs': manifest, 'output_sha256':hashlib.sha256(text.encode()).hexdigest()},indent=2)+'\n')
