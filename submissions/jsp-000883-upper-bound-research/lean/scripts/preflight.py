"""Repository-specific regression checks. Not a Lean parser or proof checker."""
from __future__ import annotations
import json
from pathlib import Path
import re
import tomllib
from lean_source import strip_comments

PACKAGE_NAME = 'jsp000883_product_proof'
MATHLIB_REV = 'db584cd6d46c92f209a44c0f1c829460d327499d'
TOOLCHAIN = 'leanprover/lean4:v4.33.0'


def config_gate(root: Path) -> dict:
    cfg = tomllib.loads((root / 'lakefile.toml').read_text())
    lock = json.loads((root / 'lake-manifest.json').read_text())
    # This project chooses a simple, unescaped Lean Name. This is not a general
    # specification of all identifiers accepted by Lake.
    if cfg.get('name') != PACKAGE_NAME or lock.get('name') != PACKAGE_NAME:
        raise ValueError(f'Lake root names must both be {PACKAGE_NAME!r}')
    if (root / 'lean-toolchain').read_text().strip() != TOOLCHAIN:
        raise ValueError('Wrong pinned Lean toolchain')
    requirements = [p for p in cfg.get('require', []) if p.get('name') == 'mathlib']
    if len(requirements) != 1 or requirements[0].get('rev') != MATHLIB_REV:
        raise ValueError('Wrong pinned Mathlib requirement')
    if lock.get('packagesDir') != '.lake/packages':
        raise ValueError('Unexpected dependency directory')
    packages = lock.get('packages', [])
    names = [p.get('name') for p in packages]
    if len(names) != len(set(names)):
        raise ValueError('Duplicate dependency name')
    if not packages or not all(isinstance(n, str) and re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', n)
                               for n in names):
        raise ValueError('Missing or unsafe dependency name')
    if not all(re.fullmatch(r'[0-9a-f]{40}', p.get('rev', '')) for p in packages):
        raise ValueError('Each dependency must have an immutable commit revision')
    matches = [p for p in packages if p['name'] == 'mathlib']
    if len(matches) != 1 or matches[0]['rev'] != MATHLIB_REV:
        raise ValueError('Wrong pinned Mathlib manifest entry')
    return {'status': 'configuration_screen_only', 'name': PACKAGE_NAME,
            'toolchain': TOOLCHAIN, 'dependency_revisions': {p['name']: p['rev'] for p in packages}}


def arithmetic_regression_gate(root: Path) -> dict:
    clean = strip_comments((root / 'JSP000883/Arithmetic.lean').read_text())
    if not re.search(r'^set_option\s+autoImplicit\s+false\s*$', clean, re.M):
        raise ValueError('Arithmetic must disable implicit undeclared binders')
    # Reject only the exact erroneous forms seen in the v0.2 review. This is
    # intentionally not advertised as a general mathematical-syntax checker.
    unsafe = re.compile(r'∏\s+j\s+∈[^,\n]+,\s*m\s*[+-]\s*j\b')
    if unsafe.search(clean):
        raise ValueError('Known unparenthesized additive product body')
    if 'Finset.not_mem_erase' in clean:
        raise ValueError('Obsolete Finset.not_mem_erase API')
    return {'status': 'known_regressions_screened_not_elaborated'}
