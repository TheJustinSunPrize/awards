#!/usr/bin/env python3
"""Fetch just the pinned finite-proof import closure, without rewriting it.

Run locally with internet access. This script does not claim that any fetched
source is valid; verify.sh subsequently builds and audits the final theorem.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import sys
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

from common import forbidden_constructs, imported_modules

ROOT = Path(__file__).resolve().parents[1]
COMMIT = '8822f7ddef30fadbd92e1c6ab4ed897af356af5e'
REPO = 'plby/lean-proofs'
BASE = f'https://raw.githubusercontent.com/{REPO}/{COMMIT}/src/latest/'
LIBRARY_ROOTS = {
    'Mathlib', 'Lean', 'Init', 'Std', 'Batteries', 'Aesop', 'Qq',
    'ProofWidgets', 'ImportGraph', 'Plausible', 'Cli',
}
ALLOWED_SOURCE_ROOTS = {'ErdosProblems', 'Util'}
MAX_FILES = 512
MAX_FILE_BYTES = 8 * 1024 * 1024


def git_blob_sha1(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def validate_identity(data: bytes, expected: dict[str, object]) -> None:
    if (len(data) != expected['bytes'] or
            hashlib.sha256(data).hexdigest() != expected['sha256'] or
            git_blob_sha1(data) != expected['git_blob_sha1']):
        raise RuntimeError(f"Pinned source identity mismatch: {expected['path']}")


def download(path: str) -> bytes:
    req = Request(BASE + path, headers={'User-Agent': 'JSP000078-reproduction/0.1'})
    with urlopen(req, timeout=60) as response:
        data = response.read(MAX_FILE_BYTES + 1)
    if len(data) > MAX_FILE_BYTES:
        raise RuntimeError(f'Upstream source exceeds size limit: {path}')
    return data


def main() -> None:
    lock = json.loads((ROOT / 'upstream-lock.json').read_text(encoding='utf-8'))
    if lock['repository'] != REPO or lock['commit'] != COMMIT:
        raise RuntimeError('Upstream lock does not match the pinned repository and commit')
    locked = {entry['module']: entry for entry in lock['files']}
    if len(locked) != len(lock['files']):
        raise RuntimeError('Duplicate module in upstream lock')
    pending = ['ErdosProblems.Erdos58']
    seen: set[str] = set()
    records: list[dict[str, object]] = []
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        if len(seen) >= MAX_FILES:
            raise RuntimeError('Import closure exceeds the safety limit')
        seen.add(module)
        relative = module.replace('.', '/') + '.lean'
        expected = locked.get(module)
        if expected is None or expected['path'] != relative:
            raise RuntimeError(f'Module missing or inconsistent in upstream lock: {module}')
        destination = ROOT / relative
        if destination.exists():
            data = destination.read_bytes()
            validate_identity(data, expected)
        else:
            # A transient or truncated response must not be recorded as pinned source.
            for attempt in range(3):
                try:
                    data = download(relative)
                    validate_identity(data, expected)
                    break
                except (HTTPError, URLError, TimeoutError, OSError, RuntimeError):
                    if attempt == 2:
                        raise
        source = data.decode('utf-8')
        forbidden = forbidden_constructs(source)
        if forbidden:
            raise RuntimeError(f'Unverified constructs in {relative}: {forbidden}')
        imports = imported_modules(source)
        for dependency in imports:
            prefix = dependency.split('.')[0]
            if prefix in LIBRARY_ROOTS:
                continue
            if prefix not in ALLOWED_SOURCE_ROOTS:
                raise RuntimeError(
                    f'Additional dependency {dependency!r} in {relative}. '
                    'Stop rather than silently change the dependency graph.')
            pending.append(dependency)
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not destination.exists():
            destination.write_bytes(data)
        records.append({
            'module': module, 'path': relative,
            'source': BASE + relative, 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest(),
            'git_blob_sha1': git_blob_sha1(data), 'imports': imports,
        })
        print(f'Verified pinned source: {module}', flush=True)
    if seen != set(locked):
        raise RuntimeError('Import closure differs from upstream lock')
    report = {
        'repository': REPO, 'commit': COMMIT,
        'lean_validation': 'NOT_PERFORMED_BY_THIS_SCRIPT',
        'files': sorted(records, key=lambda item: str(item['module'])),
    }
    target = ROOT / 'verification' / 'upstream-manifest.json'
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(f'Saved {len(records)} source files; none has been kernel-verified yet.')


if __name__ == '__main__':
    try:
        main()
    except (HTTPError, URLError, TimeoutError, OSError, UnicodeError, ValueError, RuntimeError) as error:
        print(f'ERROR: {error}', file=sys.stderr)
        sys.exit(1)
