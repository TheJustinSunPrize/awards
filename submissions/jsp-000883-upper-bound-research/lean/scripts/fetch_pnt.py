#!/usr/bin/env python3
"""Fetch ONLY the pinned local PNT source closure, verifying every Git blob.

This downloads source dependencies; it does not verify mathematical correctness.
It does not modify mathlib, remove proof obligations, or replace failures with axioms.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import os
import tempfile
import hashlib
import json
from pathlib import Path, PurePosixPath
import time
import urllib.error
import urllib.request
from lean_source import imports

ROOT = Path(__file__).resolve().parents[1]
REPO = 'plby/lean-proofs'
COMMIT = '8822f7ddef30fadbd92e1c6ab4ed897af356af5e'
# Tree identity observed at src/latest/PrimeNumberTheoremAnd in this commit.
TREE = 'b9f65ffdf398be0170db7a21de3a635f32d887b5'
PREFIX = 'PrimeNumberTheoremAnd'
ENTRY = PREFIX + '.Consequences'
KNOWN_ENTRY_BLOB = '167d52c19bdba66c37fa766415c3bd73105376b0'


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def read_url(url: str, limit: int = 25_000_000) -> bytes:
    last: Exception | None = None
    for attempt in range(3):
        try:
            req = urllib.request.Request(url, headers={'User-Agent': 'JSP000883-source-fetch/0.2.1', 'Cache-Control': 'no-cache'})
            with urllib.request.urlopen(req, timeout=45) as response:
                data = response.read(limit + 1)
            if len(data) > limit:
                raise ValueError(f'Source response exceeds {limit} bytes: {url}')
            return data
        except (urllib.error.URLError, TimeoutError) as exc:
            last = exc
            if attempt < 2:
                time.sleep(attempt + 1)
    raise RuntimeError(f'Could not fetch {url}: {last}')


def read_verified_url(url: str, expected_size: int, expected_blob: str, *,
                      attempts: int = 3, records: list[dict] | None = None) -> bytes:
    """Retry transient wrong-byte responses, but NEVER relax the pinned identity.

    The attempt receipt contains observed byte counts and hashes. Content is
    not written to the project unless both expected size and Git blob match.
    """
    if attempts < 1 or expected_size < 0:
        raise ValueError('Invalid source verification retry parameters')
    last: str = 'no response'
    for attempt in range(1, attempts + 1):
        record = {'url': url, 'attempt': attempt, 'expected_bytes': expected_size,
                  'expected_git_blob': expected_blob,
                  'started_at': datetime.now(timezone.utc).isoformat()}
        try:
            data = read_url(url)
        except (RuntimeError, urllib.error.URLError, TimeoutError, ValueError) as exc:
            record.update(status='transport_error', error=str(exc))
            last = str(exc)
        else:
            actual_blob = git_blob(data)
            ok = len(data) == expected_size and actual_blob == expected_blob
            record.update(observed_bytes=len(data), observed_git_blob=actual_blob,
                          observed_sha256=hashlib.sha256(data).hexdigest(),
                          status='identity_match' if ok else 'identity_mismatch')
            if records is not None:
                records.append(record)
            if ok:
                return data
            last = (f'expected {expected_size} bytes / {expected_blob}; '
                    f'observed {len(data)} bytes / {actual_blob}')
            if attempt < attempts:
                time.sleep(attempt)
            continue
        if records is not None:
            records.append(record)
        if attempt < attempts:
            time.sleep(attempt)
    raise ValueError(f'Pinned source identity/transport check failed after {attempts} attempts: '
                     f'{url}; {last}')


def write_atomic(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(prefix=path.name + '.', suffix='.tmp', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as stream:
            stream.write(data)
        Path(name).replace(path)
    finally:
        Path(name).unlink(missing_ok=True)


def fetch() -> dict:
    receipts: list[dict] = []
    status = 'failed'
    try:
        result = _fetch(receipts)
        status = 'source_identity_checked_not_proof_verified'
        return result
    finally:
        stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
        report = {'repository': REPO, 'commit': COMMIT, 'status': status,
                  'attempts': receipts,
                  'note': 'HTTP-source identity observations, not a Lean build.'}
        out = ROOT / 'evidence' / 'pnt-fetch-attempts' / (stamp + '.json')
        write_atomic(out, (json.dumps(report, indent=2) + '\n').encode())


def _fetch(receipts: list[dict]) -> dict:

    tree_url = f'https://api.github.com/repos/{REPO}/git/trees/{TREE}?recursive=1'
    tree_data = read_url(tree_url)
    tree = json.loads(tree_data)
    if tree.get('sha') != TREE or tree.get('truncated') is not False:
        raise ValueError('Wrong or truncated PNT tree; refusing incomplete dependency pinning')
    entries = {x['path']: x for x in tree['tree'] if x.get('type') == 'blob'}
    if entries.get('Consequences.lean', {}).get('sha') != KNOWN_ENTRY_BLOB:
        raise ValueError('PNT entry file no longer matches the pinned Git blob')
    pending = [ENTRY]
    seen: set[str] = set()
    records: list[dict] = []
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        if not module.startswith(PREFIX + '.'):
            raise ValueError(f'Unexpected local source namespace: {module}')
        rel = module[len(PREFIX) + 1:].replace('.', '/') + '.lean'
        if '..' in PurePosixPath(rel).parts or rel not in entries:
            raise ValueError(f'Import has no pinned source in the PNT tree: {module}')
        entry = entries[rel]
        dest = ROOT / PREFIX / rel
        url = f'https://raw.githubusercontent.com/{REPO}/{COMMIT}/src/latest/{PREFIX}/{rel}'
        if dest.exists() and git_blob(dest.read_bytes()) == entry['sha']:
            data = dest.read_bytes()
        else:
            data = read_verified_url(url, entry['size'], entry['sha'], records=receipts)
        if len(data) != entry['size'] or git_blob(data) != entry['sha']:
            raise ValueError(f'Pinned source identity check failed: {module}; '
                             f'expected {entry["size"]} bytes / {entry["sha"]}; '
                             f'observed {len(data)} bytes / {git_blob(data)}')
        text = data.decode('utf-8')
        deps = imports(text)
        for dep in deps:
            if dep.startswith(PREFIX + '.'):
                pending.append(dep)
            elif dep == 'Mathlib' or dep.startswith(('Mathlib.', 'Batteries.', 'Aesop.',
                                                     'Lean.', 'Std.', 'Qq.', 'Plausible.')):
                pass
            elif dep in {'Batteries', 'Aesop', 'Lean', 'Std', 'Qq', 'Plausible'}:
                pass
            else:
                raise ValueError(f'Unrecognized dependency {dep!r} in {module}; no silent omission')
        write_atomic(dest, data)
        records.append({'module': module, 'path': str(dest.relative_to(ROOT)),
                        'git_blob': entry['sha'], 'bytes': len(data),
                        'sha256': hashlib.sha256(data).hexdigest(),
                        'url': url, 'imports': deps})
        print(f'SOURCE IDENTITY OK {module}', flush=True)
    # Check that all imported local modules were actually fetched.
    for record in records:
        for dep in record['imports']:
            if dep.startswith(PREFIX + '.') and dep not in seen:
                raise ValueError(f'Missing transitive import: {dep}')
    result = {'repository': REPO, 'commit': COMMIT, 'tree': TREE, 'entry': ENTRY,
              'status': 'source_identity_checked_not_proof_verified',
              'files': sorted(records, key=lambda x: x['module'])}
    out = ROOT / 'evidence' / 'pnt-source-manifest.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + '\n')
    (ROOT / 'evidence' / 'pnt-tree.json').write_bytes(tree_data)
    print(f'Fetched {len(records)} source modules. This is NOT a Lean build.')
    return result


if __name__ == '__main__':
    argparse.ArgumentParser(description=__doc__).parse_args()
    try:
        fetch()
    except Exception as exc:
        raise SystemExit(f'PNT SOURCE FETCH FAILED: {exc}')
