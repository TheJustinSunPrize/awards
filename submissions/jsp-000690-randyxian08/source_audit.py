#!/usr/bin/env python3
"""Check literal transcription and disallowed proof shortcuts, not Lean typing.

This is deliberately not advertised as a Lean parser or theorem verifier.
A successful result is only a static consistency check for this source layout.
"""
from __future__ import annotations

import hashlib
import re
from pathlib import Path
from typing import Any


class AuditError(RuntimeError):
    """A source consistency check failed."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def without_comments(text: str) -> str:
    """Strip Lean line comments and nested block comments, respecting strings."""
    out: list[str] = []
    i, depth = 0, 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif quoted:
            ch = text[i]
            out.append(ch)
            i += 1
            if ch == '\\' and i < len(text):
                out.append(text[i])
                i += 1
            elif ch == '"':
                quoted = False
        elif text.startswith('/-', i):
            depth = 1
            out.append(' ')
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end == -1 else end
        else:
            ch = text[i]
            out.append(ch)
            quoted = ch == '"'
            i += 1
    require(depth == 0 and not quoted, 'Unclosed block comment or string')
    return ''.join(out)


def section(text: str, begin: str, end: str) -> str:
    require(text.count(begin) == 1, f'Expected exactly one marker: {begin}')
    first = text.index(begin)
    last = text.find(end, first + len(begin))
    require(last != -1, f'Missing closing marker: {end}')
    return text[first:last]


def numbers(value: str, offset: int = 0) -> tuple[int, ...]:
    return tuple(int(x.strip()) + offset for x in value.split(',') if x.strip())


def audit_source(path: Path, expected: dict[str, Any]) -> dict[str, Any]:
    raw = path.read_bytes()
    text = without_comments(raw.decode('utf-8'))
    forbidden = re.findall(
        r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|extern|ofReduceBool|sorryAx)\b',
        text,
    )
    require(not forbidden, f'Disallowed proof mechanism in source: {forbidden}')
    imports = re.findall(r'^import\s+(.+)$', text, re.MULTILINE)
    require(imports == ['Std'], f'Unexpected imports: {imports}')

    edge_section = section(text, 'def edges :', 'def H :')
    found_edges = [
        tuple(int(x) + 1 for x in match)
        for match in re.findall(
            r'⟨(\d+),\s*(\d+),\s*(\d+),\s*by decide,\s*by decide⟩',
            edge_section,
        )
    ]
    require(found_edges == expected['edges'], 'Lean edge list differs from audited witness')

    obstruction = section(text, 'private theorem binary_obstruction', 'theorem not_two_colorable')
    clauses = re.findall(r'\(x(\d+) ≠ x(\d+) ∨ x(\d+) ≠ x(\d+)\)', obstruction)
    require(all(a == c for a, _, c, _ in clauses), 'Malformed obstruction clause')
    clause_edges = [(int(a)+1, int(b)+1, int(d)+1) for a,b,_,d in clauses]
    require(clause_edges == expected['edges'], 'Obstruction clauses do not match the edges')
    require('∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 : Fin 2,' in obstruction,
            'Obstruction must quantify over all nine binary colors')

    blue_section = section(text, 'def edgeBlue', 'def blueColor')
    matches = re.findall(r'\| (\d+),\s*(\d+),\s*(\d+) => \[([^\]]*)\]', blue_section)
    found_blue = {
        (int(a)+1,int(b)+1,int(c)+1): numbers(values, 1)
        for a,b,c,values in matches
    }
    require(len(matches) == len(found_blue) == 22, 'Expected 22 unique edge certificates')
    require(found_blue == dict(zip(expected['edges'], expected['edge_blue'])),
            'Lean edge certificates differ from audited certificates')
    require('| _, _, _ => []' in blue_section, 'Unexpected edge-certificate default')

    vertex_section = section(text, 'def vertexBlue', 'theorem vertex_deletion_certificates')
    vertex_matches = re.findall(r'\| (\d+|_) => \[([^\]]*)\]', vertex_section)
    require([key for key,_ in vertex_matches] == [str(i) for i in range(8)]+['_'],
            'Unexpected vertex-certificate matching structure')
    found_vertex = [numbers(values,1) for _,values in vertex_matches]
    require(found_vertex == expected['vertex_blue'], 'Lean vertex certificates differ')

    color_section = section(text, 'def threeColor', 'theorem three_colorable')
    color_matches = re.findall(r'\| (\d+|_) => (\d+)', color_section)
    require([key for key,_ in color_matches] == [str(i) for i in range(8)]+['_'],
            'Unexpected three-color matching structure')
    found_three = {i+1:int(value) for i,(_,value) in enumerate(color_matches)}
    require(found_three == expected['three'], 'Lean three-color witness differs')

    return {
        'status': 'PASSED_STATIC_CONSISTENCY_CHECKS',
        'source_file': path.name,
        'source_sha256': hashlib.sha256(raw).hexdigest(),
        'source_lines': raw.count(b'\n'),
        'imports': imports,
        'edge_literals_checked': 22,
        'obstruction_clauses_checked': 22,
        'edge_certificate_literals_checked': 22,
        'vertex_certificate_literals_checked': 9,
        'three_color_values_checked': 9,
        'disallowed_proof_mechanisms_found': [],
        'limitation': 'Not a Lean parser, elaborator, kernel check, or semantic proof audit.',
    }
