"""Small lexical helpers for source screening, not a Lean parser or proof checker."""
from __future__ import annotations
import re


def strip_comments(text: str, *, keep_strings: bool = False) -> str:
    """Remove nested Lean comments and, by default, strings; preserve newlines."""
    out: list[str] = []
    i = depth = 0
    line_comment = string = False
    while i < len(text):
        if line_comment:
            if text[i] == '\n':
                line_comment = False
                out.append('\n')
            else:
                out.append(' ')
            i += 1
        elif depth:
            if text.startswith('/-', i):
                depth += 1; out.extend('  '); i += 2
            elif text.startswith('-/', i):
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            c = text[i]
            out.append(c if keep_strings else ('\n' if c == '\n' else ' '))
            if c == '\\' and i + 1 < len(text):
                i += 1
                out.append(text[i] if keep_strings else ' ')
            elif c == '"':
                string = False
            i += 1
        elif text.startswith('--', i):
            line_comment = True; out.extend('  '); i += 2
        elif text.startswith('/-', i):
            depth = 1; out.extend('  '); i += 2
        elif text[i] == '"':
            string = True; out.append('"' if keep_strings else ' '); i += 1
        else:
            out.append(text[i]); i += 1
    if depth or string:
        raise ValueError('Unterminated Lean block comment or string')
    return ''.join(out)


def imports(text: str) -> list[str]:
    result: list[str] = []
    for line in strip_comments(text).splitlines():
        match = re.match(r'^\s*(?:(?:public|private)\s+)?import\s+(.+?)\s*$', line)
        if match:
            for name in match.group(1).split():
                if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_0-9]+)*', name):
                    raise ValueError(f'Unsupported import syntax: {line!r}')
                result.append(name)
    return result
