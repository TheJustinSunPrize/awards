"""Small lexical helpers. These checks do NOT replace the Lean kernel."""
from __future__ import annotations

import re


def strip_comments_and_strings(text: str) -> str:
    """Preserve line breaks; remove nested Lean comments and quoted strings."""
    result: list[str] = []
    i, depth = 0, 0
    quoted = False
    while i < len(text):
        ch = text[i]
        pair = text[i:i + 2]
        if depth:
            if pair == '/-':
                depth += 1
                result.extend('  ')
                i += 2
            elif pair == '-/':
                depth -= 1
                result.extend('  ')
                i += 2
            else:
                result.append('\n' if ch == '\n' else ' ')
                i += 1
        elif quoted:
            if ch == '\\' and i + 1 < len(text):
                result.extend('  ')
                i += 2
            else:
                if ch == '"':
                    quoted = False
                result.append('\n' if ch == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            result.extend('  ')
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            if end == -1:
                result.append(' ' * (len(text) - i))
                break
            result.append(' ' * (end - i))
            i = end
        elif ch == '"':
            quoted = True
            result.append(' ')
            i += 1
        else:
            result.append(ch)
            i += 1
    if depth or quoted:
        raise ValueError('Unterminated comment or string')
    return ''.join(result)


def imported_modules(text: str) -> list[str]:
    stripped = strip_comments_and_strings(text)
    modules: list[str] = []
    for match in re.finditer(r'^\s*(?:public\s+)?import\s+([^\n]+)', stripped, re.M):
        for token in match.group(1).split():
            if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', token):
                raise ValueError(f'Unsupported import syntax: {token!r}')
            modules.append(token)
    return modules


def forbidden_constructs(text: str) -> list[str]:
    stripped = strip_comments_and_strings(text)
    return sorted(set(re.findall(
        r'\b(?:sorry|admit|axiom|native_decide|sorryAx)\b', stripped)))
