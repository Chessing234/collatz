#!/usr/bin/env python3
"""Conservative lexical screen; compiled endpoint axiom audits remain essential.

Mask comments and literal strings while preserving source positions. If a file
contains a potential interpolated string, preserve all its non-comment text:
interpolation can embed Lean terms, so treating it as inert prose is unsafe.
This is a policy screen, not a replacement for parsing or kernel verification.
"""
import re
import sys
from pathlib import Path

FORBIDDEN = re.compile(
    r'\b(sorry|sorryAx|axiom|native_decide|ofReduceBool|skipKernelTC|byAsSorry|'
    r'addDecl|addAndCompile|mkProj|ofReduceNat|evalConst|Lean\.Elab\.Command\.liftCoreM)\b'
    r'|^\s*((private|protected|noncomputable|scoped)\s+)*(admit|unsafe|partial|opaque)(\s|$)'
    r'|@\[(implemented_by|extern)', re.MULTILINE)
RAW = re.compile(r'r(#+)?"')
CHAR = re.compile(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|.)|[^'\\\n])'")


def code_only(text):
    # Retain the whole file in this uncommon case. This intentionally allows
    # false positives instead of hiding proof code in an interpolation hole.
    if re.search(r'!\s*(?:r#*)?"', text):
        return text
    out = list(text)

    def mask(a, b):
        for k in range(a, b):
            if out[k] != '\n':
                out[k] = ' '

    i = 0
    while i < len(text):
        start = i
        if text.startswith('/-', i):
            depth, i = 1, i+2
            while i < len(text) and depth:
                if text.startswith('/-', i):
                    depth, i = depth+1, i+2
                elif text.startswith('-/', i):
                    depth, i = depth-1, i+2
                else:
                    i += 1
            mask(start, i)
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
            mask(start, i)
        elif text[i] == "'" and (match := CHAR.match(text, i)):
            i = match.end()
            mask(start, i)
        elif ((i == 0 or not (text[i-1].isalnum() or text[i-1] in "_'"))
              and (match := RAW.match(text, i))):
            delimiter = '"' + (match.group(1) or '')
            end = text.find(delimiter, match.end())
            i = len(text) if end < 0 else end+len(delimiter)
            mask(start, i)
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i = min(i+2, len(text))
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            mask(start, i)
        else:
            i += 1
    return ''.join(out)


def violations(text):
    return [(number, match.group(0).strip())
            for number, line in enumerate(code_only(text).splitlines(), 1)
            for match in FORBIDDEN.finditer(line)]


def main():
    root = Path(__file__).resolve().parents[1]
    paths = sorted((root / 'Collatz').rglob('*.lean')) + [root / 'Collatz.lean']
    failed = False
    for path in paths:
        for line, token in violations(path.read_text()):
            print(f'{path.relative_to(root)}:{line}: {token}')
            failed = True
    if failed:
        raise SystemExit(1)
    print(f'Proof-escape screen passed for {len(paths)} Lean files.')


if __name__ == '__main__':
    main()
