#!/usr/bin/env python3
"""Check that ArtinPrimitiveRoots/Target.lean states the theorem with the same text as Challenge.lean.

Compares, after removing comments and normalizing whitespace, the definition of `S` and the statement of
`artin_primitive_roots_infinite` up to its `:=`. Optional argument: the repository root (default: this script's parent directory).
Exit 0 if they agree, 1 otherwise.
"""
import re
import sys
from pathlib import Path

root = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent


def statement(path: Path) -> str:
    src = path.read_text(encoding='utf-8')
    src = re.sub(r'/-.*?-/', ' ', src, flags=re.S)
    src = re.sub(r'--[^\n]*', ' ', src)
    m = re.search(r'abbrev S\b.*?theorem artin_primitive_roots_infinite\s*:.*?:=', src, re.S)
    if m is None:
        sys.exit(f'{path}: statement not found')
    return ' '.join(m.group(0).split())


challenge = statement(root / 'Challenge.lean')
solution = statement(root / 'ArtinPrimitiveRoots' / 'Target.lean')
print('Challenge.lean:', challenge)
if challenge != solution:
    print('Target.lean:   ', solution)
    print('FAIL: the statement texts differ.')
    sys.exit(1)
print('PASS: Target.lean states S and the theorem with the same text.')
