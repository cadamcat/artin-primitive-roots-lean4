#!/usr/bin/env python3
"""Check the single axiom report emitted by Verification/Axioms.lean.

Lean wraps a long axiom list over several lines, so the report is parsed from the whole log, not line by line.
Exit 0: every axiom is in the permitted set. Exit 2: the theorem depends on sorryAx (an open proof).
Exit 1: any other failure (an unexpected axiom, no report, or more than one).
"""

from pathlib import Path
import re
import sys


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
OPEN = "sorryAx"
TARGET = "ArtinPrimitiveRootsConjecture.artin_primitive_roots_infinite"
REPORT = re.compile(r"'?([^\s']+)'? depends on axioms:\s*\[([^\]]*)\]")
NONE = re.compile(r"'?([^\s']+)'? does not depend on any axioms")


def main() -> int:
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} AXIOM_LOG", file=sys.stderr)
        return 1

    log = Path(sys.argv[1]).read_text(encoding="utf-8")
    reports = [(m.group(1), m.group(2)) for m in REPORT.finditer(log)]
    reports += [(m.group(1), "") for m in NONE.finditer(log)]
    if len(reports) != 1:
        print(f"expected one axiom report, found {len(reports)}", file=sys.stderr)
        return 1

    name, body = reports[0]
    if name != TARGET:
        print(f"axiom report is for {name}, not {TARGET}", file=sys.stderr)
        return 1

    axioms = {item.strip() for item in body.split(",") if item.strip()}
    print(f"Axioms for {TARGET}: {', '.join(sorted(axioms)) or '(none)'}")
    unexpected = axioms - ALLOWED - {OPEN}
    if unexpected:
        print(f"FAIL: unexpected axioms: {', '.join(sorted(unexpected))}", file=sys.stderr)
        return 1
    if OPEN in axioms:
        print(f"OPEN: {TARGET} depends on sorryAx; the proof is incomplete.")
        return 2

    print("PASS: all axioms are in the permitted set.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
