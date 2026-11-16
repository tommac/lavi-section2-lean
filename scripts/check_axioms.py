#!/usr/bin/env python3
"""Check the output of `lake env lean AxiomAudit.lean`.

Usage: python3 scripts/check_axioms.py AxiomAudit.lean axioms.txt

Fails unless
* the output contains no errors,
* every `#print axioms` line of AxiomAudit.lean produced exactly one report, and
* every report lists only Lean's standard axioms (propext, Classical.choice, Quot.sound).

This is an allowlist: `sorryAx`, the auxiliary axioms of `native_decide`, and any
project-defined axiom all fail it.  Reports may wrap across several lines.
"""
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main(audit_path: str, output_path: str) -> int:
    with open(audit_path, encoding="utf-8") as f:
        expected = sum(1 for line in f if line.lstrip().startswith("#print axioms"))
    with open(output_path, encoding="utf-8") as f:
        text = f.read()

    errors = [line for line in text.splitlines() if "error" in line.lower()]
    reports = re.findall(r"'(.+?)' depends on axioms: \[([^\]]*)\]", text, flags=re.S)
    no_axioms = re.findall(r"'(.+?)' does not depend on any axioms", text)
    bad = []
    for name, axioms in reports:
        used = {a.strip() for a in axioms.split(",") if a.strip()}
        if not used <= ALLOWED:
            bad.append((name, sorted(used - ALLOWED)))

    total = len(reports) + len(no_axioms)
    print(f"{total} axiom reports for {expected} '#print axioms' lines; "
          f"{len(bad)} with axioms outside {sorted(ALLOWED)}; {len(errors)} error lines")
    for name, extra in bad:
        print(f"NOT ALLOWED: {name} uses {', '.join(extra)}")
    for line in errors:
        print(f"ERROR: {line}")
    return 1 if (errors or bad or total != expected) else 0


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    sys.exit(main(sys.argv[1], sys.argv[2]))
