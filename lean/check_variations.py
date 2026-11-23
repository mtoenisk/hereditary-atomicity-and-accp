#!/usr/bin/env python3
"""Check the section 9 statement map and its dated manuscript source."""

import argparse
from hashlib import sha256
from pathlib import Path
import re
import sys

# Checking an extracted source archive should leave its inventory unchanged.
sys.dont_write_bytecode = True

from check_map import LEAN_NAME, check_declarations


ROOT = Path(__file__).resolve().parent
DIGEST = "a43912b88130e84f3d98e9ab846112fee3327bf3e303a4193f7d3bfd41bd49b9"
HEADINGS = (
    "Krull dimension and absolute transcendence degree",
    "Two chains witnessing failure of weak ACCP",
    "A pair without a maximal common divisor",
)


# Entries already covered by the typed package and the dated map.
REQUIRED = {
    HEADINGS[0]: {"Boundary dimensions", "Principal chains", "Absolute transcendence degree", "Prescribed dimensions", "One-dimensional plane example"},
    HEADINGS[1]: {"Original domain", "Two chains", "Chain criterion", "Conductor transfer",
                  "Two-centre divisor bounds"},
    HEADINGS[2]: {"Dyadic counterexample", "Dyadic mass and stabilization", "Explicit pair", "Coprime splitting", "Maximal common divisors"},
}


def mapped_rows():
    source = (ROOT / "SECTION9.md").read_text()
    if source.count(DIGEST) != 1:
        raise ValueError("Unexpected manuscript hash in the section 9 map")
    expected = [f"## §9.{i}. {title}" for i, title in enumerate(HEADINGS, 1)]
    if [line for line in source.splitlines() if line.startswith("## ")] != expected:
        raise ValueError("The section 9 map must follow the three manuscript headings")
    rows = []
    seen = {heading: set() for heading in HEADINGS}
    section = None
    for line in source.splitlines():
        if line in expected:
            section = HEADINGS[expected.index(line)]
        if not line.startswith("| ") or line.startswith(("| Result |", "| ---")):
            continue
        cells = [cell.strip() for cell in line.strip("|").split("|")]
        if len(cells) != 3:
            raise ValueError(f"Malformed section 9 row: {line}")
        label, statement, references = cells
        names = re.findall(r"`([^`]+)`", references)
        if not names or not statement or any(not LEAN_NAME.fullmatch(n) for n in names):
            raise ValueError(f"Missing statement or invalid Lean name: {line}")
        if section is None or label in seen[section]:
            raise ValueError(f"Misplaced or duplicate section 9 entry: {label}")
        seen[section].add(label)
        rows.append((label, statement, names))
    for heading, required in REQUIRED.items():
        if missing := required - seen[heading]:
            raise ValueError(f"{heading}: missing entries {sorted(missing)}")
    return rows


def verify_source(path):
    source = path.read_bytes()
    if sha256(source).hexdigest() != DIGEST:
        raise ValueError("main.tex differs from the reviewed November 23 draft")
    tex = re.sub(r"(?<!\\)%[^\n]*", "", source.decode())
    section = re.search(r"\\section\{Variations on the construction\}(.*?)(?=\\section\{|\\end\{document\}|\Z)",
                        tex, flags=re.S | re.I)
    if section is None or tuple(re.findall(r"\\subsection\{([^}]+)\}", section[1])) != HEADINGS:
        raise ValueError("The dated section or its subsection headings differ from the map")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, help="November 23 manuscript main.tex")
    parser.add_argument("--lean", type=Path, help="resolve all mapped declarations in a built package")
    args = parser.parse_args()
    try:
        rows = mapped_rows()
        if args.source:
            verify_source(args.source)
        if args.lean:
            check_declarations(args.lean, "UnconditionalCounterexample", rows)
        print(f"Section 9 map checked for {len(rows)} entries across three subsections.")
    except (ValueError, OSError) as error:
        raise SystemExit(str(error))
