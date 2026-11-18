#!/usr/bin/env python3
"""Check the theorem map, its compiled proof locations, and optionally the dated TeX."""

import argparse
from difflib import unified_diff
from hashlib import sha256
from pathlib import Path
import re
import subprocess


EDITIONS = {
    "Semilocal domains": ("semilocal", 28, {
        "main.tex": "9cc88c22a1be85ad60afa64524374d8093428715f71cdec115ea081f28954306",
    }),
    "The counterexample": ("counterexample", 18, {
        "main.tex": "4c8e14dabaf731e257d53c94adc48015edccb77a8451d1de7f37f94afae15441",
        "profiles.tex": "508a0042b518087d588bd65af559530ffb2cad48a1b7e4fe68a190fc1a767f51",
        "construction.tex": "d869dcd14eddf28d93b2dc581d75a82d1b629ef418a1b6abf69b8f1495d6655e",
        "structure.tex": "7fbee0d5ab8bc6292b34a4f5c77515db34c09c85b4061abdbfe52b4e65d996a7",
        "curve.tex": "48351194ef7c2fbb05a0d260a14ad5268e0b4705c2a942a83442bd58a5709d9c",
        "conductor.tex": "01cb0991f132ed68aa0e38ba97c0a2c3d09b5b0728711cdedcf0183115ad7d35",
        "orders.tex": "1144d6aa02e443a232e239d7cba7e9262cb8753f9d5d9a6746b7e8aa0c9ea72a",
        "sharpness.tex": "89e04fd35b920adc88b82e0d370535ed4743c97950da9ba04f8632062164ce59",
    }),
}
INPUT = re.compile(r"\\(?:input|include)\{([^}]+)\}")
EVENT = re.compile(
    r"\\section\{|\\begin\{(maintheorem|theorem|lemma|proposition|corollary|definition|remark)\}"
    r"(?:\s*\[[^]]*\])?\s*\\label\{([^}]+)\}"
)
SEPARATOR = re.compile(r"\|(?:\s*:?-+:?\s*\|)+")
LEAN_NAME = re.compile(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*")
LIBRARIES = {
    "Semilocal domains": "HereditaryAtomicity",
    "The counterexample": "UnconditionalCounterexample",
}


def contract_locations(root):
    locations = {}
    for heading, library in LIBRARIES.items():
        for source in sorted((root / library / "Manuscript").rglob("*.lean")):
            for number, line in enumerate(source.read_text().splitlines(), 1):
                if not line.startswith("-- Manuscript: "):
                    continue
                key = (heading, line.removeprefix("-- Manuscript: ").strip())
                if key in locations:
                    raise ValueError(f"Duplicate manuscript marker {key}")
                locations[key] = f"[Typed proof]({source.relative_to(root).as_posix()}#L{number})"
    return locations


def manuscript_rows(directory, pins):
    def expand(name):
        data = (directory / name).read_bytes()
        if sha256(data).hexdigest() != pins[name]:
            raise ValueError(f"{directory.name}/{name} differs from the dated edition")
        source = re.sub(r"(?<!\\)%[^\n]*", "", data.decode("utf-8"))
        return INPUT.sub(lambda m: expand(str(Path(m[1]).with_suffix(".tex"))), source)

    section = item = main_theorem = 0
    rows = []
    for match in EVENT.finditer(expand("main.tex")):
        kind, label = match.groups()
        if kind is None:
            section += 1
            item = 0
        elif kind == "maintheorem":
            main_theorem += 1
            rows.append((f"Theorem {chr(64 + main_theorem)}", label))
        else:
            # Both editions number definitions and remarks on the theorem counter.
            item += 1
            if kind not in {"definition", "remark"}:
                rows.append((f"{kind.capitalize()} {section}.{item}", label))
    return rows


def map_rows(path, *, verify_links=False, refresh_links=False):
    sections = {}
    section = None
    locations = contract_locations(path.parent) if verify_links or refresh_links else None
    mapped = set()
    lines = path.read_text(encoding="utf-8").splitlines()
    for index, line in enumerate(lines):
        if line.startswith("## "):
            section = line[3:].strip()
            if section in EDITIONS:
                if section in sections:
                    raise ValueError(f"Repeated heading {section!r}")
                sections[section] = []
        elif section in EDITIONS and line.startswith("|"):
            # A Markdown table header is followed by its alignment row.
            if SEPARATOR.fullmatch(line) or (
                index + 1 < len(lines) and SEPARATOR.fullmatch(lines[index + 1])
            ):
                continue
            cells = [cell.strip() for cell in re.split(r"(?<!\\)\|", line.strip("|"))]
            if len(cells) not in (4, 5) or not all(cells):
                raise ValueError(f"{path.name} line {index + 1} has invalid table cells")
            title, label_cell, _, references = cells[:4]
            label = re.fullmatch(r"`([^`\s]+)`", label_cell)
            names = re.findall(r"`([^`]+)`", references)
            if not label or not names or not all(LEAN_NAME.fullmatch(name) for name in names):
                raise ValueError(f"{path.name} line {index + 1} has an invalid label or Lean name")
            if locations is not None:
                key = (section, label[1])
                if key not in locations or key in mapped:
                    raise ValueError(f"Missing or repeated typed proof for {key}")
                mapped.add(key)
                if refresh_links:
                    lines[index] = "| " + " | ".join([*cells[:4], locations[key]]) + " |"
                elif cells[4:] != [locations[key]]:
                    raise ValueError(f"Stale typed-proof link for {key}. Run with --refresh-links.")
            sections[section].append((title, label[1], names))
    if locations is not None and mapped != set(locations):
        raise ValueError(f"Unmapped typed proofs: {sorted(set(locations) - mapped)}")
    if refresh_links:
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return sections


def check_declarations(package, module, rows):
    names = dict.fromkeys(name for _, _, references in rows for name in references)
    code = [f"import {module}", *(f"#check @{name}" for name in names)]
    process = subprocess.run(
        ["lake", "env", "lean", "--stdin"], cwd=package,
        input="\n".join(code) + "\n", text=True, stdout=subprocess.PIPE
    )
    if process.returncode:
        raise ValueError(f"{module} declaration check failed.\n{process.stdout}")
    print(f"{module}: Lean resolved all {len(names)} referenced declarations.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manuscripts", type=Path, nargs="?",
                        help="directory containing the public semilocal/ and counterexample/ sources")
    parser.add_argument("--lean", type=Path, nargs="+", metavar="PACKAGE",
                        help="resolve declarations in the built package (or two separate libraries)")
    parser.add_argument("--refresh-links", action="store_true",
                        help="update line links after edits to manuscript proof modules")
    args = parser.parse_args()
    if args.lean and len(args.lean) not in (1, 2):
        parser.error("--lean takes one package directory or two library directories")
    table = map_rows(Path(__file__).with_name("THEOREMS.md"), verify_links=True,
                     refresh_links=args.refresh_links)
    for heading, (directory, count, pins) in EDITIONS.items():
        actual = [(title, label) for title, label, _ in table.get(heading, [])]
        if len(actual) != count or len({label for _, label in actual}) != count:
            raise ValueError(f"Expected {count} distinct result labels in {directory}")
        if args.manuscripts is None:
            print(f"{heading}: located typed proofs for {count} numbered statements.")
            continue
        expected = manuscript_rows(args.manuscripts / directory, pins)
        if actual != expected:
            difference = unified_diff(
                [" ".join(row) for row in expected], [" ".join(row) for row in actual],
                fromfile=directory, tofile=f"THEOREMS.md / {heading}", lineterm=""
            )
            raise ValueError("\n".join(difference))
        print(f"{heading}: matched {count} numbered statements in order.")
    if args.lean:
        check_declarations(args.lean[0], "HereditaryAtomicity", table["Semilocal domains"])
        check_declarations(args.lean[-1], "UnconditionalCounterexample", table["The counterexample"])


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        raise SystemExit(str(error))
