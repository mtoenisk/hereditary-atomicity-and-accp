"""Verify that every library source is inventoried and imported by its public root."""

from pathlib import Path

root = Path(__file__).resolve().parent.parent
libraries = ("Factorization", "HereditaryAtomicity", "UnconditionalCounterexample")
modules = set()
for library in libraries:
    sources = {
        ".".join(path.relative_to(root).with_suffix("").parts)
        for path in (root / library).rglob("*.lean")
    }
    if not sources:
        raise SystemExit(f"No source modules for {library}")
    direct = {
        line.removeprefix("import ").strip()
        for line in (root / f"{library}.lean").read_text().splitlines()
        if line.startswith("import ")
    }
    if not sources <= direct:
        raise SystemExit(f"Missing imports in {library}: {sorted(sources - direct)}")
    modules.update(sources)

listed = (root / "MODULES").read_text().splitlines()
if listed != sorted(modules):
    raise SystemExit("MODULES must list each shipped library module once in sorted order")
print(f"All {len(modules)} library modules are inventoried and imported.")
