#!/usr/bin/env python3
"""Inspect an unpacked source archive before running its build."""

import argparse
import json
import os
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit


LIBRARIES = {"Factorization", "HereditaryAtomicity", "UnconditionalCounterexample"}
ROOT_FILES = {
    ".gitignore", "README.md", "THEOREMS.md", "ARXIV_THEOREMS.md", "STRICT_HIERARCHY.md", "THIRD_PARTY.md", "LICENSE",
    "CITATION.cff", "MODULES", "check_map.py", "SECTION9.md", "check_variations.py", "lakefile.toml",
    "lake-manifest.json", "lean-toolchain",
} | {f"{name}.lean" for name in LIBRARIES}
SOURCE_DIRS = LIBRARIES | {"scripts", "checks", "examples"}
MARKERS = {
    "internal note identifier": re.compile(r"(?<![A-Za-z])(?:[A-Z]{2,6}[-–][0-9]{4}|(?:HA|GPF)[0-9]{4})"),
    "private editor link": re.compile(r"https?://(?:www\.)?overleaf\.com/(?:project|read)/"),
    "machine-specific file path": re.compile(r"(?:/(?:Users|home|Volumes)/[^\s/]+/|[A-Za-z]:\\Users\\[^\s\\]+\\|file:/{3}[^\s]+)"),
    "development provenance": re.compile(r"\b(?:vault|workspace)\s+(?:baseline|revision|commit)\b", re.I),
}
MARKDOWN_LINK = re.compile(r"\[[^\]\n]*\]\(([^)\n]+)\)")


def allowed_file(path):
    if len(path.parts) == 1:
        return path.name in ROOT_FILES
    directory = path.parts[0]
    if directory in LIBRARIES or directory in {"checks", "examples"}:
        return path.suffix == ".lean"
    return directory == "scripts" and path.suffix in {".py", ".sh"}


def source_files(root):
    for parent, directories, files in os.walk(root):
        for name in sorted(directories.copy()):
            path = Path(parent, name)
            rel = path.relative_to(root)
            if path.is_symlink() or rel.parts[0] not in SOURCE_DIRS or name.startswith("."):
                directories.remove(name)
                raise ValueError(f"Unexpected directory or symlink: {rel}")
        for name in sorted(files):
            path = Path(parent, name)
            rel = path.relative_to(root)
            if path.is_symlink() or not allowed_file(rel) or not path.is_file():
                raise ValueError(f"Unexpected file or symlink: {rel}")
            yield path


def check_markdown_links(root, path, text):
    for target in MARKDOWN_LINK.findall(text):
        url = urlsplit(target.strip("<>"))
        if url.scheme in {"https", "http"}:
            continue
        if url.scheme or url.netloc:
            raise ValueError(f"Nonpublic link in {path.relative_to(root)}: {target}")
        if url.path:
            destination = (path.parent / unquote(url.path)).resolve()
            if not destination.is_relative_to(root) or not destination.exists():
                raise ValueError(f"Broken or escaping link in {path.relative_to(root)}: {target}")


def check(root):
    for path in source_files(root):
        text = path.read_text(encoding="utf-8")
        for number, line in enumerate(text.splitlines(), 1):
            for label, pattern in MARKERS.items():
                if pattern.search(line):
                    raise ValueError(f"{path.relative_to(root)}:{number}: {label}")
        if path.suffix == ".md":
            check_markdown_links(root, path, text)
        if path.name == "lakefile.toml" and re.search(r"(?m)^\s*path\s*=", text):
            raise ValueError("Lake configuration uses a filesystem dependency")
    manifest = json.loads((root / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        url = urlsplit(package.get("url", ""))
        if (package["type"] != "git" or url.scheme != "https" or not url.hostname
                or url.username or not re.fullmatch(r"[a-f0-9]{40}", package["rev"])):
            raise ValueError(f"Expected a pinned public Git dependency for {package['name']}")
    print("Release file inventory, reference markers, relative links, and dependency pins passed.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="unpacked source directory")
    args = parser.parse_args()
    try:
        check(args.source.resolve(strict=True))
    except (OSError, UnicodeError, ValueError, KeyError) as error:
        raise SystemExit(str(error))
