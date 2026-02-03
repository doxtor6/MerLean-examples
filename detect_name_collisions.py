#!/usr/bin/env python3
"""Detect duplicate Lean 4 declaration names across files.

Scans all .lean files under the given directory, tracks namespace nesting,
computes fully qualified names for each declaration, and reports any name
that appears in more than one file.

Usage:
    python detect_name_collisions.py [directory]

If no directory is given, defaults to the current working directory.
"""

import re
import sys
from pathlib import Path
from collections import defaultdict

# Matches declaration keywords at the start of a line (possibly indented)
DECL_RE = re.compile(
    r"^\s*(?:noncomputable\s+|private\s+|protected\s+|unsafe\s+|partial\s+)*"
    r"(?P<kind>theorem|def|lemma|instance|abbrev|structure|class|inductive)\s+"
    r"(?P<name>\S+)"
)

NAMESPACE_RE = re.compile(r"^\s*namespace\s+(\S+)")
END_RE = re.compile(r"^\s*end\s+(\S+)")
SECTION_RE = re.compile(r"^\s*section\s+(\S+)")
END_BARE_RE = re.compile(r"^\s*end\s*$")


def fqn(ns_stack: list[str], name: str) -> str:
    """Build a fully qualified name from the namespace stack and a local name."""
    prefix = ".".join(ns_stack)
    if prefix:
        return f"{prefix}.{name}"
    return name


def scan_file(path: Path) -> list[tuple[str, str, int]]:
    """Return a list of (fqn, kind, line_number) for every declaration in the file."""
    ns_stack: list[str] = []
    results: list[tuple[str, str, int]] = []

    with open(path, encoding="utf-8", errors="replace") as f:
        for lineno, line in enumerate(f, start=1):
            # Track namespace open
            m = NAMESPACE_RE.match(line)
            if m:
                ns_stack.append(m.group(1))
                continue

            # Track namespace close (named end)
            m = END_RE.match(line)
            if m:
                name = m.group(1)
                # Pop matching namespace(s) - handle dotted names
                if ns_stack and ns_stack[-1] == name:
                    ns_stack.pop()
                elif ns_stack:
                    # Try matching the full dotted suffix
                    joined = ".".join(ns_stack)
                    if joined.endswith(name):
                        # Pop enough elements
                        parts = name.split(".")
                        for _ in parts:
                            if ns_stack:
                                ns_stack.pop()
                continue

            # Bare 'end' (closes innermost namespace/section)
            m = END_BARE_RE.match(line)
            if m:
                if ns_stack:
                    ns_stack.pop()
                continue

            # Track declarations
            m = DECL_RE.match(line)
            if m:
                kind = m.group("kind")
                name = m.group("name")
                # Skip names that start with special chars (operators, etc.)
                if name[0].isalpha() or name[0] == '_':
                    # Handle dotted declaration names (e.g., Foo.bar defined outside namespace Foo)
                    full = fqn(ns_stack, name)
                    results.append((full, kind, lineno))

    return results


def main():
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(".")
    root = root.resolve()

    if not root.is_dir():
        print(f"Error: {root} is not a directory", file=sys.stderr)
        sys.exit(1)

    # Collect all declarations: fqn -> [(file, kind, line)]
    decls: dict[str, list[tuple[Path, str, int]]] = defaultdict(list)

    lean_files = sorted(root.rglob("*.lean"))
    if not lean_files:
        print(f"No .lean files found under {root}")
        sys.exit(0)

    for path in lean_files:
        # Skip .lake directory
        try:
            path.relative_to(root / ".lake")
            continue
        except ValueError:
            pass

        for fqn_name, kind, lineno in scan_file(path):
            rel = path.relative_to(root)
            decls[fqn_name].append((rel, kind, lineno))

    # Find collisions (same fqn in multiple files)
    collisions = {
        name: locs
        for name, locs in decls.items()
        if len(set(loc[0] for loc in locs)) > 1  # in different files
    }

    if not collisions:
        print("No name collisions detected.")
        sys.exit(0)

    print(f"Found {len(collisions)} name collision(s):\n")
    for name in sorted(collisions):
        locs = collisions[name]
        kinds = set(loc[1] for loc in locs)
        print(f"  {name}  ({'/'.join(sorted(kinds))})")
        for rel_path, kind, lineno in sorted(locs):
            print(f"    - {rel_path}:{lineno}")
        print()

    sys.exit(1)


if __name__ == "__main__":
    main()
