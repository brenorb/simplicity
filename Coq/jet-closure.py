#!/usr/bin/env python3
"""Print the C.* modules that the given C.* modules load, including themselves.

    jet-closure.py MODULE...

Dependencies are read from the Require commands of Coq/C/*.v (comments are
ignored). Used by check-jets.sh --jets to scope a run to the jets' closure.
"""
import re
import sys
from pathlib import Path

COQ = Path(__file__).resolve().parent


def requires(path):
    text = re.sub(r"\(\*.*?\*\)", "", path.read_text(), flags=re.S)
    found = set()
    for match in re.finditer(r"(?:From\s+([\w.]+)\s+)?Require\s+(?:(?:Import|Export)\s+)?(.*?)\.(?=\s|$)",
                             text, re.S):
        prefix = match.group(1)
        for token in match.group(2).split():
            name = f"{prefix}.{token}" if prefix else token
            if name.startswith("C."):
                found.add(name)
    return found


def closure(roots):
    seen, todo = set(), list(roots)
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        path = COQ / (module.replace(".", "/") + ".v")
        if not path.exists():
            raise SystemExit(f"unknown module {module}")
        seen.add(module)
        todo.extend(requires(path) - seen)
    return seen


if __name__ == "__main__":
    print("\n".join(sorted(closure(sys.argv[1:]))))
