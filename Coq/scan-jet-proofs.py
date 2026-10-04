#!/usr/bin/env python3
"""Reject proof escape hatches, including inline and attributed declarations.

This is a lexical check, not a Coq parser. Nested comments and strings are
masked first; the kernel and assumption audits remain the semantic checks.
"""
import re
import sys
from pathlib import Path


def code_only(source):
    chars = list(source)
    i, depth, string = 0, 0, False
    while i < len(source):
        pair = source[i:i + 2]
        if not string and pair == "(*":
            depth += 1
            chars[i:i + 2] = "  "
            i += 2
            continue
        if depth and pair == "*)":
            depth -= 1
            chars[i:i + 2] = "  "
            i += 2
            continue
        if not depth and source[i] == '"':
            if string and pair == '""':
                chars[i:i + 2] = "  "
                i += 2
                continue
            string = not string
            chars[i] = " "
        elif depth or string:
            if source[i] != "\n":
                chars[i] = " "
        i += 1
    if depth or string:
        raise ValueError("unterminated comment or string")
    return "".join(chars)


def violations(source):
    pattern = re.compile(
        r"\b(?:Axioms?|Parameters?|Conjecture|Admitted|admit|give_up|Abort|bypass_check)\b"
        r"|\bUnset\s+(?:Guard|Universe|Positivity)\s+Checking\b")
    return list(pattern.finditer(code_only(source)))


def main():
    paths = [Path(p) for p in sys.argv[1:]] or sorted(Path("C").glob("jet*.v"))
    failed = False
    for path in paths:
        source = path.read_text()
        for match in violations(source):
            print(f"{path}:{source.count(chr(10), 0, match.start()) + 1}: {match.group()}")
            failed = True
    if failed:
        sys.exit("unproved or assumed declarations in jet sources")


if __name__ == "__main__":
    main()
