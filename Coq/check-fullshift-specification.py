#!/usr/bin/env python3
"""Check full-shift catalog binding and literal recursive program correspondence.

This supplements kernel checking; it does not verify C execution. For N > M,
compareVectorSize selects a vector of pairs of M-bit words in an N-bit word.
vectorComp vector2 adds one doubling, yielding log2(N)-log2(M) doublings.
The right-shift case is the symmetric selection. Equal sizes select iden and
are outside these registered theorem families.
"""
import os
import re
from pathlib import Path

COQ = Path(__file__).resolve().parent
REPO = Path(os.environ.get("JET_C_REPO", COQ.parent))


def compact(text):
    return re.sub(r"\s+", "", text)


def check(coq=COQ, repo=REPO):
    catalog = (repo / "Haskell/Core/Simplicity/CoreJets.hs").read_text()
    programs = (repo / "Haskell/Core/Simplicity/Programs/Word.hs").read_text()
    word = (coq / "Simplicity/Word.v").read_text()
    expected_dispatch = """full_shift wa wb = go (compareVectorSize wb wa)
      go (Left v) = full_right_shift1 (vectorComp vector2 v)
      go (Right (Left Refl)) = iden
      go (Right (Right v)) = full_left_shift1 (vectorComp vector2 v)"""
    for line in expected_dispatch.splitlines():
        if compact(line) not in compact(programs):
            raise ValueError("canonical full_shift dispatch differs")
    for direction in ("left", "right"):
        hs = re.search(rf"full_{direction}_shift1 \(DoubleV v\) = (.*?)\n where", programs, re.S)
        coq_body = re.search(rf"Definition build_full_{direction}_shift1.*?:=(.*?)\.", word, re.S)
        if not hs or not coq_body:
            raise ValueError("missing full_shift recursive definition")
        translated = coq_body[1]
        for old, new in (("O O H", "ooh"), ("O I H", "oih"),
                         ("I O H", "ioh"), ("I I H", "iih"),
                         ("O H", "oh"), ("I H", "ih")):
            translated = re.sub(r"\b" + r"\s+".join(old.split()) + r"\b", new, translated)
        if compact(translated) != compact(hs[1]):
            raise ValueError(f"full_{direction}_shift1 literal recursion differs")
        recursion = f"| 0 => iden | S n => build_full_{direction}_shift1 full_{direction}_shift1"
        if compact(recursion) not in compact(word):
            raise ValueError(f"full_{direction}_shift1 recursive dispatch differs")
    count = 0
    for filename in ("jet_core_fullshift_jets.v", "jet_core_fullshift64_jets.v"):
        source = (coq / "C" / filename).read_text()
        for direction, n, m, body in re.findall(
                r"Theorem full_(left|right)_shift_(\d+)_(\d+)_local_spec\s*:(.*?)\bProof\.", source, re.S):
            n, m = int(n), int(m)
            if not 0 < m < n or n & (n - 1) or m & (m - 1):
                raise ValueError("invalid full_shift vector sizes")
            symbol = f"Full{direction.title()}Shift{n}_{m}"
            a, b = (n, m) if direction == "left" else (m, n)
            assignment = f"specificationWord {symbol} = Prog.full_shift word{a} word{b}"
            if compact(assignment) not in compact(catalog):
                raise ValueError(f"canonical catalog mismatch: {symbol}")
            depth = n.bit_length() - m.bit_length()
            term = f"(@full_{direction}_shift1 (Word {m.bit_length()-1}) {depth} Alg.CoreFunSem)"
            if compact(term) not in compact(body):
                raise ValueError(f"Coq full_shift specialization mismatch: {symbol}")
            count += 1
    if count != 36:
        raise ValueError(f"full_shift theorem surface differs: {count}")
    return count


if __name__ == "__main__":
    try:
        count = check()
    except (ValueError, OSError) as error:
        raise SystemExit(str(error))
    print(f"canonical full_shift catalog/recursive specializations match: {count}")
