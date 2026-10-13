#!/usr/bin/env python3
"""Manifest of the Coq modules added on this branch (relative to the fork
point), for integration: path, group, SHA-256, number of theorems/lemmas,
and the script that verifies the group.

Usage: shared-manifest.py write|check   (run from the repository root)"""
import hashlib, re, subprocess, sys

FORK = "a8685146"
OUT = "Coq/SHARED_MANIFEST.tsv"
GROUPS = [  # first match wins
    (r"^Coq/linked/", "linked", "bash Coq/audit-linked.sh; bash Coq/build-linked-startup.sh --check"),
    (r"^Coq/startup/", "startup", "bash Coq/build-startup.sh --check"),
    (r"^Coq/elements-sha/", "elements-sha", "bash Coq/audit-elements-sha.sh"),
    (r"^Coq/bitcoin-env/", "bitcoin-env", "bash Coq/audit-bitcoin-env.sh"),
    (r"^Coq/elements-env/", "elements-env", "bash Coq/build-elements-env.sh"),
    (r"^Coq/C/jets_(bitcoin|elements)_env\.v$", "environment-programs", "bash Coq/C/regenerate-bitcoin-env.sh; bash Coq/C/regenerate-elements-env.sh (clightgen output)"),
    (r"^Coq/forward/", "forward", "bash Coq/build-elements-forward.sh --check"),
    (r"^Coq/C/(jet_)?memcpy", "memcpy", "bash Coq/build-jets.sh --coqchk -silent -o C.jet_memcpy_exact C.jet_memcpy_impl C.jet_memcpy_model_consistent"),
    (r"^Coq/C/(jet_)?memcmp", "memcmp", "bash Coq/build-jets.sh --coqchk -silent -o C.jet_memcmp_impl C.jet_memcmp_model"),
    (r"^Coq/C/jets_elements\.v$", "elements-program", "bash Coq/C/regenerate-elements-jets.sh (clightgen output)"),
    (r"^Coq/C/jet_elements_", "elements", "bash Coq/build-jets.sh --coqchk -silent -o C.jet_elements_runs_everywhere C.jet_elements_runs_everywhere_rest"),
    (r"^Coq/C/jet_bitcoin_env_constructible", "bitcoin-environments", "bash Coq/build-jets.sh --coqchk -silent -o C.jet_bitcoin_env_constructible_raw C.jet_bitcoin_env_constructible_distance C.jet_bitcoin_env_constructible_indexed"),
    (r"^Coq/C/jet_env_constructible", "environment-construction", "(checked with its consumers)"),
    (r"^Coq/C/jet_(frame_constructible|frame_executable|app_executable|env_rep_stable)", "frames",
     "bash Coq/build-jets.sh --coqchk -silent -o C.jet_frame_constructible_context C.jet_frame_executable_registry C.jet_app_executable_registry C.jet_frame_constructible_secp"),
    (r"", "other", ""),
]

def manifest():
    files = subprocess.run(["git", "diff", "--name-only", "--diff-filter=A", FORK, "HEAD", "--", "*.v"],
                           check=True, capture_output=True, text=True).stdout.split()
    rows = ["path\tgroup\tsha256\tresults\tverify"]
    for path in sorted(files):
        data = open(path, "rb").read()
        group, verify = next((g, v) for pat, g, v in GROUPS if re.search(pat, path))
        results = len(re.findall(rb"^(?:Theorem|Lemma|Corollary) ", data, re.M))
        rows.append("\t".join([path, group, hashlib.sha256(data).hexdigest(), str(results), verify]))
    return "\n".join(rows) + "\n"

if __name__ == "__main__":
    text = manifest()
    if sys.argv[1:] == ["write"]:
        open(OUT, "w").write(text)
        print("%d modules" % (text.count("\n") - 1))
    elif sys.argv[1:] == ["check"]:
        if open(OUT).read() != text:
            sys.exit("stale " + OUT)
        print("manifest matches: %d modules" % (text.count("\n") - 1))
    else:
        sys.exit(__doc__)
