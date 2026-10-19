#!/usr/bin/env python3
"""Per-module snapshot records of the public jet theorems.

    jet-records.py {contracts,assumptions} [--update] [--modules FILE]

Records come from C/jet_public_theorems.txt (theorem types and assumption
sets) and C/jet_contract_definitions.txt (definitions that give contracts
their meaning). Each listed module is printed by its own coqc run that loads
only that module's dependencies, so a record depends on nothing outside its
module's closure: a scoped run and a full run produce identical records, and
one broken module cannot change another module's records.

Snapshots live in C/snapshots/<module>.{contracts,assumptions}. Without
--update every selected module's records must equal its snapshot; with
--update the selected snapshots are rewritten (review the diff). --modules
restricts the run to the module names listed in FILE (one per line).
"""
import argparse
import concurrent.futures
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

COQ = Path(__file__).resolve().parent
SNAPSHOTS = COQ / "C/snapshots"
THEOREMS = COQ / "C/jet_public_theorems.txt"
DEFINITIONS = COQ / "C/jet_contract_definitions.txt"
# Axioms inherited from the Coq standard library and CompCert's parameterized
# external-call and inline-assembly semantics. Anything else fails.
INHERITED = {
    "Classical_Prop.classic",
    "FunctionalExtensionality.functional_extensionality_dep",
    "ClassicalDedekindReals.sig_forall_dec",
    "ClassicalDedekindReals.sig_not_dec",
    "Events.external_functions_sem",
    "Events.external_functions_properties",
    "Events.inline_assembly_sem",
    "Events.inline_assembly_properties",
}
MARK = "JET_RECORD "


def listed(path):
    rows = []
    for line in path.read_text().splitlines():
        parts = line.split()
        if line.startswith("#") or len(parts) != 2:
            continue
        rows.append((parts[0], parts[1]))
    return rows


def records_by_module(kind):
    modules = {}
    for module, name in listed(THEOREMS):
        modules.setdefault(module, []).append(("theorem", name))
    if kind == "contracts":
        for module, name in listed(DEFINITIONS):
            modules.setdefault(module, []).append(("definition", name))
    return modules


def script(kind, module, entries):
    lines = ['Set Warnings "-notation-overridden".', f"Require Import {module}."]
    if kind == "contracts":
        lines += ["Set Printing All.", "Set Printing Width 120."]
    for what, name in entries:
        key = f"{module}.{name}"
        lines.append(f'Goal True. idtac "{MARK}{key}". exact I. Qed.')
        if kind == "assumptions":
            lines.append(f"Print Assumptions {key}.")
        elif what == "theorem":
            lines.append(f"Check @{key}.")
        else:
            lines.append(f"Print {key}.")
    return "\n".join(lines) + "\n"


def run_module(kind, module, entries, work):
    source = Path(work) / (module.replace(".", "_") + ".v")
    source.write_text(script(kind, module, entries))
    result = subprocess.run(["bash", str(COQ / "build-jets.sh"), "--coqc", "-q", str(source)],
                            cwd=COQ, capture_output=True, text=True)
    if result.returncode != 0:
        return module, None, result.stdout + result.stderr
    records, key, body = {}, None, []
    for line in result.stdout.splitlines():
        line = line.rstrip()
        if line.startswith(MARK):
            if key:
                records[key] = body
            key, body = line[len(MARK):], []
        elif key:
            body.append(line)
    if key:
        records[key] = body
    return module, records, ""


def render(kind, module, entries, records):
    out = []
    for what, name in entries:
        key = f"{module}.{name}"
        if key not in records:
            raise ValueError(f"missing record {key}")
        body = records[key]
        if kind == "assumptions":
            axioms, inside = [], False
            for line in body:
                if line.startswith("Axioms:"):
                    inside = True
                elif line.startswith("Closed under the global context"):
                    inside = False
                elif inside and line and not line[0].isspace():
                    axioms.append(line.split()[0])
            out.append(f"{key} : {', '.join(sorted(set(axioms))) if axioms else 'closed'}")
        else:
            while body and not body[-1]:
                body = body[:-1]
            out.append(f"### {key}")
            out.extend(body)
    return "\n".join(out) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("kind", choices=["contracts", "assumptions"])
    parser.add_argument("--update", action="store_true")
    parser.add_argument("--modules")
    args = parser.parse_args()
    modules = records_by_module(args.kind)
    selected = sorted(modules)
    if args.modules:
        wanted = {m.strip() for m in Path(args.modules).read_text().split() if m.strip()}
        selected = [m for m in selected if m in wanted]
    jobs = int(os.environ.get("JOBS") or os.cpu_count() or 2)
    failed, changed, bad_axioms = [], [], set()
    with tempfile.TemporaryDirectory(prefix=f"jet-{args.kind}.") as work, \
            concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = [pool.submit(run_module, args.kind, m, modules[m], work) for m in selected]
        for future in concurrent.futures.as_completed(futures):
            module, records, error = future.result()
            if records is None:
                failed.append((module, error))
                continue
            try:
                text = render(args.kind, module, modules[module], records)
            except ValueError as exc:
                failed.append((module, str(exc)))
                continue
            if args.kind == "assumptions":
                for line in text.splitlines():
                    axioms = line.split(" : ", 1)[1]
                    if axioms != "closed":
                        bad_axioms |= set(axioms.split(", ")) - INHERITED
            snapshot = SNAPSHOTS / f"{module}.{args.kind}"
            if args.update:
                SNAPSHOTS.mkdir(parents=True, exist_ok=True)
                snapshot.write_text(text)
            elif not snapshot.exists() or snapshot.read_text() != text:
                changed.append(module)
    for module, error in sorted(failed):
        print(f"{module}: could not produce records\n{error}", file=sys.stderr)
    if bad_axioms:
        print("Unexpected axioms (not inherited from Coq/CompCert):", *sorted(bad_axioms), sep="\n  ",
              file=sys.stderr)
    stale = []
    if not args.modules:
        stale = sorted(p.name for p in SNAPSHOTS.glob(f"*.{args.kind}") if p.name[:-len(args.kind) - 1] not in modules)
        if args.update:
            for name in stale:
                (SNAPSHOTS / name).unlink()
            stale = []
    if changed:
        label = "public theorem contracts changed" if args.kind == "contracts" else "assumption sets differ"
        print(f"{label} in {len(changed)} module(s): {', '.join(sorted(changed))}", file=sys.stderr)
    if stale:
        print(f"snapshots for unlisted modules: {', '.join(stale)}", file=sys.stderr)
    if failed or bad_axioms or changed or stale:
        sys.exit(1)
    verb = "updated" if args.update else "match"
    print(f"{args.kind} records {verb}: {len(selected)} module(s)")


if __name__ == "__main__":
    main()
