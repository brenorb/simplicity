# Checked linking repairs and isolated integration

This review continues the non-linked integration of frozen Claude snapshot
`30404face45383153528f36d915de6d7df11f3f4`. It does not merge the branch
wholesale, change its active worktree, or alter the normal jet registry.

Three linking modules used unchecked conversion casts. Before staging each
source, this driver replaces exactly that proof with
`timeout 10 (vm_compute; reflexivity)`. Statements and all other proof bodies
are unchanged. The core equality first passed a separate bounded experiment;
the complete linking modules and their callers must also pass the checks.

The copied trees have different `C.jets` / `C.jets_sha` programs. The frozen
generator replaces the external memcpy declaration with the CompCert Clight
implementation generated from `jet_memcpy_exact.c`; five call-site modules
are derived with the frozen patcher. Sources using either changed program or
the replacement model are rebuilt. Renamed program modules are rebuilt too:
an object compiled as `C.jets` cannot be reused as `C.jets_unlinked`.
Unaffected objects may be copied, hash-pinned, and recursively kernel-checked.
There are no compiler-output symlinks into the main or Claude checkout.

Run with pinned Coq 8.17.1 / CompCert 3.14 dependencies, and a sufficiently
large process stack (`ulimit -s 65520`). Source editing and installation use
the preceding driver's patch helper. Commands:

```
python3 -B proof-work/linked-repair/run.py freeze
python3 -B proof-work/linked-repair/run.py prepare core  # also sha, bitcoin
python3 -B proof-work/linked-repair/run.py audit /absolute/candidate
python3 -B proof-work/linked-repair/test-review.py /absolute/candidate
python3 -B proof-work/linked-repair/run.py install /absolute/candidate
python3 -B proof-work/linked-repair/run.py post-check
```

Each audit regenerates the original applicable C programs and memcpy reference
and compares exact AST bytes, freshly builds affected/new modules, prints full
types, definitions and assumptions (including proof-valued builder aliases),
and recursively runs `coqchk -o` with no unsafe options. Generated linked
programs are independently regenerated during receipt validation; the linking
theorems establish their relation to CompCert's actual linker. Test fixtures
reject damaged inventories, receipts, sources, generators and terminal logs.

Whole-program linking results alone may inherit `Axioms.proof_irr`, via
CompCert's composite-environment linking. AST-level link results must be
closed. Jet execution contracts retain only the previously documented
inherited assumptions. This is not a new axiom or a normal-registry allowlist
change. Review receipts list every observed dependency individually.

Installation is additive and source-only, in program-specific directories.
Supporting original `JetStartup` modules are imported only when required by
the new linked startup tree. No compiled objects, generated shadow programs,
old broad build/audit scripts, stale coverage generators or old expansive
receipts are installed. New installation ledgers compose with the previous
integration's preservation check. Existing staged and dirty work is retained.

## Scope

These contracts describe **internally linked programs**, not the unchanged
program using abstract external libc semantics. In particular, the original
104 conditional registry entries remain conditional. Fresh-frame execution
does not mean arbitrary malformed frames are accepted. Existing SHA startup,
environment readability, separation and application-input bounds remain as
stated in the individual contracts. Registered coverage stays 364/533; this
review neither resumes nor completes the paused all-jets goal.

An old unchecked conversion in the existing secp normalization dependency is
a separate repair, not hidden by this integration. Claude's uncommitted
Elements copyInput experiment, the radix-sort obligation, remaining Elements
specification bridges and runtime-driver composition remain outside this
batch. No remote is modified.
