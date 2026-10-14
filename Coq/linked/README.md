# Internally linked jet programs

These sources belong to isolated derived Coq programs, **not** the main
`C` namespace. Use the copied-tree driver in
[`proof-work/linked-repair`](../../proof-work/linked-repair/README.md).
Do not add these files directly to the ordinary `_CoqProject.jets`.

In the core tree, `C.jets_unlinked` names the unchanged original core AST
and `C.jets` names the AST with the reference memcpy linked internally.
In the SHA tree, `C.jets_sha_unlinked` names the original SHA AST and
`C.jets_sha` names its linked counterpart. The generator preserves the
existing definition order and substitutes the internal function; the linker
proof checks CompCert's actual program-linking relation. Three source repairs
use bounded, checked conversion instead of unchecked casts.

The reference is generated from `Coq/C/jet_memcpy_exact.c`: it uses CompCert's
defined one-byte block-copy builtin and preserves arbitrary memory values,
including pointer fragments and uninitialized bytes. It is not a claim about
the machine's external libc memcpy and is not installed into production C.
Execution proofs are rebuilt against the internal-call model and adjusted
call sites; no premise is silently removed from an unchanged program.

AST-level linking results have no assumptions. The two whole-program linking
declarations in each linker module inherit CompCert's proof-irrelevance axiom;
that exception is confined to their assumption reports. The original normal
registry and its 104 `memcpy_model`-conditional entries are unchanged.

The per-program installation and audit receipts, including recursive kernel
checks and exact exported contract/assumption inventories, are under
`proof-work/linked-repair`. The source files preserve Claude's frozen snapshot
except for the explicitly documented checked equality proofs. Old broad
symlink-based build scripts and expansive old receipts are not imported.
