# Negation candidate snapshot review

- All 3583 old assumption records are unchanged. There are 87 added results:
  57 closed, 14 with functional extensionality alone, four with inherited
  logical assumptions, and twelve with the six inherited execution assumptions.
  No new axiom names or changes to the kernel allowlist occur.
- The complete old printed type/definition snapshot is retained verbatim and
  in order: the diff contains only insertions (3833 lines), no deletions or
  replacements. There are no printer-qualification exceptions to approve.
- The additions are 87 result types and **35** definitions (not the earlier
  reported 34). All 87 results match the archive manifest. Eleven existing
  checked lemmas in `jet_literal_division_add` were missing from that manifest's
  result list; they are now recorded without any proof-source change.
- All 23 materialized proof modules match the archived checked bytes exactly.
  The missing final blank line in `jet_secp_negate_local.v` is restored; the
  dependent final contract and literal parametricity modules rebuild with
  exit 0 (77960), using Coq 8.17.1 and a 65520 KiB stack.

The added interfaces separate helper execution, exact limb loads, representation
and bounds, normalization/writer execution, public entry/source-copy/body/return/
free, literal canonical programs, all-width add/division semantic adapters and
parametricity. The public registration is only
`fe_negate_literal_local_spec`, not the optimized supporting theorem. Its full
Word256 input domain, output encoding, cursor/prefix and memory observations
remain those reviewed in `PUBLIC-CONTRACT-REVIEW.md`; the final six assumptions
are inherited execution assumptions, with no extra libc model. No assumed call,
output or impossible input premise has been added to the public interface.

The 35 new definitions comprise: canonical add (1), Haskell word conversion (2),
literal division (10), canonical negation/multiplication/normalization/factor (4),
helper symbolic arguments/run/tree/state (4), field representation/limb expressions
(5), public body statements (2), literal field programs (3), and wide writer
bounds/output/environment mappings (4). Their source correspondence and semantic
roles are covered by the canonical, recursive, literal and foundations reviews
and the four candidate gates (152 mutation fixtures); this is not a formal
Haskell compiler translation or an exhaustive inherited-repository fidelity
certification.

Next: run separate frozen `check-jets.sh --accept` without update flags. Do not
change candidate inputs during that run. Only successful full acceptance followed
by guarded integration and checkout acceptance can increase accepted coverage.
