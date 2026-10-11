# Continue from sharp bounds to the actual second-fold value

The two archived modules compile completely. Last checked declarations:
`second_fold_bridge_modulo_order` and `reduce512_second_limb_kinds`.
The former concerns an explicitly named integer bridge, not actual C output.
The latter concerns the actual completed prefix, not its numerical correctness.

The separate scratch experiment
`/tmp/jet-scalar-mul.lkomWj/jet_secp_reduce512_second_symbolic.v`
is **not compiled or archived as a verified module**. It contains a proposed
factored symbolic/machine schedule and representation proofs after the failing
source lemma; those later proofs have not been checked. No admission is used.

## Exact current failure

The all-five `second_symbolic_source` equality times out under bounded direct
conversion. The original whole-list reflexivity and vm_compute both timed out.
Splitting list constructors with `f_equal2` isolates the first failing leaf:

```coq
reduce512_second_temp _p3 = sc_lo second_sy3
```

The p0, p1 and p2 leaves close separately by bounded reflexivity in the
interactive session. That is an accepted tactic prefix, **not** a compiled
all-five source theorem. Neither direct reflexivity nor vm_compute closes the
p3 leaf in ten seconds. The next remaining leaf is the p4 narrowing expression.
`f_equal` alone made no progress on the still-folded p3 expressions.

Do not simply retry whole-array normalization or extend every timeout. The
second stage duplicates first-fold expressions inside uint128 products; keep
the first-fold state/digits shared and derive smaller operation/temp bindings,
or use a proved suffix/state/substitution decomposition. Each new abstraction
must preserve the actual prefix source and discharge its internal premises.
An alternative value-preserving symbolic compression needs its own formal
correctness proof; a proposed schedule cannot be assumed to be source output.

Reproduce from `/tmp/jet-scalar-integration.XAMDsw/Coq`, pinned Coq 8.17.1
on PATH and stack 65520 KiB:

```sh
bash build-jets.sh --coqc -R /tmp/jet-scalar-mul.lkomWj MulC \
  /tmp/jet-scalar-mul.lkomWj/jet_secp_reduce512_second_symbolic.v
```

Current syntax uses lowercase Ltac `timeout` inside tacticals; uppercase
`Timeout` is a vernacular wrapper and is not a tactic in `[...|...]`.

## Actual second-stage arithmetic schedule

- p0: fast multiply m4*C0 into (m0,0,0), fast extract.
- p1: fast sum m1, full multiply m5*C0, full multiply m4*C1, extract.
- p2: full sum m2, full multiply m6*C0, full multiply m5*C1, full sum m4,
  extract. m6 is the actual zero-extended uint32 first-fold value.
- p3: fast sum m3, fast multiply m6*C1, fast sum m5, fast extract.
- p4: **narrow c0 + m6 into uint32**, then zero extend when representing the
  fifth output limb. Do not omit the added m6 or either real narrowing cast.

Reuse `wide_accumulate_small` for p1/p2 and the first-fold m6 <= 1 bound for
p3's fast guards. Reconstruct the untruncated five-limb value first. The sharp
bridge bound in this archive then gives p4 <= 2 and lossless narrowing, once
the source/value bridge is proved. Next use the existing unchanged helper
execution, accepted overflow/scalar_reduce lemmas, public caller/writer/free
proofs, and the literal Simplicity bridge. No new public coverage yet.

Main coverage remains 351/533; accepted isolated scalar-add is 359/533 with
exact main integration and verification still pending. Claude owns Elements,
linked memcpy, SHA startup and shared constructibility. No overlap or registry
change here. Signed atomic local commits only, no remote pushes.
