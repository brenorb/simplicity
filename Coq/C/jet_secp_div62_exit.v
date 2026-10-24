(** The original final stores/return decode to the canonical 62-step matrix. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.divstep C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_div62_invariant C.jet_secp_div62_transition C.jet_secp_div62_finish.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition div62_matrix_field matrix j := nth j
  [Trans.u matrix;Trans.v matrix;Trans.q matrix;Trans.r matrix] 0.
Definition div62_exit_words start j := nth j
  [Int64.repr(Trans.u(Trans.transN 62 start));Int64.repr(Trans.v(Trans.transN 62 start));
   Int64.repr(Trans.q(Trans.transN 62 start));Int64.repr(Trans.r(Trans.transN 62 start));
   Int64.repr(eta(fst(stepN 62 start)))] Int64.zero.

Lemma div62_matrix_field_bound start j : (j<4)%nat ->
  -(2^62)<=div62_matrix_field (Trans.transN 62 start) j<=2^62.
Proof.
  intro J;pose proof (Trans.bounded_transN 62 start) as Bound;unfold Trans.bounded in Bound.
  change (Z.of_nat 62) with 62 in Bound.
  pose proof (Z.abs_nonneg(Trans.u(Trans.transN 62 start))).
  pose proof (Z.abs_nonneg(Trans.v(Trans.transN 62 start))).
  pose proof (Z.abs_nonneg(Trans.q(Trans.transN 62 start))).
  pose proof (Z.abs_nonneg(Trans.r(Trans.transN 62 start))).
  destruct j as [|[|[|[|j]]]];try lia;
    cbn [div62_matrix_field nth];apply Z.abs_le;lia.
Qed.

Lemma div62_matrix_field_signed start j : (j<4)%nat ->
  Int64.signed(Int64.repr(div62_matrix_field (Trans.transN 62 start) j))=
    div62_matrix_field (Trans.transN 62 start) j.
Proof.
  intro J;apply Int64.signed_repr;pose proof (div62_matrix_field_bound start j J).
  change Int64.min_signed with (-9223372036854775808);change Int64.max_signed with 9223372036854775807;lia.
Qed.

Lemma div62_exit_words_field start j : (j<4)%nat ->
  div62_exit_words start j=Int64.repr(div62_matrix_field (Trans.transN 62 start) j).
Proof. destruct j as [|[|[|[|j]]]];intro J;try lia;reflexivity. Qed.

Theorem exec_div62_exit le m start precision b :
  -683<=eta start<683 -> div62_loop_invariant start precision 62 0 b le ->
  Mem.range_perm m b 0 32 Cur Freeable -> exists lef mf,
    Clight2.exec_stmt secp_ge empty_env le m div62_finish E0 lef mf
      (Out_return (Some(Vlong(Int64.repr(eta(fst(stepN 62 start)))),tlong))) /\
    (forall j,(j<4)%nat -> exists w,Mem.load Mint64 mf b (8*Z.of_nat j)=Some(Vlong w) /\
      Int64.signed w=div62_matrix_field (Trans.transN 62 start) j) /\
    Int64.signed(Int64.repr(eta(fst(stepN 62 start))))=eta(fst(stepN 62 start)) /\
    Mem.range_perm mf b 0 32 Cur Freeable /\ lframe (fun bx _=>bx<>b) m mf.
Proof.
  intros Initial (_ & _ & (u & v & MU & MV & U & V & Q & R) & _ & Eta & _ & T) Free.
  rewrite Z.pow_0_r,Z.mul_1_r in MU,MV;rewrite <- MU in U;rewrite <- MV in V.
  rewrite Z.add_0_r in Eta.
  destruct (exec_div62_finish (div62_exit_words start) le m b T U V Q R Eta Free)
    as (lef & mf & Run & Loads & Owned & Frame).
  exists lef,mf;split;[exact Run|];split.
  - intros j J;exists (div62_exit_words start j);split;[now apply Loads|].
    rewrite div62_exit_words_field by exact J;now apply div62_matrix_field_signed.
  - split.
    + apply Int64.signed_repr;pose proof (etaBounds 683 62 start Initial) as Bound.
      change (Z.of_nat 62) with 62 in Bound.
      change Int64.min_signed with (-9223372036854775808);change Int64.max_signed with 9223372036854775807;lia.
    + split;assumption.
Qed.
