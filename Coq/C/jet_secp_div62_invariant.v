(** Trajectory-indexed invariant for the original post-count statements. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.extraMath C.divstep C.jet_clight_temp_frame C.jet_secp_statement_prefix
  C.jet_secp_div62_count C.jet_secp_div62_limit C.jet_secp_div62_numeric C.jet_secp_div62_transition
  C.jet_secp_div62_consume C.jet_secp_div62_entry C.jet_secp_linkage C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition div62_modified := [_i;_eta;_g;_u;_v;_f;_q;_r;_w;_m;_limit;_tmp;_t'2;_t'3].
Lemma div62_count_safe : temp_writes_within div62_modified div62_count_prefix=true.
Proof. reflexivity. Qed.
Lemma div62_cancel_safe : temp_writes_within div62_modified div62_after_count_prefix=true.
Proof. reflexivity. Qed.
Lemma div62_after_count_safe : temp_writes_within div62_modified div62_after_count=true.
Proof. reflexivity. Qed.
Lemma div62_step_t e le m s lef out : temp_writes_within div62_modified s=true ->
  Clight2.exec_stmt secp_ge e le m s E0 lef m out -> lef!_t=le!_t.
Proof.
  intros Safe Run;apply (exec_temp_frame _ _ _ _ _ _ _ _ _ _ Run Safe).
  cbn [div62_modified In];intuition discriminate.
Qed.

Definition div62_loop_invariant start precision (n : nat) pending b le :=
  (n<=62)%nat /\ 0<=pending<=Z.of_nat n /\
  div62_pending_matrix le (Trans.transN n start) pending /\
  div62_pending_fg le (fst(stepN n start)) (precision-Z.of_nat n) pending /\
  le!_eta=Some(Vlong(Int64.repr(eta (fst(stepN n start))+pending))) /\
  le!_i=Some(Vint(Int.repr(62-Z.of_nat n+pending))) /\ le!_t=Some(Vptr b Ptrofs.zero).

Lemma div62_invariant_count_bounds start precision n pending b le :
  div62_loop_invariant start precision n pending b le ->
  pending<=div62_expected_count le (62-Z.of_nat n+pending)<=62-Z.of_nat n+pending.
Proof.
  intros (N & P & Matrix & (a & g0 & A & B & F & G) & Eta & Index & T).
  unfold div62_expected_count;rewrite G.
  pose proof (div62_sentinel_count_bound (Int64.repr(g0*2^pending)) (62-Z.of_nat n+pending) ltac:(lia)).
  pose proof (div62_sentinel_consumes_pending g0 pending (62-Z.of_nat n+pending) ltac:(lia) ltac:(lia));lia.
Qed.

Lemma div62_branch_width_bound st i : -745<=eta st<=745 -> 1<=i<=62 ->
  1<=div62_branch_width st i<=i.
Proof.
  intros Eta I;unfold div62_branch_width,div62_sign;destruct (zlt (eta st) 0);
    unfold div62_cancel_bits,div62_limit;lia.
Qed.

Theorem div62_entry_invariant m st precision f0 g0 b : 62<=precision<=64 ->
  eqm (2^precision) (Int64.unsigned f0) (f st) -> eqm (2^precision) (Int64.unsigned g0) (g st) ->
  exists le0 le1,
    function_entry2 secp_ge f_secp256k1_modinv64_divsteps_62_var
      [Vlong(Int64.repr(eta st));Vlong f0;Vlong g0;Vptr b Ptrofs.zero] m empty_env le0 m /\
    Clight2.exec_stmt secp_ge empty_env le0 m div62_initializers E0 le1 m Out_normal /\
    div62_loop_invariant st precision 0 0 b le1.
Proof.
  intros P F G;destruct (div62_entry_to_loop m st precision f0 g0 b P F G)
    as (le0 & le1 & Entry & Init & Matrix & FG & Eta & Index & T).
  exists le0,le1;split;[exact Entry|];split;[exact Init|].
  unfold div62_loop_invariant;split;[lia|];split;[lia|].
  change (div62_pending_matrix le1 Trans.I 0 /\ div62_pending_fg le1 st (precision-0) 0 /\
    le1!_eta=Some(Vlong(Int64.repr(eta st+0))) /\
    le1!_i=Some(Vint(Int.repr(62-0+0))) /\ le1!_t=Some(Vptr b Ptrofs.zero)).
  rewrite Z.sub_0_r,Z.add_0_r;repeat split;assumption.
Qed.

Theorem exec_div62_consume_invariant e le m start precision n pending b :
  62<=precision<=64 -> div62_loop_invariant start precision n pending b le ->
  le!_zeros=Some(Vint(Int.repr(div62_expected_count le (62-Z.of_nat n+pending)))) ->
  exists lef n1,
    Clight2.exec_stmt secp_ge e le m div62_count_prefix E0 lef m
      (div62_count_outcome (62-Z.of_nat n+pending) (div62_expected_count le (62-Z.of_nat n+pending))) /\
    (n<=n1<=62)%nat /\
    Z.of_nat n1=Z.of_nat n+div62_expected_count le (62-Z.of_nat n+pending)-pending /\
    div62_loop_invariant start precision n1 0 b lef /\
    (n1=62%nat \/ Zodd(g(fst(stepN n1 start)))).
Proof.
  intros Precision Inv Zeros;pose proof (div62_invariant_count_bounds _ _ _ _ _ _ Inv) as CountBounds.
  destruct Inv as (N & P & Matrix & FG & Eta & Index & T).
  set (i:=62-Z.of_nat n+pending) in *;set (z:=div62_expected_count le i) in *.
  destruct (exec_div62_consume e le m (fst(stepN n start)) (Trans.transN n start)
    (precision-Z.of_nat n) pending i ltac:(unfold i;lia) ltac:(unfold i;lia)
    ltac:(unfold i;lia) ltac:(lia) Matrix FG Eta Index Zeros)
    as (lef & Run & NewMatrix & NewFG & NewEta & NewIndex & Odd).
  fold z in Run,NewMatrix,NewFG,NewEta,NewIndex,Odd.
  set (n1:=(Z.to_nat(z-pending)+n)%nat).
  assert (N1 : Z.of_nat n1=Z.of_nat n+z-pending) by
    (unfold n1;rewrite Nat2Z.inj_add,Z2Nat.id by lia;lia).
  rewrite Trans.transN_stepN in NewMatrix.
  rewrite <- stepN_app_fst in NewFG,NewEta,Odd.
  fold n1 in NewMatrix,NewFG,NewEta,Odd.
  replace (precision-Z.of_nat n-(z-pending)) with (precision-Z.of_nat n1) in NewFG by lia.
  exists lef,n1;split;[exact Run|];split.
  - apply Nat2Z.inj_le in N;split;apply Nat2Z.inj_le;unfold i in *;lia.
  - split;[exact N1|];split.
    + unfold div62_loop_invariant;split;[apply Nat2Z.inj_le;unfold i in *;lia|];split;[lia|].
      split;[exact NewMatrix|];split;[exact NewFG|];split.
      * rewrite Z.add_0_r;exact NewEta.
      * split.
        -- replace (62-Z.of_nat n1+0) with (i-z) by (unfold i;lia);exact NewIndex.
        -- rewrite (div62_step_t _ _ _ _ _ _ div62_count_safe Run);exact T.
    + destruct Odd as [Exit|Nonexit];[left;apply Nat2Z.inj;unfold i in *;lia|now right].
Qed.

Theorem exec_div62_cancel_invariant e le m start precision n b :
  62<=precision<=64 -> -683<=eta start<683 ->
  div62_loop_invariant start precision n 0 b le -> (n<62)%nat -> Zodd(g(fst(stepN n start))) ->
  exists lef n2 pending,
    Clight2.exec_stmt secp_ge e le m div62_after_count_prefix E0 lef m Out_normal /\
    (n<n2)%nat /\ div62_loop_invariant start precision n2 pending b lef.
Proof.
  intros Precision Initial (N & P & Matrix & FG & Eta & Index & T) Nonexit Odd.
  destruct Matrix as (u & v & MU & MV & U & V & Q & R).
  rewrite Z.pow_0_r,Z.mul_1_r in MU,MV;rewrite <- MU in U;rewrite <- MV in V.
  destruct FG as (a & g0 & A & B & F & G);rewrite Z.pow_0_r,Z.mul_1_r in G.
  rewrite Z.add_0_r in Eta,Index.
  pose proof (etaBounds 683 n start Initial) as EtaBound.
  assert (Bounds : -745<=eta(fst(stepN n start))<=745) by (apply Nat2Z.inj_le in N;lia).
  assert (IRange : 1<=62-Z.of_nat n<=62) by (apply Nat2Z.inj_lt in Nonexit;lia).
  pose proof (div62_branch_width_bound _ _ Bounds IRange) as K.
  set (k:=div62_branch_width (fst(stepN n start)) (62-Z.of_nat n)) in *.
  destruct (exec_div62_transition_matrix e le m (fst(stepN n start)) (62-Z.of_nat n) a g0
    (precision-Z.of_nat n) (Trans.transN n start) Bounds IRange Odd ltac:(lia)
    A B Eta Index F G U V Q R) as (lef & Run & NewMatrix & NewFG & NewEta & NewIndex).
  fold k in NewMatrix,NewFG,NewEta.
  set (n2:=(Z.to_nat k+n)%nat).
  assert (N2 : Z.of_nat n2=Z.of_nat n+k) by
    (unfold n2;rewrite Nat2Z.inj_add,Z2Nat.id by lia;lia).
  rewrite Trans.transN_stepN in NewMatrix;rewrite <- stepN_app_fst in NewFG,NewEta.
  fold n2 in NewMatrix,NewFG,NewEta.
  replace (precision-Z.of_nat n-k) with (precision-Z.of_nat n2) in NewFG by lia.
  exists lef,n2,k;split;[exact Run|];split;[apply Nat2Z.inj_lt;lia|].
  unfold div62_loop_invariant;split;[apply Nat2Z.inj_le;lia|];split;[lia|].
  split;[exact NewMatrix|];split;[exact NewFG|];split;[exact NewEta|];split.
  - replace (62-Z.of_nat n2+k) with (62-Z.of_nat n) by lia;exact NewIndex.
  - rewrite (div62_step_t _ _ _ _ _ _ div62_cancel_safe Run);exact T.
Qed.

Theorem exec_div62_postcount_invariant e le m start precision n pending b :
  62<=precision<=64 -> -683<=eta start<683 ->
  div62_loop_invariant start precision n pending b le ->
  le!_zeros=Some(Vint(Int.repr(div62_expected_count le (62-Z.of_nat n+pending)))) ->
  exists lef out,
    Clight2.exec_stmt secp_ge e le m div62_after_count E0 lef m out /\
    ((out=Out_break /\ div62_loop_invariant start precision 62 0 b lef) \/
     (out=Out_normal /\ exists n2 p2,(n<n2)%nat /\ div62_loop_invariant start precision n2 p2 b lef)).
Proof.
  intros Precision Initial Inv Zeros.
  destruct (exec_div62_consume_invariant e le m start precision n pending b Precision Inv Zeros)
    as (le1 & n1 & Count & Bounds & N1 & Inv1 & Odd).
  destruct (Nat.eq_dec n1 62) as [Exit|Nonexit].
  - subst n1.
    assert (Same : 62-Z.of_nat n+pending=div62_expected_count le (62-Z.of_nat n+pending)) by lia.
    assert (Test : Z.eqb (62-Z.of_nat n+pending) (div62_expected_count le (62-Z.of_nat n+pending))=true)
      by (apply Z.eqb_eq;exact Same).
    unfold div62_count_outcome in Count;rewrite Test in Count.
    exists le1,Out_break;split.
    + rewrite div62_count_source;eapply exec_statement_prefix_aborts;[discriminate|exact Count].
    + left;split;[reflexivity|exact Inv1].
  - assert (Less : (n1<62)%nat) by lia.
    destruct Odd as [Impossible|Odd];[contradiction|].
    destruct (exec_div62_cancel_invariant e le1 m start precision n1 b Precision Initial Inv1 Less Odd)
      as (lef & n2 & p2 & Cancel & Progress & Inv2).
    assert (Different : 62-Z.of_nat n+pending<>div62_expected_count le (62-Z.of_nat n+pending)).
    { intro Same;apply Nonexit;apply Nat2Z.inj;lia. }
    unfold div62_count_outcome in Count.
    destruct (Z.eqb_spec (62-Z.of_nat n+pending) (div62_expected_count le (62-Z.of_nat n+pending)))
      as [Impossible|_];[contradiction|].
    exists lef,Out_normal;split.
    + rewrite div62_count_source;eapply exec_statement_prefix_then_last;[exact Count|exact Cancel].
    + right;split;[reflexivity|];exists n2,p2;split;[lia|exact Inv2].
Qed.
