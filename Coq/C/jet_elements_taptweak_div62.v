(** Actual linked 62-divstep call using the approved counting model.
    Numerical invariants and termination are reused from the original proof;
    each counting call is derived at the linked symbol, on a nonzero sentinel. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clightdefs Clight
 ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.extraMath C.divstep C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_statement_prefix C.jet_secp_div62_count C.jet_secp_div62_consume
 C.jet_secp_div62_transition C.jet_secp_div62_entry C.jet_secp_div62_invariant
 C.jet_secp_div62_finish C.jet_secp_div62_exit C.jet_secp_div62_loop
 C.jet_elements_taptweak_pure C.jet_elements_taptweak_curve_transport
 C.jet_elements_taptweak_internal C.jet_clight_internal_preserve C.jet_clight_internal_frame
 C.jet_transport_entry C.jet_ctz_model.
Require Import C.jet_elements_taptweak_div62_support.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_curve_helpers.
Section ACTUAL_COUNT_CALLS.
Variable Model:ctz_model.
Variable m:mem.
Theorem exec_elements_taptweak_div62_body_invariant le start precision n pending b :
  62<=precision<=64 -> -683<=eta start<683 ->
  div62_loop_invariant start precision n pending b le -> exists lef out,
    Clight2.exec_stmt elements_taptweak_ge empty_env le m div62_loop_body E0 lef m out /\
    ((out=Out_break /\ div62_loop_invariant start precision 62 0 b lef) \/
     (out=Out_normal /\ exists n2 p2,(n<n2)%nat /\ div62_loop_invariant start precision n2 p2 b lef)).
Proof.
  intros Precision Initial Inv.
  pose proof Inv as (N & P & Matrix & (a & g0 & A & B & F & G) & Eta & Index & T).
  set (i:=62-Z.of_nat n+pending) in *.
  assert (I:0<=i<=62) by (unfold i;apply Nat2Z.inj_le in N;lia).
  set (w:=Int64.repr(g0*2^pending)) in *.
  pose proof (exec_elements_taptweak_div62_count_call Model le m w i I G Index) as Call.
  set (z:=div62_sentinel_count w i) in *.
  assert (Zeros:(div62_counted_temps le z)!_zeros=
    Some(Vint(Int.repr(div62_expected_count (div62_counted_temps le z) i)))).
  { rewrite div62_counted_expected;unfold div62_expected_count;rewrite G.
    unfold div62_counted_temps;apply PTree.gss. }
  destruct (exec_div62_postcount_invariant empty_env (div62_counted_temps le z) m
    start precision n pending b Precision Initial (div62_counted_invariant _ _ _ _ _ _ z Inv) Zeros)
    as (lef & out & Post & Result).
  assert(PostT:Clight2.exec_stmt elements_taptweak_ge empty_env (div62_counted_temps le z) m div62_after_count E0 lef m out).
  { apply elements_taptweak_div62_pure_exec;[cbn[elements_taptweak_div62_pure_phases In];tauto|exact Post]. }
  exists lef,out;split;[|exact Result].
  rewrite div62_body_count_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0)
    (m1:=m) (le1:=le);[constructor|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Call|exact PostT].
Qed.

Theorem exec_elements_taptweak_div62_loop_fuel fuel : forall le start precision n pending b,
  (62-n<fuel)%nat -> 62<=precision<=64 -> -683<=eta start<683 ->
  div62_loop_invariant start precision n pending b le -> exists lef,
    Clight2.exec_stmt elements_taptweak_ge empty_env le m div62_loop E0 lef m Out_normal /\
    div62_loop_invariant start precision 62 0 b lef.
Proof.
  induction fuel as [|fuel IH];intros le start precision n pending b Fuel Precision Initial Inv;
    [lia|].
  destruct (exec_elements_taptweak_div62_body_invariant le start precision n pending b Precision Initial Inv)
    as (le1 & out & Body & [(-> & Final)|(-> & n2 & p2 & Progress & Next)]).
  - exists le1;split;[|exact Final].
    rewrite div62_loop_source;eapply exec_Sloop_stop1;[exact Body|constructor].
  - pose proof (proj1 Inv) as N;pose proof (proj1 Next) as N2.
    destruct (IH le1 start precision n2 p2 b ltac:(lia) Precision Initial Next)
      as (lef & Repeat & Final).
    exists lef;split;[|exact Final].
    rewrite div62_loop_source in Repeat |- *.
    eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0)
      (m1:=m) (m2:=m) (le1:=le1) (le2:=le1) (out1:=Out_normal).
    + exact Body.
    + constructor.
    + constructor.
    + exact Repeat.
Qed.

Theorem exec_elements_taptweak_div62_loop_invariant le start precision n pending b :
  62<=precision<=64 -> -683<=eta start<683 ->
  div62_loop_invariant start precision n pending b le -> exists lef,
    Clight2.exec_stmt elements_taptweak_ge empty_env le m div62_loop E0 lef m Out_normal /\
    div62_loop_invariant start precision 62 0 b lef.
Proof. intros; eapply (exec_elements_taptweak_div62_loop_fuel 63);[lia|eassumption|eassumption|eassumption]. Qed.

Theorem eval_elements_taptweak_div62 st precision f0 g0 b :
  62<=precision<=64 -> -683<=eta st<683 ->
  eqm (2^precision) (Int64.unsigned f0) (f st) ->
  eqm (2^precision) (Int64.unsigned g0) (g st) ->
  Mem.range_perm m b 0 32 Cur Freeable -> exists mf,
    Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_modinv64_divsteps_62_var)
      [Vlong(Int64.repr(eta st));Vlong f0;Vlong g0;Vptr b Ptrofs.zero]
      E0 mf (Vlong(Int64.repr(eta(fst(stepN 62 st))))) /\
    (forall j,(j<4)%nat -> exists w,Mem.load Mint64 mf b (8*Z.of_nat j)=Some(Vlong w) /\
      Int64.signed w=div62_matrix_field (Trans.transN 62 st) j) /\
    (forall j,(j<4)%nat -> Mem.load Mint64 mf b (8*Z.of_nat j)=Some(Vlong(div62_exit_words st j))) /\
    Int64.signed(Int64.repr(eta(fst(stepN 62 st))))=eta(fst(stepN 62 st)) /\
    Mem.range_perm mf b 0 32 Cur Freeable /\ lframe(fun bx _=>bx<>b) m mf /\ readonly_preserved m mf.
Proof.
  intros Precision Initial F G Free.
  destruct (div62_entry_invariant m st precision f0 g0 b Precision F G)
    as (le0 & le1 & Entry & Init & Inv).
  destruct (exec_elements_taptweak_div62_loop_invariant le1 st precision 0 0 b Precision Initial Inv)
    as (le2 & Loop & Terminal).
  destruct (exec_div62_exit le2 m st precision b Initial Terminal Free)
    as (lef & mf & Finish & Loads & Eta & Owned & Frame).
  assert (ExactLoads:forall j,(j<4)%nat ->
    Mem.load Mint64 mf b (8*Z.of_nat j)=Some(Vlong(div62_exit_words st j))).
  { intros j J;destruct (Loads j J) as (w & Load & Signed).
    rewrite div62_exit_words_field by exact J;rewrite <- Signed,Int64.repr_signed;exact Load. }
  assert(FinishT:Clight2.exec_stmt elements_taptweak_ge empty_env le2 m div62_finish E0 lef mf
    (Out_return(Some(Vlong(Int64.repr(eta(fst(stepN 62 st)))),tlong)))).
  { apply elements_taptweak_div62_pure_exec;[cbn[elements_taptweak_div62_pure_phases In];tauto|exact Finish]. }
  assert(Readonly:readonly_preserved m mf).
  { eapply(proj1(internal_exec_preserved _ _ elements_taptweak_internal_table));
    [exact FinishT|apply plain_empty|exact elements_taptweak_div62_finish_closed]. }
  exists mf;split;[|split;[exact Loads|];split;[exact ExactLoads|];
    split;[exact Eta|];split;[exact Owned|];split;[exact Frame|exact Readonly]].
  eapply eval_funcall_internal with (e:=empty_env) (le1:=le0) (le2:=lef) (m1:=m) (m2:=mf)
    (out:=Out_return(Some(Vlong(Int64.repr(eta(fst(stepN 62 st)))),tlong))).
  - eapply function_entry2_transport;[exact elements_taptweak_div62_vars_checked|exact Entry].
  - rewrite div62_finish_source;eapply exec_statement_prefix_then_last;[apply elements_taptweak_div62_pure_exec;[cbn[elements_taptweak_div62_pure_phases In];tauto|exact Init]|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Loop|exact FinishT].
  - split;[discriminate|reflexivity].
  - reflexivity.
Qed.
End ACTUAL_COUNT_CALLS.
