(** Connect the stored canonical divstep matrix to the original inverse
    caller's eta assignment, coefficient/f-g updates and stop/shrink control.
    The full divstep call (in particular CTZ) remains a separate obligation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_zero C.jet_secp_modinv_var_shorten.
Require Import C.jet_secp_modinv_var_de C.jet_secp_modinv_var_fg C.jet_secp_modinv_var_post C.jet_secp_modinv_var_tail.
Require Import C.jet_secp_modinv_var_invariant C.jet_secp_modinv_var_ranges C.jet_secp_modinv_var_batch_exit.
Require Import C.jet_secp_modinv_de_numeric C.jet_secp_modinv_de_exec C.jet_secp_modinv_fg_prefix.
Require Import C.jet_secp_modinv_de_correction_numeric C.jet_secp_modinv_fg_body.
Require Import C.jet_secp_modinv_fg_loop_numeric.
Require Import C.jet_secp_modinv_normalize62_words C.jet_secp_modinv_normalize62_numeric C.jet_secp_fe_math C.divstep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma inv_batch_de_word st rho high i : (i<5)%nat ->
  de62_array (inv_de_rho (inv_batch_result_rho st rho)) high i=de62_array (inv_de_rho rho) high i.
Proof. destruct high;destruct i as [|[|[|[|[|i]]]]];intro I;try lia;reflexivity. Qed.

Lemma inv_batch_de_value st rho high :
  de62_input_value (inv_de_rho (inv_batch_result_rho st rho)) high=de62_input_value (inv_de_rho rho) high.
Proof. destruct high;reflexivity. Qed.

Lemma inv_batch_de_bounds st rho : de62_state_bounds (inv_de_rho rho) ->
  de62_state_bounds (inv_de_rho (inv_batch_result_rho st rho)).
Proof.
  intros (Limbs & Values);split.
  - intros high i I;rewrite inv_batch_de_word by exact I;apply Limbs;exact I.
  - intro high;rewrite inv_batch_de_value;apply Values.
Qed.

Lemma inv_batch_fg_value st len rho high : (0<len<=5)%nat ->
  inv_fg_active_value len (inv_batch_result_rho st rho) high=inv_fg_active_value len rho high.
Proof.
  intro Len;unfold inv_fg_active_value;apply norm62_value_ext;intros i I.
  rewrite inv_batch_result_prefix;[reflexivity|destruct high;lia].
Qed.

Lemma inv_batch_coefficient_link st value len rho : (0<len<=5)%nat -> inv_coefficient_link value len rho ->
  inv_coefficient_link value len (inv_batch_result_rho st rho).
Proof.
  intros Len Link high;unfold inv_coefficient_link in *.
  rewrite inv_batch_de_value,inv_batch_fg_value by exact Len;apply Link.
Qed.

Lemma inv_batch_state_matches st len rho : (0<len<=5)%nat -> inv_state_matches len rho st ->
  inv_state_matches len (inv_batch_result_rho st rho) st.
Proof.
  intros Len (F & G);split;rewrite inv_batch_fg_value by exact Len;assumption.
Qed.

Lemma inv_batch_fg_bounds st rho : inv_fg_limb_bounds rho -> inv_fg_limb_bounds (inv_batch_result_rho st rho).
Proof.
  intros Bounds high j J;unfold inv_fg_limb_bounds in *.
  rewrite inv_batch_result_prefix;[apply Bounds;exact J|destruct high;lia].
Qed.

Lemma inv_batch_fg_capacity st len rho : (0<len<=5)%nat -> inv_fg_value_capacity len rho ->
  inv_fg_value_capacity len (inv_batch_result_rho st rho).
Proof.
  intros Len Capacity high;unfold inv_fg_value_capacity in *.
  rewrite inv_batch_fg_value by exact Len;apply Capacity.
Qed.

Definition inv_return_eta := match nth 1 (fst inv_caller_loop_parts) Sskip with
  Ssequence _ s=>s | _=>Sskip end.
Lemma inv_return_eta_source : inv_return_eta=Sset _eta (Etempvar _t'1 tlong).
Proof. reflexivity. Qed.
Definition inv_after_batch := Ssequence inv_return_eta inv_after_divsteps.

Lemma inv_post_eta_preserved le lef : inv_post_temp_frame le lef -> lef!_eta=le!_eta.
Proof.
  intro Frame;apply Frame;unfold inv_post_modified,inv_test_modified,inv_shorten_modified;
    cbn [app In];intuition discriminate.
Qed.

Definition inv_batch_next_rho len st rho := inv_iteration_rho len (inv_batch_result_rho st rho).
Definition inv_batch_next_length len st rho := inv_iteration_length len (inv_batch_result_rho st rho).

Theorem exec_inv_after_stored_batch value len rho st beta e le m :
  (0<len<=5)%nat -> rep (inv_batch_result_rho st rho) beta inv_loop_regs m ->
  ematch beta (snd inv_start_alloc) e ->
  le!_modinfo=Some(Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
  le!_len=Some(Vint(Int.repr(Z.of_nat len))) ->
  le!_t'1=Some(Vlong(Int64.repr(eta(fst(stepN 62 st))))) ->
  de62_state_bounds (inv_de_rho rho) -> inv_fg_limb_bounds rho ->
  inv_coefficient_link value len rho -> inv_state_matches len rho st -> exists lef mf out,
  Clight2.exec_stmt secp_ge e le m inv_after_batch E0 lef mf out /\
  rep (inv_batch_next_rho len st rho) beta inv_loop_regs mf /\
  lef!_len=Some(Vint(Int.repr(Z.of_nat(inv_batch_next_length len st rho)))) /\
  lef!_eta=Some(Vlong(Int64.repr(eta(fst(stepN 62 st))))) /\
  de62_state_bounds (inv_de_rho (inv_batch_next_rho len st rho)) /\
  inv_coefficient_link value (inv_batch_next_length len st rho) (inv_batch_next_rho len st rho) /\
  inv_state_matches (inv_batch_next_length len st rho) (inv_batch_next_rho len st rho) (fst(stepN 62 st)) /\
  (g st=0 -> out=Out_break /\
    de62_input_value (inv_de_rho (inv_batch_next_rho len st rho)) false mod feP=
      de62_input_value (inv_de_rho rho) false mod feP) /\
  (inv_fg_value_capacity len rho -> inv_fg_limb_bounds (inv_batch_next_rho len st rho) /\
    inv_fg_value_capacity (inv_batch_next_length len st rho) (inv_batch_next_rho len st rho)) /\
  (forall high,
    2^62*de62_input_value (inv_de_rho (inv_batch_next_rho len st rho)) high=
      de62_matrix_value (inv_de_rho (inv_batch_result_rho st rho)) high+
        feP*de62_correction_value (inv_de_rho (inv_batch_result_rho st rho)) high /\
    (2^62*de62_input_value (inv_de_rho (inv_batch_next_rho len st rho)) high-
      de62_matrix_value (inv_de_rho (inv_batch_result_rho st rho)) high) mod feP=0) /\
  (forall high,inv_fg_active_value (inv_batch_next_length len st rho) (inv_batch_next_rho len st rho) high=
    fg_matrix_value (inv_fg_rho len (inv_de_next_rho (inv_batch_result_rho st rho))) high len/2^62) /\
  inv_tail_low_bounds (inv_batch_next_length len st rho) (inv_batch_next_rho len st rho) /\
  (out=Out_break <-> inv_fg_active_value (inv_batch_next_length len st rho) (inv_batch_next_rho len st rho) true=0) /\
  (out=Out_normal -> inv_fg_active_value (inv_batch_next_length len st rho) (inv_batch_next_rho len st rho) true<>0) /\
  (out=Out_break \/ out=Out_normal) /\ (0<inv_batch_next_length len st rho<=5)%nat /\
  (forall id,id<>_eta -> ~In id inv_post_modified -> lef!id=le!id) /\
  lframe (fun b ofs=>~foot (inv_de_layout beta) (map rshape de62_regs) b ofs /\
    ~foot (inv_fg_layout beta) (map rshape fg_regs) b ofs /\ b<>blk beta 4 /\ b<>blk beta 5) m mf.
Proof.
  intros Len Rep Env Modinfo Length Returned DE FG Link State.
  set (r:=inv_batch_result_rho st rho).
  set (le1:=PTree.set _eta (Vlong(Int64.repr(eta(fst(stepN 62 st))))) le).
  assert (Assign : Clight2.exec_stmt secp_ge e le m inv_return_eta E0 le1 m Out_normal).
  { rewrite inv_return_eta_source;apply exec_Sset;apply eval_Etempvar;exact Returned. }
  assert (Modinfo1 : le1!_modinfo=Some(Vptr (blk beta 1) (Ptrofs.repr (bas beta 1)))).
  { unfold le1;rewrite PTree.gso by discriminate;exact Modinfo. }
  assert (Length1 : le1!_len=Some(Vint(Int.repr(Z.of_nat len)))).
  { unfold le1;rewrite PTree.gso by discriminate;exact Length. }
  assert (DE1 : de62_state_bounds (inv_de_rho r)) by (apply inv_batch_de_bounds;exact DE).
  assert (FG1 : forall high j,(j<5)%nat ->
    Z.abs(Int64.signed(fg_array_word (inv_fg_rho len r) high j))<=2^62).
  { intros high j J;rewrite inv_fg_limb_array by exact J.
    apply inv_batch_fg_bounds;[exact FG|exact J]. }
  assert (Link1 : inv_coefficient_link value len r) by (apply inv_batch_coefficient_link;assumption).
  assert (State1 : inv_state_matches len r st) by (apply inv_batch_state_matches;assumption).
  destruct (exec_inv_after_divsteps_invariant value len r st beta e le1 m Len Rep Env Modinfo1 Length1
    DE1 FG1 Link1 State1 (inv_batch_result_matrix st rho))
    as (lef & mf & out & Exec & Post & NewLen & NewDE & NewLink & NewState & Zero & Capacity &
      DENumeric & FGNumeric & Low & Stop & Nonzero & Outcomes & Range & TFrame & Frame).
  assert (Eta : lef!_eta=Some(Vlong(Int64.repr(eta(fst(stepN 62 st)))))).
  { rewrite (inv_post_eta_preserved le1 lef TFrame);unfold le1;apply PTree.gss. }
  assert (ZeroNext : g st=0 -> out=Out_break /\
    de62_input_value (inv_de_rho (inv_iteration_rho len r)) false mod feP=
      de62_input_value (inv_de_rho rho) false mod feP).
  { intro Z;destruct (Zero Z) as (Break & D);split;[exact Break|].
    unfold r in D;rewrite inv_batch_de_value in D;exact D. }
  assert (CapacityNext : inv_fg_value_capacity len rho ->
    inv_fg_limb_bounds (inv_iteration_rho len r) /\
      inv_fg_value_capacity (inv_iteration_length len r) (inv_iteration_rho len r)).
  { intro C;apply Capacity;apply inv_batch_fg_capacity;assumption. }
  assert (TempFrame : forall id,id<>_eta -> ~In id inv_post_modified -> lef!id=le!id).
  { intros id Ne Outside;rewrite (TFrame id Outside);unfold le1;apply PTree.gso;exact Ne. }
  exists lef,mf,out;split.
  - unfold inv_after_batch;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le1) (m1:=m);assumption.
  - split;[exact Post|];split;[exact NewLen|];split;[exact Eta|].
    split;[exact NewDE|];split;[exact NewLink|];split;[exact NewState|];split;[exact ZeroNext|].
    split;[exact CapacityNext|];split;[exact DENumeric|];split;[exact FGNumeric|];split;[exact Low|].
    split;[exact Stop|];split;[exact Nonzero|];split;[exact Outcomes|];split;[exact Range|];split;assumption.
Qed.
