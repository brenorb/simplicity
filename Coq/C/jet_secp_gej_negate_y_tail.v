(** Actual generated Y arithmetic statements; no helper execution is assumed
    in the final owned-tail theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events Globalenvs.
Require Import C.jet_exec C.jet_sx_expr C.jet_sx_state C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_write_fe_numeric C.jet_secp_field_negate_storage C.jet_secp_point_write_run.
Require Import C.jet_secp_gej_negate_fields C.jet_secp_gej_negate_prefix C.jet_secp_point_y_arithmetic.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma gej_negate_weak_symbol :
  exists b, Genv.find_symbol secp_ge _secp256k1_fe_normalize_weak = Some b /\
    Genv.find_funct_ptr secp_ge b = Some (Internal f_secp256k1_fe_normalize_weak).
Proof. exists (secp_symbol_block _secp256k1_fe_normalize_weak); split; reflexivity. Qed.
Lemma gej_negate_field_symbol :
  exists b, Genv.find_symbol secp_ge _secp256k1_fe_negate = Some b /\
    Genv.find_funct_ptr secp_ge b = Some (Internal f_secp256k1_fe_negate).
Proof. exists (secp_symbol_block _secp256k1_fe_negate); split; reflexivity. Qed.
Local Opaque secp_ge.

Lemma eval_gej_negate_y_address le m b :
  le!_r = Some (Vptr b Ptrofs.zero) ->
  eval_expr secp_ge empty_env le m gej_negate_y_address (Vptr b (Ptrofs.repr 40)).
Proof.
  intro HR; unfold gej_negate_y_address; apply eval_Eaddrof.
  exact (eval_gej_pointer_field le m b 0 _r _y 40 (Tstruct __5467 noattr)
    ltac:(cbn;tauto) ltac:(lia)
    ltac:(change (128 <= 18446744073709551615);lia) HR).
Qed.

Lemma exec_gej_negate_y_tail_from_calls le m mw mf b :
  le!_r = Some (Vptr b Ptrofs.zero) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_weak)
    [Vptr b (Ptrofs.repr 40)] E0 mw Vundef ->
  Clight2.eval_funcall secp_ge mw (Internal f_secp256k1_fe_negate)
    [Vptr b (Ptrofs.repr 40);Vptr b (Ptrofs.repr 40);Vint Int.one] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge empty_env le m gej_negate_y_tail E0 le mf Out_normal.
Proof.
  intros HR HW HN; unfold gej_negate_y_tail.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mw) (le1 := le).
  - destruct gej_negate_weak_symbol as (bf & HS & HF).
    eapply exec_Scall with (vf := Vptr bf Ptrofs.zero)
      (vargs := [Vptr b (Ptrofs.repr 40)])
      (f := Internal f_secp256k1_fe_normalize_weak) (vres := Vundef).
    + reflexivity.
    + eapply eval_Elvalue.
      * eapply eval_Evar_global; [reflexivity|exact HS].
      * apply deref_loc_reference; reflexivity.
    + eapply eval_Econs.
      * apply eval_gej_negate_y_address; exact HR.
      * reflexivity.
      * apply eval_Enil.
    + change (Genv.find_funct_ptr secp_ge bf = Some (Internal f_secp256k1_fe_normalize_weak)); exact HF.
    + reflexivity.
    + exact HW.
  - destruct gej_negate_field_symbol as (bf & HS & HF).
    eapply exec_Scall with (vf := Vptr bf Ptrofs.zero)
      (vargs := [Vptr b (Ptrofs.repr 40);Vptr b (Ptrofs.repr 40);Vint Int.one])
      (f := Internal f_secp256k1_fe_negate) (vres := Vundef).
    + reflexivity.
    + eapply eval_Elvalue.
      * eapply eval_Evar_global; [reflexivity|exact HS].
      * apply deref_loc_reference; reflexivity.
    + eapply eval_Econs.
      * apply eval_gej_negate_y_address; exact HR.
      * reflexivity.
      * eapply eval_Econs.
        -- apply eval_gej_negate_y_address; exact HR.
        -- reflexivity.
        -- eapply eval_Econs; [constructor|reflexivity|apply eval_Enil].
    + change (Genv.find_funct_ptr secp_ge bf = Some (Internal f_secp256k1_fe_negate)); exact HF.
    + reflexivity.
    + exact HN.
Qed.

Theorem exec_gej_negate_y_tail_owned le m b value :
  le!_r = Some (Vptr b Ptrofs.zero) ->
  0 <= value < 2^256 ->
  fe_at m b 40 (map Int64.repr (fe_limbs_of value)) ->
  Mem.range_perm m b 0 128 Cur Freeable ->
  exists mf,
    Clight2.exec_stmt secp_ge empty_env le m gej_negate_y_tail E0 le mf Out_normal /\
    fe_at mf b 40 (negate_values (write_fe_rho value 0)) /\
    Mem.range_perm mf b 0 128 Cur Freeable /\
    lframe (fun bx pos => ~ foot [(b,0)] (map rshape (point_write_initial_regs PointY)) bx pos) m mf.
Proof.
  intros HR HV HField HFree.
  destruct (point_y_arithmetic_calls m b value HV HField HFree)
    as (mw & mf & HW & HN & HFieldFinal & HFreeFinal & HFrame).
  exists mf; split.
  - eapply exec_gej_negate_y_tail_from_calls; eassumption.
  - split; [exact HFieldFinal|]; split; assumption.
Qed.
Timeout 60 Print Assumptions exec_gej_negate_y_tail_owned.
