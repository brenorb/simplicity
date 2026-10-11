(** Actual generated affine Y address and original arithmetic statements. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events Globalenvs.
Require Import C.jet_exec C.jet_sx_expr C.jet_sx_state C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_write_fe_numeric C.jet_secp_field_negate_storage.
Require Import C.jet_secp_affine_self_copy C.jet_secp_affine_y_output.
Require Import C.jet_secp_gej_negate_y_tail.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma affine_field_members :
  option_map co_members ((genv_cenv secp_ge)!__6121) =
  Some [Member_plain _x (Tstruct __5467 noattr);
        Member_plain _y (Tstruct __5467 noattr); Member_plain _infinity tint].
Proof. vm_compute; reflexivity. Qed.

Lemma affine_y_field_layout :
  exists co, (genv_cenv secp_ge)!__6121 = Some co /\
    field_offset secp_ge _y (co_members co) = Errors.OK (40,Full).
Proof.
  pose proof affine_field_members as HM.
  destruct ((genv_cenv secp_ge)!__6121) as [co|] eqn:HC; [|discriminate].
  exists co; split; [reflexivity|].
  inversion HM as [HMembers]; rewrite HMembers; vm_compute; reflexivity.
Qed.

Definition affine_negate_y_address : expr :=
  Eaddrof (Efield (Ederef (Etempvar _r (tptr (Tstruct __6121 noattr)))
    (Tstruct __6121 noattr)) _y (Tstruct __5467 noattr)) (tptr (Tstruct __5467 noattr)).
Definition affine_negate_y_tail : statement :=
  Ssequence
    (Scall None (Evar _secp256k1_fe_normalize_weak (Tfunction
      (Tcons (tptr (Tstruct __5467 noattr)) Tnil) tvoid cc_default))
      [affine_negate_y_address])
    (Scall None (Evar _secp256k1_fe_negate (Tfunction
      (Tcons (tptr (Tstruct __5467 noattr))
        (Tcons (tptr (Tstruct __5467 noattr)) (Tcons tint Tnil))) tvoid cc_default))
      [affine_negate_y_address;affine_negate_y_address;Econst_int (Int.repr 1) tint]).
Lemma affine_negate_helper_body : fn_body f_secp256k1_ge_neg =
  Ssequence affine_negate_copy_stmt affine_negate_y_tail.
Proof. reflexivity. Qed.
Local Opaque secp_ge.

Lemma eval_affine_negate_y_address le m b :
  le!_r = Some (Vptr b Ptrofs.zero) ->
  eval_expr secp_ge empty_env le m affine_negate_y_address (Vptr b (Ptrofs.repr 40)).
Proof.
  intro HR; unfold affine_negate_y_address; apply eval_Eaddrof.
  destruct affine_y_field_layout as (co & HC & HO).
  replace (Ptrofs.repr 40) with (Ptrofs.add Ptrofs.zero (Ptrofs.repr 40)) by reflexivity.
  eapply eval_Efield_struct with (co := co) (delta := 40).
  - eapply eval_Elvalue.
    + apply eval_Ederef; apply eval_Etempvar; exact HR.
    + apply deref_loc_copy; reflexivity.
  - reflexivity.
  - exact HC.
  - exact HO.
Qed.

Lemma exec_affine_negate_y_tail_from_calls le m mw mf b :
  le!_r = Some (Vptr b Ptrofs.zero) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_weak)
    [Vptr b (Ptrofs.repr 40)] E0 mw Vundef ->
  Clight2.eval_funcall secp_ge mw (Internal f_secp256k1_fe_negate)
    [Vptr b (Ptrofs.repr 40);Vptr b (Ptrofs.repr 40);Vint Int.one] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge empty_env le m affine_negate_y_tail E0 le mf Out_normal.
Proof.
  intros HR HW HN; unfold affine_negate_y_tail.
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
      * apply eval_affine_negate_y_address; exact HR.
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
      * apply eval_affine_negate_y_address; exact HR.
      * reflexivity.
      * eapply eval_Econs.
        -- apply eval_affine_negate_y_address; exact HR.
        -- reflexivity.
        -- eapply eval_Econs; [constructor|reflexivity|apply eval_Enil].
    + change (Genv.find_funct_ptr secp_ge bf = Some (Internal f_secp256k1_fe_negate)); exact HF.
    + reflexivity.
    + exact HN.
Qed.
Print Assumptions exec_affine_negate_y_tail_from_calls.
