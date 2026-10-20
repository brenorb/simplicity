(** Typed call adapters; the public-body theorem discharges their executions. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_multiply_public_layout.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma exec_read_call e le m mf id b bl :
  e!id = Some (b, field_type) -> e!jets_secp._src = Some (bl, frame_type) ->
  e!jets_secp._read_fe = None ->
  Clight2.eval_funcall secp_ge m (Internal f_read_fe)
    [Vptr b Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m (read_stmt id) E0 le mf Out_normal.
Proof.
  intros HA HL HNone HCall; destruct helper_symbols as (HS & HF & _).
  eapply exec_Scall with (vf := Vptr (secp_symbol_block jets_secp._read_fe) Ptrofs.zero)
    (vargs := [Vptr b Ptrofs.zero; Vptr bl Ptrofs.zero]) (f := Internal f_read_fe) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [eapply eval_Evar_global; [exact HNone|exact HS]|apply deref_loc_reference; reflexivity].
  - eapply eval_Econs.
    + apply eval_Eaddrof; apply eval_Evar_local; exact HA.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof; apply eval_Evar_local; exact HL.
      * reflexivity.
      * apply eval_Enil.
  - exact HF.
  - reflexivity.
  - exact HCall.
Qed.

Lemma exec_mul_call e le m mf ba bb :
  e!jets_secp._a = Some (ba, field_type) -> e!jets_secp._b = Some (bb, field_type) ->
  e!jets_secp._secp256k1_fe_mul = None ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m mul_stmt E0 le mf Out_normal.
Proof.
  intros HA HB HNone HCall; destruct helper_symbols as (_ & _ & _ & _ & HS & HF).
  eapply exec_Scall with (vf := Vptr (secp_symbol_block jets_secp._secp256k1_fe_mul) Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero])
    (f := Internal f_secp256k1_fe_mul) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [eapply eval_Evar_global; [exact HNone|exact HS]|apply deref_loc_reference; reflexivity].
  - eapply eval_Econs.
    + apply eval_Eaddrof; apply eval_Evar_local; exact HA.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof; apply eval_Evar_local; exact HA.
      * reflexivity.
      * eapply eval_Econs.
        -- apply eval_Eaddrof; apply eval_Evar_local; exact HB.
        -- reflexivity.
        -- apply eval_Enil.
  - exact HF.
  - reflexivity.
  - exact HCall.
Qed.

Lemma exec_write_call e le m mf ba bd dbase :
  e!jets_secp._a = Some (ba, field_type) -> e!jets_secp._write_fe = None ->
  le!jets_secp._dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_write_fe)
    [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m write_stmt E0 le mf Out_normal.
Proof.
  intros HA HNone HDst HCall; destruct helper_symbols as (_ & _ & HS & HF & _).
  eapply exec_Scall with (vf := Vptr (secp_symbol_block jets_secp._write_fe) Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero]) (f := Internal f_write_fe) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [eapply eval_Evar_global; [exact HNone|exact HS]|apply deref_loc_reference; reflexivity].
  - eapply eval_Econs.
    + apply eval_Etempvar; exact HDst.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof; apply eval_Evar_local; exact HA.
      * reflexivity.
      * apply eval_Enil.
  - exact HF.
  - reflexivity.
  - exact HCall.
Qed.

Lemma exec_four_call_body le m ma mr mm mf bl ba bb bd dbase :
  le!jets_secp._dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_read_fe) [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero] E0 ma Vundef ->
  Clight2.eval_funcall secp_ge ma (Internal f_read_fe) [Vptr bb Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mr Vundef ->
  Clight2.eval_funcall secp_ge mr (Internal f_secp256k1_fe_mul)
    [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero] E0 mm Vundef ->
  Clight2.eval_funcall secp_ge mm (Internal f_write_fe) [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (public_env bl ba bb) le m rest_stmt E0 le mf
    (Out_return (Some (Vint Int.one, tint))).
Proof.
  intros HD HA HB HM HW; unfold rest_stmt.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ma) (le1 := le).
  - eapply exec_read_call; [reflexivity|reflexivity|reflexivity|exact HA].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := le).
    + eapply exec_read_call; [reflexivity|reflexivity|reflexivity|exact HB].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mm) (le1 := le).
      * eapply exec_mul_call; [reflexivity|reflexivity|reflexivity|exact HM].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf) (le1 := le).
        -- eapply exec_write_call; [reflexivity|reflexivity|exact HD|exact HW].
        -- apply exec_Sreturn_some; constructor.
Qed.
