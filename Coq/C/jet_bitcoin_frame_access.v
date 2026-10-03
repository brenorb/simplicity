(** Frame-field access in the actual Bitcoin composite environment. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Maps Memory Values Errors.
Require Import C.jet_frame_layout C.jets_bitcoin C.jet_bitcoin_linkage.
Import Ctypes Values Mem ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma bitcoin_frame_fields_checked :
  match (Clight.genv_cenv bitcoin_ge)!_frameItem with
  | Some co =>
    field_offset (Clight.genv_cenv bitcoin_ge) _edge (co_members co) = OK (0, Full) /\
    field_offset (Clight.genv_cenv bitcoin_ge) _offset (co_members co) = OK (8, Full)
  | None => False
  end.
Proof. vm_compute; split; reflexivity. Qed.

Lemma eval_bitcoin_frame_edge_at m le bf base bw edge :
  frame_base_valid base -> le!_frame = Some (Vptr bf (Ptrofs.repr base)) ->
  Mem.load Mptr m bf base = Some (Vptr bw edge) ->
  eval_expr bitcoin_ge empty_env le m
    (Efield (Ederef (Etempvar _frame (tptr (Tstruct _frameItem noattr)))
      (Tstruct _frameItem noattr)) _edge (tptr tulong)) (Vptr bw edge).
Proof.
  intros HB HE HM. pose proof bitcoin_frame_fields_checked as HF.
  destruct ((Clight.genv_cenv bitcoin_ge)!_frameItem) as [co|] eqn:HCo; [|contradiction].
  eapply eval_Elvalue.
  - eapply eval_Efield_struct with (co := co) (delta := 0).
    + eapply eval_Elvalue; [apply eval_Ederef, eval_Etempvar; exact HE|].
      apply deref_loc_copy; reflexivity.
    + reflexivity.
    + exact HCo.
    + exact (proj1 HF).
  - apply deref_loc_value with (chunk := Mptr); [reflexivity|].
    unfold Mem.loadv. rewrite frame_field_address by (assumption || lia).
    rewrite Z.add_0_r; exact HM.
Qed.

Lemma eval_bitcoin_frame_offset_lvalue_at m le bf base :
  le!_frame = Some (Vptr bf (Ptrofs.repr base)) ->
  eval_lvalue bitcoin_ge empty_env le m
    (Efield (Ederef (Etempvar _frame (tptr (Tstruct _frameItem noattr)))
      (Tstruct _frameItem noattr)) _offset tulong)
    bf (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 8)) Full.
Proof.
  intro HE. pose proof bitcoin_frame_fields_checked as HF.
  destruct ((Clight.genv_cenv bitcoin_ge)!_frameItem) as [co|] eqn:HCo; [|contradiction].
  eapply eval_Efield_struct with (co := co) (delta := 8).
  - eapply eval_Elvalue; [apply eval_Ederef, eval_Etempvar; exact HE|].
    apply deref_loc_copy; reflexivity.
  - reflexivity.
  - exact HCo.
  - exact (proj2 HF).
Qed.

Lemma eval_bitcoin_frame_offset_at m le bf base n :
  frame_base_valid base -> le!_frame = Some (Vptr bf (Ptrofs.repr base)) ->
  Mem.load Mint64 m bf (base + 8) = Some (Vlong n) ->
  eval_expr bitcoin_ge empty_env le m
    (Efield (Ederef (Etempvar _frame (tptr (Tstruct _frameItem noattr)))
      (Tstruct _frameItem noattr)) _offset tulong) (Vlong n).
Proof.
  intros HB HE HM. eapply eval_Elvalue; [apply eval_bitcoin_frame_offset_lvalue_at; exact HE|].
  apply deref_loc_value with (chunk := Mint64); [reflexivity|].
  unfold Mem.loadv. rewrite frame_field_address by (assumption || lia); exact HM.
Qed.

Lemma assign_bitcoin_frame_offset_at m mf bf base n :
  frame_base_valid base -> Mem.store Mint64 m bf (base + 8) (Vlong n) = Some mf ->
  assign_loc (Clight.genv_cenv bitcoin_ge) tulong m bf
    (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 8)) Full (Vlong n) mf.
Proof.
  intros HB HS. apply assign_loc_value with (chunk := Mint64); [reflexivity|].
  unfold Mem.storev. rewrite frame_field_address by (assumption || lia); exact HS.
Qed.

Lemma assign_bitcoin_frame_word_at m mf bw ofs w :
  Mem.store Mint64 m bw (Ptrofs.unsigned ofs) (Vlong w) = Some mf ->
  assign_loc (Clight.genv_cenv bitcoin_ge) tulong m bw ofs Full (Vlong w) mf.
Proof. intro HS. apply assign_loc_value with (chunk := Mint64); [reflexivity|exact HS]. Qed.
