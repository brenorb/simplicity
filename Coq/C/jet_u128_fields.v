(** Actual LP64 uint128 struct fields and both getter calls. The source-order
    lo/hi layout is independent of the high/low output serialization order. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition u128_field (high : bool) := if high then _hi else _lo.
Definition u128_field_offset (high : bool) : Z := if high then 8 else 0.
Definition u128_field_expr high id := Efield
  (Ederef (Etempvar id (tptr (Tstruct _secp256k1_uint128 noattr)))
    (Tstruct _secp256k1_uint128 noattr)) (u128_field high) tulong.
Definition u128_get (high : bool) := if high then f_secp256k1_u128_hi_u64 else f_secp256k1_u128_to_u64.
Definition u128_get_id (high : bool) := if high then _secp256k1_u128_hi_u64 else _secp256k1_u128_to_u64.
Definition u128_get_temps high br base := PTree.set _a (Vptr br (Ptrofs.repr base))
  (create_undef_temps (u128_get high).(fn_temps)).

Lemma eval_u128_field_lvalue high id e le m br base :
  le!id = Some (Vptr br (Ptrofs.repr base)) ->
  eval_lvalue ge0 e le m (u128_field_expr high id)
    br (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr (u128_field_offset high))) Full.
Proof.
  intros HP. eapply eval_Efield_struct.
  - eapply eval_Elvalue.
    + apply eval_Ederef. apply eval_Etempvar; exact HP.
    + apply deref_loc_copy; reflexivity.
  - reflexivity.
  - vm_compute; reflexivity.
  - destruct high; vm_compute; reflexivity.
Qed.

Lemma eval_u128_field high id e le m br base w :
  frame_base_valid base -> le!id = Some (Vptr br (Ptrofs.repr base)) ->
  Mem.load Mint64 m br (base + u128_field_offset high) = Some (Vlong w) ->
  eval_expr ge0 e le m (u128_field_expr high id) (Vlong w).
Proof.
  intros HB HP HL. eapply eval_Elvalue.
  - apply eval_u128_field_lvalue; exact HP.
  - apply deref_loc_value with (chunk := Mint64); [reflexivity|].
    unfold Mem.loadv. rewrite frame_field_address by (assumption || destruct high; cbn; lia). exact HL.
Qed.

Lemma u128_get_body high : (u128_get high).(fn_body) =
  Ssequence (Sset _t'1 (u128_field_expr high _a)) (Sreturn (Some (Etempvar _t'1 tulong))).
Proof. destruct high; reflexivity. Qed.

Lemma u128_get_symbol high : Genv.find_symbol (Clight.genv_genv ge0) (u128_get_id high) =
  Some (jet_symbol_block (u128_get_id high)).
Proof. destruct high; vm_compute; reflexivity. Qed.
Lemma u128_get_funct high : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block (u128_get_id high)) Ptrofs.zero) = Some (Internal (u128_get high)).
Proof. destruct high; vm_compute; reflexivity. Qed.

Theorem eval_u128_get_layout high m br base w : frame_base_valid base ->
  Mem.load Mint64 m br (base + u128_field_offset high) = Some (Vlong w) ->
  Clight2.eval_funcall ge0 m (Internal (u128_get high)) [Vptr br (Ptrofs.repr base)] E0 m (Vlong w).
Proof.
  intros HB HL.
  set (le0 := u128_get_temps high br base). set (le1 := PTree.set _t'1 (Vlong w) le0).
  eapply eval_funcall_internal with (e := PTree.empty _) (le1 := le0) (le2 := le1)
    (m1 := m) (m2 := m) (out := Out_return (Some (Vlong w,tulong))).
  - constructor.
    + destruct high; constructor.
    + destruct high; change (list_norepet [_a]); repeat constructor; cbn; tauto.
    + destruct high; change (list_disjoint [_a] [_t'1]); vm_compute; intuition congruence.
    + destruct high; constructor.
    + destruct high; reflexivity.
  - rewrite u128_get_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
    + apply exec_set. eapply eval_u128_field; [exact HB|unfold le0, u128_get_temps; apply PTree.gss|exact HL].
    + apply exec_Sreturn_some. apply eval_Etempvar. unfold le1; apply PTree.gss.
  - destruct high; cbn; split; solve [discriminate|reflexivity].
  - reflexivity.
Qed.
