(** Frame structures at arbitrary byte offsets, with non-wrapping field addresses.
    These contracts retain the actual CompCert block/offset memory layout. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Maps Memory Events.
Require Import C.jet_exec C.jet_frame_spec C.jets.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Definition frame_base_valid (base : Z) : Prop :=
  0 <= base /\ base + 16 <= Ptrofs.max_unsigned.

Definition frame_fields_at (m : mem) (bf : block) (base : Z)
    (bw : block) (edge cursor : Z) : Prop :=
  Mem.load Mptr m bf base = Some (Vptr bw (Ptrofs.repr edge)) /\
  Mem.load Mint64 m bf (base + 8) = Some (Vlong (Int64.repr cursor)).

Lemma frame_fields_at_zero m bf bw edge cursor :
  frame_fields_at m bf 0 bw edge cursor <-> frame_fields m bf bw edge cursor.
Proof. reflexivity. Qed.

Lemma frame_field_address base delta :
  frame_base_valid base -> 0 <= delta <= 8 ->
  Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr delta)) = base + delta.
Proof.
  intros [H0 HM] HD. unfold Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr base) by lia.
  rewrite (Ptrofs.unsigned_repr delta) by lia.
  apply Ptrofs.unsigned_repr; lia.
Qed.

Lemma eval_frame_edge_at m le bf base bw edge :
  frame_base_valid base ->
  le!_frame = Some (Vptr bf (Ptrofs.repr base)) ->
  Mem.load Mptr m bf base = Some (Vptr bw edge) ->
  eval_expr ge0 empty_env le m
    (Efield (Ederef (Etempvar _frame (tptr (Tstruct _frameItem noattr)))
       (Tstruct _frameItem noattr)) _edge (tptr tulong)) (Vptr bw edge).
Proof.
  intros HB HP HL. eapply eval_Elvalue.
  - eapply eval_Efield_struct.
    + eapply eval_Elvalue.
      * eapply eval_Ederef. eapply eval_Etempvar; exact HP.
      * apply deref_loc_copy; reflexivity.
    + reflexivity.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
  - apply deref_loc_value with (chunk := Mptr); [reflexivity |].
    unfold Mem.loadv.
    rewrite frame_field_address by (assumption || lia).
    replace (base + 0) with base by lia. exact HL.
Qed.

Lemma eval_frame_offset_at m le bf base n :
  frame_base_valid base ->
  le!_frame = Some (Vptr bf (Ptrofs.repr base)) ->
  Mem.load Mint64 m bf (base + 8) = Some (Vlong n) ->
  eval_expr ge0 empty_env le m
    (Efield (Ederef (Etempvar _frame (tptr (Tstruct _frameItem noattr)))
       (Tstruct _frameItem noattr)) _offset tulong) (Vlong n).
Proof.
  intros HB HP HL. eapply eval_Elvalue.
  - eapply eval_Efield_struct.
    + eapply eval_Elvalue.
      * eapply eval_Ederef. eapply eval_Etempvar; exact HP.
      * apply deref_loc_copy; reflexivity.
    + reflexivity.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
  - apply deref_loc_value with (chunk := Mint64); [reflexivity |].
    unfold Mem.loadv.
    rewrite frame_field_address by (assumption || lia). exact HL.
Qed.

Lemma eval_frame_offset_lvalue_at m le bf base :
  le!_frame = Some (Vptr bf (Ptrofs.repr base)) ->
  eval_lvalue ge0 empty_env le m
    (Efield (Ederef (Etempvar _frame (tptr (Tstruct _frameItem noattr)))
       (Tstruct _frameItem noattr)) _offset tulong)
    bf (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 8)) Full.
Proof.
  intros HP. eapply eval_Efield_struct.
  - eapply eval_Elvalue.
    + eapply eval_Ederef. eapply eval_Etempvar; exact HP.
    + apply deref_loc_copy; reflexivity.
  - reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Lemma assign_frame_offset_at m mf bf base n :
  frame_base_valid base ->
  Mem.store Mint64 m bf (base + 8) (Vlong n) = Some mf ->
  assign_loc (prog_comp_env prog) tulong m bf
    (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 8)) Full (Vlong n) mf.
Proof.
  intros HB HS. apply assign_loc_value with (chunk := Mint64); [reflexivity |].
  unfold Mem.storev.
  rewrite frame_field_address by (assumption || lia). exact HS.
Qed.
