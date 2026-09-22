(** Actual write8 crossing branch for arbitrary payload bytes.
    The high word is at offset 8, the next word at offset 0. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_write8 C.jets C.jet_frame_arith C.jet_frame_constants
  C.jet_frame_access C.jet_LSBclear_width C.jet_LSBkeep_width C.jet_word_bits C.jet_crossing_arith.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Require Import C.jet_write8_crossing.

Definition crossing_high (k : Z) (old : int64) (x : int) : int64 :=
  Int64.or (clear_low k old)
    (Int64.zero_ext k
      (Int64.repr (Int.signed (Int.shr x (Int64.loword (Int64.repr (8 - k))))))).

Definition crossing_low (k : Z) (x : int) : int64 :=
  Int64.shl (Int64.zero_ext (8 - k) (Int64.repr (Int.unsigned x)))
    (Int64.repr (56 + k)).

Lemma eval_write8_crossing_raw m mh mo ml mf bd bw k oldhigh oldlow x :
  1 <= k <= 7 ->
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr (64 + k))) ->
  Mem.load Mint64 m bw 8 = Some (Vlong oldhigh) ->
  Mem.store Mint64 m bw 8 (Vlong (crossing_high k oldhigh x)) = Some mh ->
  Mem.load Mint64 mh bd 8 = Some (Vlong (Int64.repr (64 + k))) ->
  Mem.store Mint64 mh bd 8 (Vlong (Int64.repr 64)) = Some mo ->
  Mem.load Mint64 mo bw 0 = Some (Vlong oldlow) ->
  Mem.store Mint64 mo bw 0 (Vlong (crossing_low k x)) = Some ml ->
  Mem.load Mint64 ml bd 8 = Some (Vlong (Int64.repr 64)) ->
  Mem.store Mint64 ml bd 8 (Vlong (Int64.repr (56 + k))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
    [Vptr bd Ptrofs.zero; Vint x] E0 mf Vundef.
Proof.
  intros HK HE HO HH SH HOh SO HL SL HOl SF.
  pose proof (byte_crossing_arithmetic_holds k HK) as HA.
  unfold byte_crossing_arithmetic in HA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_write8_x bd x) (m1 := m)
      (m2 := mf) (out := Out_normal) (vres := Vundef).
  - apply entry_write8_x.
  - unfold f_simplicity_write8; cbn [fn_body].
    timeout 10 crossing_stmt.
  - reflexivity.
  - reflexivity.
Qed.

(** Initial loads suffice: all intervening reads follow from the four stores. *)
Lemma eval_write8_crossing m mh mo ml mf bd bw k oldhigh oldlow x :
  1 <= k <= 7 ->
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr (64 + k))) ->
  Mem.load Mint64 m bw 8 = Some (Vlong oldhigh) ->
  Mem.load Mint64 m bw 0 = Some (Vlong oldlow) ->
  Mem.store Mint64 m bw 8 (Vlong (crossing_high k oldhigh x)) = Some mh ->
  Mem.store Mint64 mh bd 8 (Vlong (Int64.repr 64)) = Some mo ->
  Mem.store Mint64 mo bw 0 (Vlong (crossing_low k x)) = Some ml ->
  Mem.store Mint64 ml bd 8 (Vlong (Int64.repr (56 + k))) = Some mf ->
  bd <> bw ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
    [Vptr bd Ptrofs.zero; Vint x] E0 mf Vundef.
Proof.
  intros HK HE HO HH HL SH SO SL SF Hneq.
  eapply eval_write8_crossing_raw; eauto.
  - rewrite <- HO. eapply Mem.load_store_other; [exact SH | auto].
  - erewrite Mem.load_store_other; [|exact SO|auto].
    erewrite Mem.load_store_other; [exact HL|exact SH|right; left; cbn; lia].
  - erewrite Mem.load_store_other; [|exact SL|auto].
    exact (Mem.load_store_same _ _ _ _ _ _ SO).
Qed.

