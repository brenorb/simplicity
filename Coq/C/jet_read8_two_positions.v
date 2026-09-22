(** Generated read8 for every non-crossing input cursor within a word. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_read8 C.jet_write8 C.jets
  C.jet_frame_arith C.jet_frame_constants C.jet_frame_access.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Require Import C.jet_read8_position.

Lemma eval_read8_high m mf bf bw w cursor :
  0 <= cursor <= 56 ->
  Mem.load Mptr m bf 0 = Some (Vptr bw (Ptrofs.repr 16)) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr cursor)) ->
  Mem.load Mint64 m bw 8 = Some (Vlong w) ->
  Mem.store Mint64 m bf 8 (Vlong (Int64.repr (cursor + 8))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read8)
    [Vptr bf Ptrofs.zero] E0 mf (Vint (read8_at cursor w)).
Proof.
  intros HC HE HO HW SF.
  pose proof (read8_cursor_arithmetic cursor HC) as HA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_read8 bf) (m1 := m)
      (m2 := mf) (out := Out_return (Some (Vint (read8_at cursor w), tuchar)))
      (vres := Vint (read8_at cursor w)).
  - apply entry_read8.
  - unfold f_simplicity_read8; cbn [fn_body].
    timeout 10 readpos_stmt.
  - cbn; split; [discriminate |].
    change (Some (Vint (Int.zero_ext 8 (read8_at cursor w))) = Some (Vint (read8_at cursor w))).
    unfold read8_at, read8_result. rewrite Int.zero_ext_idem by lia. reflexivity.
  - reflexivity.
Qed.

Lemma eval_read8_low m mf bf bw w cursor :
  64 <= cursor <= 120 ->
  Mem.load Mptr m bf 0 = Some (Vptr bw (Ptrofs.repr 16)) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr cursor)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong w) ->
  Mem.store Mint64 m bf 8 (Vlong (Int64.repr (cursor + 8))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read8)
    [Vptr bf Ptrofs.zero] E0 mf (Vint (read8_at (cursor - 64) w)).
Proof.
  intros HC HE HO HW SF.
  pose proof (read8_cursor_arithmetic (cursor - 64) ltac:(lia)) as HA.
  assert (HD : Int64.divu (Int64.repr cursor) (Int64.repr 64) = Int64.one).
  { unfold Int64.divu. rewrite !cursor_unsigned by lia.
    replace (cursor / 64) with 1; [reflexivity |].
    apply Z.div_unique with (r := cursor - 64); lia. }
  assert (HM : Int64.modu (Int64.repr cursor) (Int64.repr 64) = Int64.repr (cursor - 64)).
  { unfold Int64.modu. rewrite !cursor_unsigned by lia.
    f_equal. symmetry. apply Z.mod_unique with (q := 1); lia. }
  assert (HAdd : Int64.add (Int64.repr cursor) (Int64.repr 8) = Int64.repr (cursor + 8)).
  { unfold Int64.add. rewrite !cursor_unsigned by lia. reflexivity. }
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_read8 bf) (m1 := m)
      (m2 := mf) (out := Out_return (Some (Vint (read8_at (cursor - 64) w), tuchar)))
      (vres := Vint (read8_at (cursor - 64) w)).
  - apply entry_read8.
  - unfold f_simplicity_read8; cbn [fn_body].
    timeout 10 readpos_stmt.
  - cbn; split; [discriminate |].
    change (Some (Vint (Int.zero_ext 8 (read8_at (cursor - 64) w))) = Some (Vint (read8_at (cursor - 64) w))).
    unfold read8_at, read8_result. rewrite Int.zero_ext_idem by lia. reflexivity.
  - reflexivity.
Qed.

