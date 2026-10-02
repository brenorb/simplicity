(** Actual read4 crossing branch, with all cursor stores and helper calls.
    Reader infrastructure, not a public jet-equivalence claim. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_read8 C.jet_write8 C.jet_frame_layout.
Require Import C.jet_frame_access C.jet_frame_constants C.jet_frame_arith C.jets.
Require Import C.jet_read8_layout C.jet_LSBkeep_width C.jet_read4_layout.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Definition read4_narrow w := Int.zero_ext 8 (Int.repr (Int64.unsigned w)).
Definition read4_crossing_high k high :=
  Int.zero_ext 8 (Int.or Int.zero
    (Int.zero_ext 8 (Int.shl (read4_narrow (Int64.zero_ext k high))
      (Int64.loword (Int64.repr (4 - k)))))).
Definition read4_crossing_result k high low :=
  Int.zero_ext 8 (Int.or (read4_crossing_high k high)
    (read4_narrow (Int64.zero_ext (4 - k) (Int64.shru low (Int64.repr (60 + k)))))).

Lemma read4_crossing_arithmetic k : 1 <= k <= 3 ->
  Int64.divu (Int64.repr (64 - k)) (Int64.repr 64) = Int64.zero /\
  Int64.modu (Int64.repr (64 - k)) (Int64.repr 64) = Int64.repr (64 - k) /\
  Int64.sub (Int64.repr 64) (Int64.repr (64 - k)) = Int64.repr k /\
  Int64.ltu (Int64.repr k) (Int64.repr 4) = true /\
  Int64.sub (Int64.repr 4) (Int64.repr k) = Int64.repr (4 - k) /\
  Int64.ltu (Int64.repr (4 - k)) (Int64.repr 32) = true /\
  Int64.add (Int64.repr (64 - k)) (Int64.repr k) = Int64.repr 64 /\
  Int64.ltu (Int64.repr 64) (Int64.repr (4 - k)) = false /\
  Int64.sub (Int64.repr 64) (Int64.repr (4 - k)) = Int64.repr (60 + k) /\
  Int64.ltu (Int64.repr (60 + k)) Int64.iwordsize = true /\
  Int64.add (Int64.repr 64) (Int64.repr (4 - k)) = Int64.repr (68 - k).
Proof.
  intros HK. assert (HC : k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct HC as [-> | [-> | ->]]; repeat split; reflexivity.
Qed.

Ltac read4layout_cross_stmt :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [read4layout_cross_stmt | read4layout_cross_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      apply exec_set; read4layout_expr
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true);
        [read4layout_expr | reflexivity | read4layout_cross_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Swhile _ _) _ _ _ _ =>
      unfold Swhile; read4layout_cross_stmt
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sloop _ _) _ _ _ _ =>
      eapply exec_Sloop_stop1 with (out' := Out_break);
      [ eapply exec_Sseq_2;
        [ eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
          [read4layout_expr | reflexivity | apply exec_Sbreak]
        | discriminate ]
      | constructor ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBkeep _) _) _ _ _ _ =>
      eapply call_word_helper with (f := f_LSBkeep);
      [ reflexivity | reflexivity | reflexivity | apply symbol_LSBkeep | apply funct_LSBkeep
      | read4layout_expr | read4layout_expr | apply eval_keep_width; lia ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign (Efield _ _offset _) _) _ _ _ _ =>
      eapply exec_Sassign_value;
      [ apply eval_frame_offset_lvalue_at; reflexivity | read4layout_expr | read4layout_scalar
      | eapply assign_frame_offset_at; [eassumption | read4layout_scalar] ]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      apply exec_Sreturn_some; read4layout_expr
  end.

Lemma eval_read4_layout_crossing_raw m mm mf bf base bw edge cursor k high low :
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - 4 ->
  1 <= k <= 3 -> cursor mod 64 = 64 - k ->
  8 * (2 + cursor / 64) <= edge <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Mem.store Mint64 m bf (base + 8) (Vlong (Int64.repr (cursor + k))) = Some mm ->
  Mem.load Mint64 mm bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low) ->
  Mem.load Mint64 mm bf (base + 8) = Some (Vlong (Int64.repr (cursor + k))) ->
  Mem.store Mint64 mm bf (base + 8) (Vlong (Int64.repr (cursor + 4))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read4)
    [Vptr bf (Ptrofs.repr base)] E0 mf (Vint (read4_crossing_result k high low)).
Proof.
  intros HB HC HK HR HE [HF HO] HH SM HL HOm SF.
  assert (HQ : 0 <= cursor / 64 <= Int64.max_unsigned).
  { split; [apply Z.div_pos; lia |]. apply Z.div_le_upper_bound; lia. }
  pose proof (read4_layout_index cursor HC) as [HIdiv [HImod HIadd]].
  rewrite HR in HImod.
  pose proof (read8_layout_pointer edge (cursor / 64) HQ ltac:(lia)) as [HPfirst HPword].
  assert (HPnext : Ptrofs.sub (Ptrofs.repr (edge - 8 * (1 + cursor / 64)))
      (Ptrofs.repr 8) = Ptrofs.repr (edge - 8 * (2 + cursor / 64))).
  { unfold Ptrofs.sub. rewrite Ptrofs.unsigned_repr by lia.
    change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8. f_equal; lia. }
  pose proof (read4_crossing_arithmetic k HK)
    as [HAdiv [HAmod [HAsub [HAltu [HAsub8 [HAshift [HAadd [HALtu [HASub [HAShift HAAdd]]]]]]]]]].
  assert (HStep : Int64.add (Int64.repr cursor) (Int64.repr k) = Int64.repr (cursor + k)).
  { unfold Int64.add. rewrite (Int64.unsigned_repr cursor) by lia.
    rewrite cursor_unsigned by lia. reflexivity. }
  assert (HFinal : Int64.add (Int64.repr (cursor + k)) (Int64.repr (4 - k)) =
      Int64.repr (cursor + 4)).
  { unfold Int64.add. rewrite (Int64.unsigned_repr (cursor + k)) by lia.
    rewrite cursor_unsigned by lia. f_equal; lia. }
  assert (HHp : Mem.load Mint64 m bw
      (Ptrofs.unsigned (Ptrofs.repr (edge - 8 * (1 + cursor / 64)))) = Some (Vlong high)).
  { rewrite Ptrofs.unsigned_repr by lia. exact HH. }
  assert (HLp : Mem.load Mint64 mm bw
      (Ptrofs.unsigned (Ptrofs.repr (edge - 8 * (2 + cursor / 64)))) = Some (Vlong low)).
  { rewrite Ptrofs.unsigned_repr by lia. exact HL. }
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_read4_layout bf base) (m1 := m)
      (m2 := mf) (out := Out_return (Some (Vint (read4_crossing_result k high low), tuchar)))
      (vres := Vint (read4_crossing_result k high low)).
  - apply entry_read4_layout.
  - unfold f_simplicity_read4; cbn [fn_body]. timeout 10 read4layout_cross_stmt.
  - cbn; split; [discriminate |].
    change (Some (Vint (Int.zero_ext 8 (read4_crossing_result k high low))) =
      Some (Vint (read4_crossing_result k high low))).
    unfold read4_crossing_result. rewrite Int.zero_ext_idem by lia. reflexivity.
  - reflexivity.
Qed.

