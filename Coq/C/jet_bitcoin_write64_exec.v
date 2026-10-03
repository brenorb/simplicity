(** Actual Bitcoin-program write64 execution, reusing core arithmetic and pure
    word-helper proofs. Raw store composition is internal, not public coverage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps ClightBigstep Memory Events.
Require Import C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_frame_arith C.jet_word_slice.
Require Import C.jet_frame_access C.jet_frame_constants C.jet_write_wide_layout C.jet_wide.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_frame_access C.jet_bitcoin_word_helpers.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge.
Set Default Timeout 10.

Ltac bitcoin_writer_expr :=
  first [solve [apply eval_generated_uword_bits]
    | solve [eapply eval_bitcoin_frame_edge_at; [eassumption|reflexivity|eassumption]]
    | solve [eapply eval_bitcoin_frame_offset_at; [eassumption|reflexivity|eassumption]]
    | solve [eapply eval_Elvalue; [eapply eval_Ederef; apply eval_Etempvar; reflexivity|
        eapply deref_loc_value; [reflexivity|eassumption]]]
    | (apply eval_Etempvar; reflexivity)
    | (eapply eval_Ecast; [bitcoin_writer_expr|writelayout_scalar])
    | (eapply eval_Eunop; [bitcoin_writer_expr|writelayout_scalar])
    | (eapply eval_Ebinop; [bitcoin_writer_expr|bitcoin_writer_expr|writelayout_scalar])
    | apply eval_Econst_int | apply eval_Econst_long].

Ltac bitcoin_writer_call funbody sym funproof :=
  eapply call_word_helper_ge with (f := funbody);
  [reflexivity|reflexivity|reflexivity|apply sym|apply funproof|
   bitcoin_writer_expr|bitcoin_writer_expr|
   first [apply eval_bitcoin_clear_width; lia|apply eval_bitcoin_keep_width; lia]].

Ltac bitcoin_writer_assign :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign (Efield _ _offset _) _) _ _ _ _ =>
    eapply exec_Sassign_value;
    [apply eval_bitcoin_frame_offset_lvalue_at; reflexivity|bitcoin_writer_expr|writelayout_scalar|
     eapply assign_bitcoin_frame_offset_at; [eassumption|first [eassumption|writelayout_scalar]]]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign (Ederef _ _) _) _ _ _ _ =>
    eapply exec_Sassign_value;
    [apply eval_Ederef, eval_Etempvar; reflexivity|bitcoin_writer_expr|writelayout_scalar|
     apply assign_bitcoin_frame_word_at; first [eassumption|writelayout_scalar]]
  end.

Ltac bitcoin_writer_stmt :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [bitcoin_writer_stmt|bitcoin_writer_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ => apply exec_set; bitcoin_writer_expr
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
    first [eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
      [bitcoin_writer_expr|reflexivity|apply exec_Sskip]
    | eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true);
      [bitcoin_writer_expr|reflexivity|bitcoin_writer_stmt]]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Swhile _ _) _ _ _ _ => unfold Swhile; bitcoin_writer_stmt
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sloop _ _) _ _ _ _ =>
    eapply exec_Sloop_stop1 with (out' := Out_break);
    [eapply exec_Sseq_2;
      [eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
        [bitcoin_writer_expr|reflexivity|apply exec_Sbreak]|discriminate]|constructor]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBclear _) _) _ _ _ _ =>
    bitcoin_writer_call f_LSBclear bitcoin_clear_symbol bitcoin_clear_funct
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBkeep _) _) _ _ _ _ =>
    bitcoin_writer_call f_LSBkeep bitcoin_keep_symbol bitcoin_keep_funct
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ => bitcoin_writer_assign
  end.

Lemma entry_bitcoin_write64 m bf base x :
  function_entry2 bitcoin_ge f_simplicity_write64 [Vptr bf (Ptrofs.repr base); Vlong x]
    m empty_env (le_write_wide W64 bf base x) m.
Proof.
  constructor; try constructor; try reflexivity.
  all: try (repeat constructor; simpl; intuition discriminate).
  all: intros id1 id2 H1 H2 Heq; simpl in H1, H2; subst id2;
      destruct H1 as [H1|[H1|H1]]; repeat (destruct H2 as [H2|H2]);
      vm_compute in H1, H2; congruence.
Qed.

Lemma eval_bitcoin_write64_crossing_raw m mh mo ml mf bf base bw edge cursor k oldhigh oldlow x :
  frame_base_valid base -> 64 <= cursor <= Int64.max_unsigned ->
  1 <= k < 64 -> write_word_shift cursor = k ->
  0 <= edge -> 8 <= write_word_address edge cursor ->
  write_word_address edge cursor + 8 <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong oldhigh) ->
  Mem.store Mint64 m bw (write_word_address edge cursor)
    (Vlong (slice_high 64 k oldhigh x)) = Some mh ->
  Mem.load Mint64 mh bf (base + 8) = Some (Vlong (Int64.repr cursor)) ->
  Mem.store Mint64 mh bf (base + 8) (Vlong (Int64.repr (cursor - k))) = Some mo ->
  Mem.load Mint64 mo bw (write_word_address edge cursor - 8) = Some (Vlong oldlow) ->
  Mem.store Mint64 mo bw (write_word_address edge cursor - 8)
    (Vlong (slice_low 64 k x)) = Some ml ->
  Mem.load Mint64 ml bf (base + 8) = Some (Vlong (Int64.repr (cursor - k))) ->
  Mem.store Mint64 ml bf (base + 8) (Vlong (Int64.repr (cursor - 64))) = Some mf ->
  Clight2.eval_funcall bitcoin_ge m (Internal f_simplicity_write64)
    [Vptr bf (Ptrofs.repr base); Vlong x] E0 mf Vundef.
Proof.
  intros HB HC HK HKdef HE HA0 HA [HF HO] HH SH HOh SO HL SL HOl SF.
  pose proof (write_layout_index cursor ltac:(lia)) as [HQ [HK' [Hsub [Hdiv [Hmod Hwidth]]]]].
  rewrite HKdef in Hwidth.
  pose proof (write_layout_pointer edge ((cursor - 1) / 64) HQ HE
    ltac:(unfold write_word_address in HA; lia)) as Hptr.
  fold (write_word_address edge cursor) in Hptr.
  assert (Haddr : Ptrofs.unsigned (Ptrofs.repr (write_word_address edge cursor)) =
      write_word_address edge cursor) by (apply Ptrofs.unsigned_repr; lia).
  assert (HaddrL : Ptrofs.unsigned (Ptrofs.repr (write_word_address edge cursor - 8)) =
      write_word_address edge cursor - 8) by (apply Ptrofs.unsigned_repr; lia).
  assert (HptrL : Ptrofs.sub (Ptrofs.repr (write_word_address edge cursor)) (Ptrofs.repr 8) =
      Ptrofs.repr (write_word_address edge cursor - 8)).
  { unfold Ptrofs.sub. rewrite Haddr. reflexivity. }
  assert (HHp : Mem.load Mint64 m bw
      (Ptrofs.unsigned (Ptrofs.repr (write_word_address edge cursor))) = Some (Vlong oldhigh))
    by (rewrite Haddr; exact HH).
  assert (HLp : Mem.load Mint64 mo bw
      (Ptrofs.unsigned (Ptrofs.repr (write_word_address edge cursor - 8))) = Some (Vlong oldlow))
    by (rewrite HaddrL; exact HL).
  assert (SHp : Mem.store Mint64 m bw
      (Ptrofs.unsigned (Ptrofs.repr (write_word_address edge cursor)))
      (Vlong (slice_high 64 k oldhigh x)) = Some mh) by (rewrite Haddr; exact SH).
  assert (SLp : Mem.store Mint64 mo bw
      (Ptrofs.unsigned (Ptrofs.repr (write_word_address edge cursor - 8)))
      (Vlong (slice_low 64 k x)) = Some ml) by (rewrite HaddrL; exact SL).
  assert (Hcross : Int64.ltu (Int64.repr k) (Int64.repr 64) = true).
  { unfold Int64.ltu. rewrite !cursor_unsigned by lia. rewrite zlt_true by lia; reflexivity. }
  pose proof (cursor_sub 64 k ltac:(lia) ltac:(lia)) as Hremain.
  pose proof (cursor_sub 64 (64 - k) ltac:(lia) ltac:(lia)) as Hshift_sub.
  assert (Hshr : Int64.ltu (Int64.repr (64 - k)) Int64.iwordsize = true).
  { unfold Int64.ltu. rewrite cursor_unsigned by lia.
    change ((if zlt (64 - k) 64 then true else false) = true).
    rewrite zlt_true by lia; reflexivity. }
  assert (Hshift : Int64.ltu (Int64.repr (64 - (64 - k))) Int64.iwordsize = true).
  { unfold Int64.ltu. rewrite cursor_unsigned by lia.
    change ((if zlt (64 - (64 - k)) 64 then true else false) = true).
    rewrite zlt_true by lia; reflexivity. }
  assert (Hstop : Int64.ltu (Int64.repr 64) (Int64.repr (64 - k)) = false).
  { unfold Int64.ltu. rewrite !cursor_unsigned by lia. rewrite zlt_false by lia; reflexivity. }
  assert (Hfirst : Int64.sub (Int64.repr cursor) (Int64.repr k) = Int64.repr (cursor - k)).
  { unfold Int64.sub. rewrite (Int64.unsigned_repr cursor) by lia.
    rewrite cursor_unsigned by lia; reflexivity. }
  assert (Hfinal : Int64.sub (Int64.repr (cursor - k)) (Int64.repr (64 - k)) =
      Int64.repr (cursor - 64)).
  { unfold Int64.sub. rewrite (Int64.unsigned_repr (cursor - k)) by lia.
    rewrite cursor_unsigned by lia. f_equal; lia. }
  unfold slice_high in SHp. unfold slice_low in SLp.
  eapply eval_funcall_internal with (e := empty_env) (le1 := le_write_wide W64 bf base x)
    (m1 := m) (m2 := mf) (out := Out_normal) (vres := Vundef).
  - apply entry_bitcoin_write64.
  - unfold f_simplicity_write64; cbn [fn_body]; bitcoin_writer_stmt.
  - reflexivity.
  - reflexivity.
Qed.

Lemma eval_bitcoin_write64_non_crossing_raw m mw mf bf base bw edge cursor old x :
  frame_base_valid base -> 64 <= cursor <= Int64.max_unsigned ->
  64 <= write_word_shift cursor -> 0 <= edge -> write_word_address edge cursor + 8 <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong old) ->
  Mem.store Mint64 m bw (write_word_address edge cursor)
    (Vlong (put_slice 64 (write_word_shift cursor) old x)) = Some mw ->
  Mem.store Mint64 mw bf (base + 8) (Vlong (Int64.repr (cursor - 64))) = Some mf -> bf <> bw ->
  Clight2.eval_funcall bitcoin_ge m (Internal f_simplicity_write64)
    [Vptr bf (Ptrofs.repr base); Vlong x] E0 mf Vundef.
Proof.
  intros HB HC HN HE HA [HF HO] HW SW SF HD.
  pose proof (write_layout_index cursor ltac:(lia)) as [HQ [HK [Hsub [Hdiv [Hmod Hwidth]]]]].
  pose proof (write_layout_pointer edge ((cursor - 1) / 64) HQ HE
    ltac:(unfold write_word_address in HA; lia)) as Hptr.
  fold (write_word_address edge cursor) in Hptr.
  assert (Haddr : Ptrofs.unsigned (Ptrofs.repr (write_word_address edge cursor)) = write_word_address edge cursor)
    by (apply Ptrofs.unsigned_repr; unfold write_word_address in *; lia).
  assert (HWp : Mem.load Mint64 m bw (Ptrofs.unsigned (Ptrofs.repr (write_word_address edge cursor))) = Some (Vlong old))
    by (rewrite Haddr; exact HW).
  assert (SWp : Mem.store Mint64 m bw (Ptrofs.unsigned (Ptrofs.repr (write_word_address edge cursor)))
    (Vlong (put_slice 64 (write_word_shift cursor) old x)) = Some mw) by (rewrite Haddr; exact SW).
  assert (HOw : Mem.load Mint64 mw bf (base + 8) = Some (Vlong (Int64.repr cursor))).
  { erewrite Mem.load_store_other; [exact HO|exact SW|auto]. }
  assert (Hcross : Int64.ltu (Int64.repr (write_word_shift cursor)) (Int64.repr 64) = false).
  { unfold Int64.ltu. rewrite !cursor_unsigned by lia. rewrite zlt_false by lia; reflexivity. }
  pose proof (cursor_sub (write_word_shift cursor) 64 ltac:(lia) ltac:(lia)) as Hshift_sub.
  assert (Hshift : Int64.ltu (Int64.repr (write_word_shift cursor - 64)) Int64.iwordsize = true).
  { unfold Int64.ltu. rewrite cursor_unsigned by lia.
    change ((if zlt (write_word_shift cursor - 64) 64 then true else false) = true).
    rewrite zlt_true by lia; reflexivity. }
  assert (Hfinal : Int64.sub (Int64.repr cursor) (Int64.repr 64) = Int64.repr (cursor - 64)).
  { unfold Int64.sub. rewrite (Int64.unsigned_repr cursor) by lia.
    rewrite cursor_unsigned by lia; reflexivity. }
  unfold put_slice in SWp.
  eapply eval_funcall_internal with (e := empty_env) (le1 := le_write_wide W64 bf base x)
    (m1 := m) (m2 := mf) (out := Out_normal) (vres := Vundef).
  - apply entry_bitcoin_write64.
  - unfold f_simplicity_write64; cbn [fn_body]; bitcoin_writer_stmt.
  - reflexivity.
  - reflexivity.
Qed.
