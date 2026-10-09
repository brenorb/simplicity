(** The actual generated 16/32/64-bit writers, at arbitrary physical layouts.
    All three widths use unsigned long in the pinned Linux LP64 translation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_wide C.jet_word_slice.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_frame_arith C.jet_write8_layout.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
(* The slowest guarded sentence took 5.3 s in a clean baseline build (2026-09-27,
   see JET_BUILD.md); the bound is kept, with margin for slower CI machines. *)
Set Default Timeout 30.

Definition le_write_wide s bf base x : temp_env :=
  PTree.set _x (Vlong x) (PTree.set _frame (Vptr bf (Ptrofs.repr base))
    (create_undef_temps (wide_writer s).(fn_temps))).

Lemma entry_write_wide s m bf base x :
  function_entry2 ge0 (wide_writer s) [Vptr bf (Ptrofs.repr base); Vlong x]
    m empty_env (le_write_wide s bf base x) m.
Proof.
  destruct s; constructor; try constructor; try reflexivity.
  all: try (repeat constructor; simpl; intuition discriminate).
  all: intros id1 id2 H1 H2 Heq; simpl in H1, H2; subst id2;
    destruct H1 as [H1|[H1|H1]];
    repeat (destruct H2 as [H2|H2]);
    vm_compute in H1, H2; congruence.
Qed.

Lemma eval_write_wide_crossing_raw s m mh mo ml mf bf base bw edge cursor k oldhigh oldlow x :
  frame_base_valid base -> wide_bits s <= cursor <= Int64.max_unsigned ->
  1 <= k < wide_bits s -> write_word_shift cursor = k ->
  0 <= edge -> 8 <= write_word_address edge cursor ->
  write_word_address edge cursor + 8 <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong oldhigh) ->
  Mem.store Mint64 m bw (write_word_address edge cursor)
    (Vlong (slice_high (wide_bits s) k oldhigh x)) = Some mh ->
  Mem.load Mint64 mh bf (base + 8) = Some (Vlong (Int64.repr cursor)) ->
  Mem.store Mint64 mh bf (base + 8) (Vlong (Int64.repr (cursor - k))) = Some mo ->
  Mem.load Mint64 mo bw (write_word_address edge cursor - 8) = Some (Vlong oldlow) ->
  Mem.store Mint64 mo bw (write_word_address edge cursor - 8)
    (Vlong (slice_low (wide_bits s) k x)) = Some ml ->
  Mem.load Mint64 ml bf (base + 8) = Some (Vlong (Int64.repr (cursor - k))) ->
  Mem.store Mint64 ml bf (base + 8) (Vlong (Int64.repr (cursor - wide_bits s))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal (wide_writer s))
    [Vptr bf (Ptrofs.repr base); Vlong x] E0 mf Vundef.
Proof.
  intros HB HC HK HKdef HE HA0 HA [HF HO] HH SH HOh SO HL SL HOl SF.
  pose proof (wide_bits_bounds s) as HNbound.
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
      (Vlong (slice_high (wide_bits s) k oldhigh x)) = Some mh) by (rewrite Haddr; exact SH).
  assert (SLp : Mem.store Mint64 mo bw
      (Ptrofs.unsigned (Ptrofs.repr (write_word_address edge cursor - 8)))
      (Vlong (slice_low (wide_bits s) k x)) = Some ml) by (rewrite HaddrL; exact SL).
  assert (Hcross : Int64.ltu (Int64.repr k) (Int64.repr (wide_bits s)) = true).
  { unfold Int64.ltu. rewrite !cursor_unsigned by lia. rewrite zlt_true by lia; reflexivity. }
  pose proof (cursor_sub (wide_bits s) k ltac:(lia) ltac:(lia)) as Hremain.
  pose proof (cursor_sub 64 (wide_bits s - k) ltac:(lia) ltac:(lia)) as Hshift_sub.
  assert (Hshr : Int64.ltu (Int64.repr (wide_bits s - k)) Int64.iwordsize = true).
  { unfold Int64.ltu. rewrite cursor_unsigned by lia.
    change ((if zlt (wide_bits s - k) 64 then true else false) = true).
    rewrite zlt_true by lia; reflexivity. }
  assert (Hshift : Int64.ltu (Int64.repr (64 - (wide_bits s - k))) Int64.iwordsize = true).
  { unfold Int64.ltu. rewrite cursor_unsigned by lia.
    change ((if zlt (64 - (wide_bits s - k)) 64 then true else false) = true).
    rewrite zlt_true by lia; reflexivity. }
  assert (Hstop : Int64.ltu (Int64.repr 64) (Int64.repr (wide_bits s - k)) = false).
  { unfold Int64.ltu. rewrite !cursor_unsigned by lia. rewrite zlt_false by lia; reflexivity. }
  assert (Hfirst : Int64.sub (Int64.repr cursor) (Int64.repr k) = Int64.repr (cursor - k)).
  { unfold Int64.sub. rewrite (Int64.unsigned_repr cursor) by lia.
    rewrite cursor_unsigned by lia; reflexivity. }
  assert (Hfinal : Int64.sub (Int64.repr (cursor - k)) (Int64.repr (wide_bits s - k)) =
      Int64.repr (cursor - wide_bits s)).
  { unfold Int64.sub. rewrite (Int64.unsigned_repr (cursor - k)) by lia.
    rewrite cursor_unsigned by lia. f_equal; lia. }
  unfold slice_high in SHp. unfold slice_low in SLp.
  destruct s;
    cbv beta iota delta [wide_bits] in HNbound, HC, HK, Hcross, Hremain, Hshift_sub, Hshr,
      Hshift, Hstop, Hfinal, SHp, SLp, SF.
  all: match goal with
  | |- ClightBigstep.Clight2.eval_funcall _ _ (Internal (wide_writer ?sz)) _ _ _ _ =>
      eapply ClightBigstep.eval_funcall_internal
        with (e := empty_env) (le1 := le_write_wide sz bf base x) (m1 := m)
          (m2 := mf) (out := Out_normal) (vres := Vundef)
  end.
  all: try apply entry_write_wide; try reflexivity.
  all: unfold wide_writer, f_simplicity_write16, f_simplicity_write32, f_simplicity_write64;
    cbn [fn_body]; bytelayout_stmt.
Qed.

Lemma eval_write_wide_non_crossing_raw s m mw mf bf base bw edge cursor old x :
  frame_base_valid base -> wide_bits s <= cursor <= Int64.max_unsigned ->
  wide_bits s <= write_word_shift cursor ->
  0 <= edge -> write_word_address edge cursor + 8 <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong old) ->
  Mem.store Mint64 m bw (write_word_address edge cursor)
    (Vlong (put_slice (wide_bits s) (write_word_shift cursor) old x)) = Some mw ->
  Mem.store Mint64 mw bf (base + 8) (Vlong (Int64.repr (cursor - wide_bits s))) = Some mf ->
  (bf <> bw \/ write_word_address edge cursor + 8 <= base \/
    base + 16 <= write_word_address edge cursor) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal (wide_writer s))
    [Vptr bf (Ptrofs.repr base); Vlong x] E0 mf Vundef.
Proof.
  intros HB HC HN HE HA [HF HO] HW SW SF HD.
  pose proof (wide_bits_bounds s) as HNbound.
  pose proof (write_layout_index cursor ltac:(lia)) as [HQ [HK [Hsub [Hdiv [Hmod Hwidth]]]]].
  pose proof (write_layout_pointer edge ((cursor - 1) / 64) HQ HE
    ltac:(unfold write_word_address in HA; lia)) as Hptr.
  fold (write_word_address edge cursor) in Hptr.
  assert (Haddr : Ptrofs.unsigned (Ptrofs.repr (write_word_address edge cursor)) =
      write_word_address edge cursor).
  { apply Ptrofs.unsigned_repr. unfold write_word_address in *; lia. }
  assert (HWp : Mem.load Mint64 m bw
      (Ptrofs.unsigned (Ptrofs.repr (write_word_address edge cursor))) = Some (Vlong old))
    by (rewrite Haddr; exact HW).
  assert (SWp : Mem.store Mint64 m bw
      (Ptrofs.unsigned (Ptrofs.repr (write_word_address edge cursor)))
      (Vlong (put_slice (wide_bits s) (write_word_shift cursor) old x)) = Some mw)
    by (rewrite Haddr; exact SW).
  assert (HOw : Mem.load Mint64 mw bf (base + 8) = Some (Vlong (Int64.repr cursor))).
  { erewrite Mem.load_store_other; [exact HO|exact SW|].
    change (bf <> bw \/ base + 8 + 8 <= write_word_address edge cursor \/
      write_word_address edge cursor + 8 <= base + 8).
    destruct HD as [HD|[HD|HD]]; [left; exact HD|right; right; lia|right; left; lia]. }
  assert (Hcross : Int64.ltu (Int64.repr (write_word_shift cursor)) (Int64.repr (wide_bits s)) = false).
  { unfold Int64.ltu. rewrite !cursor_unsigned by lia. rewrite zlt_false by lia; reflexivity. }
  pose proof (cursor_sub (write_word_shift cursor) (wide_bits s) ltac:(lia) ltac:(lia)) as Hshift_sub.
  assert (Hshift : Int64.ltu (Int64.repr (write_word_shift cursor - wide_bits s)) Int64.iwordsize = true).
  { unfold Int64.ltu. rewrite cursor_unsigned by lia.
    change ((if zlt (write_word_shift cursor - wide_bits s) 64 then true else false) = true).
    rewrite zlt_true by lia; reflexivity. }
  assert (Hfinal : Int64.sub (Int64.repr cursor) (Int64.repr (wide_bits s)) = Int64.repr (cursor - wide_bits s)).
  { unfold Int64.sub. rewrite (Int64.unsigned_repr cursor) by lia.
    rewrite cursor_unsigned by lia; reflexivity. }
  unfold put_slice in SWp.
  (** Split before creating execution witnesses: each function has its own
      final temporary environment, including its width-dependent n value. *)
  destruct s;
    cbv beta iota delta [wide_bits] in HNbound, HC, HN, Hcross, Hshift_sub, Hshift, Hfinal, SWp, SF.
  all: match goal with
  | |- ClightBigstep.Clight2.eval_funcall _ _ (Internal (wide_writer ?sz)) _ _ _ _ =>
      eapply ClightBigstep.eval_funcall_internal
        with (e := empty_env) (le1 := le_write_wide sz bf base x) (m1 := m)
          (m2 := mf) (out := Out_normal) (vres := Vundef)
  end.
  all: try apply entry_write_wide; try reflexivity.
  all: unfold wide_writer, f_simplicity_write16, f_simplicity_write32, f_simplicity_write64;
    cbn [fn_body]; bytelayout_stmt.
Qed.
