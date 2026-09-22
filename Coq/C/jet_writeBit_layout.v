(** Generated bit writer at arbitrary frame addresses and backing-word indices. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_frame_access.
Require Import C.jet_word_bits C.jet_writeBit C.jet_writeBit_position.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Definition le_writeBit_layout (bf : block) base (bit : int) : temp_env :=
  PTree.set _bit (Vint bit) (PTree.set _frame (Vptr bf (Ptrofs.repr base))
    (create_undef_temps f_writeBit.(fn_temps))).

Lemma entry_writeBit_layout m bf base bit :
  function_entry2 ge0 f_writeBit [Vptr bf (Ptrofs.repr base); Vint bit]
    m empty_env (le_writeBit_layout bf base bit) m.
Proof.
  constructor.
  - constructor.
  - repeat constructor; simpl; intuition discriminate.
  - intros id1 id2 H1 H2 Heq. simpl in H1, H2. subst id2.
    repeat match goal with H : _ \/ _ |- _ => destruct H end.
    all: vm_compute in *; congruence.
  - constructor.
  - reflexivity.
Qed.

Definition write_bit_value cursor old (bit : bool) :=
  if bit then Int64.or old (Int64.shl Int64.one (Int64.repr ((cursor - 1) mod 64)))
  else clear_low (write_word_shift cursor) old.

Ltac bitlayout_stmt :=
  lazymatch goal with
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [bitlayout_stmt | bitlayout_stmt]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sloop _ _) _ _ _ _ =>
      apply exec_writeBit_debug_loop
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      apply exec_set; writelayout_expr
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      first [eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
        [writelayout_expr | reflexivity | bitlayout_stmt]
      | eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true);
        [writelayout_expr | reflexivity | bitlayout_stmt]]
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ (Evar _LSBclear _) _) _ _ _ _ =>
      writelayout_call f_LSBclear symbol_LSBclear funct_LSBclear
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ => writelayout_assign
  | |- ClightBigstep.exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      apply exec_Sreturn_some; writelayout_expr
  end.

Lemma eval_writeBit_layout_raw m mo mf bf base bw edge cursor old bit :
  frame_base_valid base -> 1 <= cursor <= Int64.max_unsigned ->
  0 <= edge -> write_word_address edge cursor + 8 <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong old) ->
  Mem.store Mint64 m bf (base + 8) (Vlong (Int64.repr (cursor - 1))) = Some mo ->
  Mem.store Mint64 mo bw (write_word_address edge cursor)
    (Vlong (write_bit_value cursor old bit)) = Some mf -> bf <> bw ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_writeBit)
    [Vptr bf (Ptrofs.repr base); Vint (if bit then Int.one else Int.zero)] E0 mf
    (Vint (if bit then Int.one else Int.zero)).
Proof.
  intros HB HC HE HA [HF HO] HW SO SW HD.
  pose proof (write_layout_index cursor HC) as [HQ [HK [Hsub [Hdiv [Hmod Hwidth]]]]].
  pose proof (write_layout_pointer edge ((cursor - 1) / 64) HQ HE
    ltac:(unfold write_word_address in HA; lia)) as Hptr.
  fold (write_word_address edge cursor) in Hptr.
  assert (Haddr : Ptrofs.unsigned (Ptrofs.repr (write_word_address edge cursor)) =
      write_word_address edge cursor).
  { apply Ptrofs.unsigned_repr. unfold write_word_address in *; lia. }
  assert (HFo : Mem.load Mptr mo bf base = Some (Vptr bw (Ptrofs.repr edge))).
  { erewrite Mem.load_store_other; [exact HF|exact SO|right; left; change (base + 8 <= base + 8); lia]. }
  pose proof (Mem.load_store_same _ _ _ _ _ _ SO) as HOo.
  assert (HWp : Mem.load Mint64 mo bw
      (Ptrofs.unsigned (Ptrofs.repr (write_word_address edge cursor))) = Some (Vlong old)).
  { rewrite Haddr. erewrite Mem.load_store_other; [exact HW|exact SO|auto]. }
  assert (SWp : Mem.store Mint64 mo bw
      (Ptrofs.unsigned (Ptrofs.repr (write_word_address edge cursor)))
      (Vlong (write_bit_value cursor old bit)) = Some mf) by (rewrite Haddr; exact SW).
  assert (Hshift : Int64.ltu (Int64.repr ((cursor - 1) mod 64)) Int64.iwordsize = true).
  { unfold Int64.ltu. rewrite Int64.unsigned_repr by (unfold write_word_shift in HK;
      change (0 <= (cursor - 1) mod 64 <= 18446744073709551615); lia).
    change ((if zlt ((cursor - 1) mod 64) 64 then true else false) = true).
    rewrite zlt_true by (unfold write_word_shift in HK; lia). reflexivity. }
  destruct bit; cbn [write_bit_value] in SWp;
    eapply ClightBigstep.eval_funcall_internal
      with (e := empty_env) (m1 := m) (m2 := mf).
  - apply entry_writeBit_layout.
  - unfold f_writeBit; cbn [fn_body]. timeout 10 bitlayout_stmt.
  - cbn; split; [discriminate|reflexivity].
  - reflexivity.
  - apply entry_writeBit_layout.
  - unfold f_writeBit; cbn [fn_body]. timeout 10 bitlayout_stmt.
  - cbn; split; [discriminate|reflexivity].
  - reflexivity.
Qed.
