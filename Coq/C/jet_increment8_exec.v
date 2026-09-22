(** Execution of the generated increment jet on a concrete, byte-aligned frame.
    All helper calls below execute their generated Clight bodies. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_one8 C.jet_read8 C.jet_write8.
Require Import C.jet_writeBit C.jet_increment8 C.jets.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Lemma symbol_read8 :
  Genv.find_symbol (Clight.genv_genv ge0) _simplicity_read8 = Some block_read8.
Proof. vm_compute; reflexivity. Qed.

Lemma funct_read8 :
  Genv.find_funct (Clight.genv_genv ge0) (Vptr block_read8 Ptrofs.zero) =
    Some (Internal f_simplicity_read8).
Proof. reflexivity. Qed.

Lemma symbol_writeBit :
  Genv.find_symbol (Clight.genv_genv ge0) _writeBit = Some block_writeBit.
Proof. vm_compute; reflexivity. Qed.

Lemma funct_writeBit :
  Genv.find_funct (Clight.genv_genv ge0) (Vptr block_writeBit Ptrofs.zero) =
    Some (Internal f_writeBit).
Proof. reflexivity. Qed.

Definition increment8_carry_word (r : int) : int64 :=
  if Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r)
  then Int64.repr 256 else Int64.zero.

Definition increment8_written_word (r : int) : int64 :=
  Int64.or (increment8_carry_word r)
    (Int64.and (Int64.repr (Int.unsigned (increment8_byte r))) (Int64.repr 255)).

Lemma load_store64_other_block m m' b ofs w chunk b' ofs' v :
  Mem.store Mint64 m b ofs (Vlong w) = Some m' ->
  b' <> b -> Mem.load chunk m b' ofs' = Some v ->
  Mem.load chunk m' b' ofs' = Some v.
Proof.
  intros HS Hneq HL. rewrite <- HL.
  eapply Mem.load_store_other; [exact HS | left; exact Hneq].
Qed.

Lemma load_edge_store_offset m m' bf w v :
  Mem.store Mint64 m bf 8 (Vlong w) = Some m' ->
  Mem.load Mptr m bf 0 = Some v -> Mem.load Mptr m' bf 0 = Some v.
Proof.
  intros HS HL. rewrite <- HL.
  eapply Mem.load_store_other; [exact HS | right; left; change (0 + 8 <= 8); lia].
Qed.

Lemma load_store64_same m m' b ofs w :
  Mem.store Mint64 m b ofs (Vlong w) = Some m' ->
  Mem.load Mint64 m' b ofs = Some (Vlong w).
Proof. intros HS. exact (Mem.load_store_same _ _ _ _ _ _ HS). Qed.

Lemma eval_write8_increment_value m m1 m2 bd bw r :
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr 8)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong (increment8_carry_word r)) ->
  Mem.store Mint64 m bw 0 (Vlong (increment8_written_word r)) = Some m1 ->
  Mem.store Mint64 m1 bd 8 (Vlong Int64.zero) = Some m2 ->
  bd <> bw ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
    [Vptr bd Ptrofs.zero; Vint (increment8_byte r)] E0 m2 Vundef.
Proof.
  intros HE HO HW SW SO Hneq.
  eapply eval_write8_x with (w := increment8_carry_word r)
    (c := increment8_carry_word r)
    (k := Int64.and (Int64.repr (Int.unsigned (increment8_byte r)))
      (Int64.repr 255)) (m1 := m1).
  - exact HE.
  - exact HO.
  - exact HW.
  - exact SW.
  - eapply load_store64_other_block; eauto.
  - exact SO.
  - change (increment8_written_word r =
      Int64.or (increment8_carry_word r)
        (Int64.shl (Int64.and (Int64.repr (Int.unsigned (increment8_byte r)))
          (Int64.repr 255)) Int64.zero)).
    rewrite Int64.shl_zero. reflexivity.
  - apply symbol_LSBclear.
  - apply funct_LSBclear.
  - apply symbol_LSBkeep.
  - apply funct_LSBkeep.
  - pose proof (eval_LSBclear8_value m (increment8_carry_word r)) as HC.
    unfold increment8_carry_word in *.
    destruct (Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r));
      exact HC.
  - apply eval_LSBkeep8_value.
Qed.

Lemma increment8_helper_statements m mr mo mc mw mf bl bd bs bi bw w :
  Mem.load Mptr m bl 0 = Some (Vptr bi (Ptrofs.repr 8)) ->
  Mem.load Mint64 m bl 8 = Some (Vlong (Int64.repr 56)) ->
  Mem.load Mint64 m bi 0 = Some (Vlong w) ->
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr 9)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong Int64.zero) ->
  bl <> bd -> bl <> bw -> bd <> bw ->
  Mem.store Mint64 m bl 8 (Vlong (Int64.repr 64)) = Some mr ->
  Mem.store Mint64 mr bd 8 (Vlong (Int64.repr 8)) = Some mo ->
  Mem.store Mint64 mo bw 0 (Vlong (increment8_carry_word (read8_result w))) = Some mc ->
  Mem.store Mint64 mc bw 0 (Vlong (increment8_written_word (read8_result w))) = Some mw ->
  Mem.store Mint64 mw bd 8 (Vlong Int64.zero) = Some mf ->
  let r := read8_result w in
  ClightBigstep.Clight2.exec_stmt ge0 (e_increment8 bl)
    (le_increment8 bd bs Ptrofs.zero) m increment8_read_stmt
    E0 (le_increment8_read bd bs Ptrofs.zero r) mr Out_normal /\
  ClightBigstep.Clight2.exec_stmt ge0 (e_increment8 bl)
    (le_increment8_x bd bs Ptrofs.zero r) mr increment8_bit_stmt
    E0 (le_increment8_x bd bs Ptrofs.zero r) mc Out_normal /\
  ClightBigstep.Clight2.exec_stmt ge0 (e_increment8 bl)
    (le_increment8_x bd bs Ptrofs.zero r) mc increment8_write_stmt
    E0 (le_increment8_x bd bs Ptrofs.zero r) mf Out_normal.
Proof.
  intros HLE HLO HI HE HO HW HLd HLw HDw SR SO SC SW SF r.
  assert (HEr : Mem.load Mptr mr bd 0 = Some (Vptr bw Ptrofs.zero))
    by (eapply load_store64_other_block; eauto).
  assert (HOr : Mem.load Mint64 mr bd 8 = Some (Vlong (Int64.repr 9)))
    by (eapply load_store64_other_block; eauto).
  assert (HWr : Mem.load Mint64 mr bw 0 = Some (Vlong Int64.zero))
    by (eapply load_store64_other_block; eauto).
  assert (HEo : Mem.load Mptr mo bd 0 = Some (Vptr bw Ptrofs.zero))
    by (eapply load_edge_store_offset; eauto).
  assert (HOo : Mem.load Mint64 mo bd 8 = Some (Vlong (Int64.repr 8)))
    by (eapply load_store64_same; eauto).
  assert (HWo : Mem.load Mint64 mo bw 0 = Some (Vlong Int64.zero))
    by (eapply load_store64_other_block; eauto).
  assert (HEc : Mem.load Mptr mc bd 0 = Some (Vptr bw Ptrofs.zero))
    by (eapply load_store64_other_block; eauto).
  assert (HOc : Mem.load Mint64 mc bd 8 = Some (Vlong (Int64.repr 8)))
    by (eapply load_store64_other_block; eauto).
  assert (HWc : Mem.load Mint64 mc bw 0 = Some (Vlong (increment8_carry_word r)))
    by (eapply load_store64_same; eauto).
  split.
  - eapply call_increment8_read.
    + apply symbol_read8.
    + apply funct_read8.
    + eapply eval_read8; eauto using symbol_LSBkeep, funct_LSBkeep.
  - split.
    + eapply call_increment8_writeBit with (bit := increment8_carry_bit r)
        (vret := Vint (increment8_carry_bit r)).
      * reflexivity.
      * apply eval_increment8_carry.
      * apply cast_increment8_carry.
      * apply symbol_writeBit.
      * apply funct_writeBit.
      * change (Mem.store Mint64 mo bw 0 (Vlong (increment8_carry_word r)) = Some mc) in SC.
        unfold increment8_carry_bit, increment8_carry_word in *.
        destruct (Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r)).
        -- eapply eval_writeBit_one_call; eauto.
        -- eapply eval_writeBit_zero_call; eauto.
    + eapply call_increment8_write with (x := increment8_byte r).
      * reflexivity.
      * apply eval_increment8_sum.
      * apply cast_increment8_sum.
      * apply symbol_write8.
      * apply funct_write8.
      * eapply eval_write8_increment_value; eauto.
Qed.
