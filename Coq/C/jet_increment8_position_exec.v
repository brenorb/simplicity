(** Composition at every non-crossing output cursor. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_one8 C.jet_read8 C.jet_increment8 C.jets.
Require Import C.jet_increment8_exec C.jet_increment8_position_update.
Require Import C.jet_writeBit_position C.jet_write8_position.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Lemma increment8_helper_statements_position m mr mo mc mw mf bl bd bs bi bw w old cursor :
  9 <= cursor <= 64 ->
  Mem.load Mptr m bl 0 = Some (Vptr bi (Ptrofs.repr 8)) ->
  Mem.load Mint64 m bl 8 = Some (Vlong (Int64.repr 56)) ->
  Mem.load Mint64 m bi 0 = Some (Vlong w) ->
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr cursor)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong old) ->
  bl <> bd -> bl <> bw -> bd <> bw ->
  Mem.store Mint64 m bl 8 (Vlong (Int64.repr 64)) = Some mr ->
  Mem.store Mint64 mr bd 8 (Vlong (Int64.repr (cursor - 1))) = Some mo ->
  Mem.store Mint64 mo bw 0 (Vlong (increment8_carry_at cursor old (read8_result w))) = Some mc ->
  Mem.store Mint64 mc bw 0 (Vlong (increment8_word_at cursor old (read8_result w))) = Some mw ->
  Mem.store Mint64 mw bd 8 (Vlong (Int64.repr (cursor - 9))) = Some mf ->
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
  intros HCurs HLE HLO HI HE HO HW HLd HLw HDw SR SO SC SW SF r.
  assert (HEr : Mem.load Mptr mr bd 0 = Some (Vptr bw Ptrofs.zero))
    by (eapply load_store64_other_block; eauto).
  assert (HOr : Mem.load Mint64 mr bd 8 = Some (Vlong (Int64.repr cursor)))
    by (eapply load_store64_other_block; eauto).
  assert (HWr : Mem.load Mint64 mr bw 0 = Some (Vlong old))
    by (eapply load_store64_other_block; eauto).
  assert (HEo : Mem.load Mptr mo bd 0 = Some (Vptr bw Ptrofs.zero))
    by (eapply load_edge_store_offset; eauto).
  assert (HOo : Mem.load Mint64 mo bd 8 = Some (Vlong (Int64.repr (cursor - 1))))
    by (eapply load_store64_same; eauto).
  assert (HWo : Mem.load Mint64 mo bw 0 = Some (Vlong old))
    by (eapply load_store64_other_block; eauto).
  assert (HEc : Mem.load Mptr mc bd 0 = Some (Vptr bw Ptrofs.zero))
    by (eapply load_store64_other_block; eauto).
  assert (HOc : Mem.load Mint64 mc bd 8 = Some (Vlong (Int64.repr (cursor - 1))))
    by (eapply load_store64_other_block; eauto).
  assert (HWc : Mem.load Mint64 mc bw 0 = Some (Vlong (increment8_carry_at cursor old r)))
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
      * change (Mem.store Mint64 mo bw 0 (Vlong (increment8_carry_at cursor old r)) = Some mc) in SC.
        unfold increment8_carry_bit, increment8_carry_at in *.
        destruct (Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r)).
        -- eapply eval_writeBit_true_position; eauto; lia.
        -- eapply eval_writeBit_false_position; eauto; lia.
    + eapply call_increment8_write with (x := increment8_byte r).
      * reflexivity.
      * apply eval_increment8_sum.
      * apply cast_increment8_sum.
      * apply symbol_write8.
      * apply funct_write8.
      * replace (cursor - 9) with (cursor - 1 - 8) in SF by lia.
        eapply eval_write8_position; eauto; lia.
Qed.
