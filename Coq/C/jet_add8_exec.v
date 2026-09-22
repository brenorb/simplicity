(** Composition at every non-crossing output cursor. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_one8 C.jet_read8 C.jet_read8_position C.jet_add8 C.jets.
Require Import C.jet_add8_update C.jet_increment8_exec.
Require Import C.jet_writeBit_position C.jet_write8_position.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Lemma add8_helper_statements_position m mr mr2 mo mc mw mf bl bd bs bi bw w old cursor read_cursor :
  0 <= read_cursor <= 48 ->
  9 <= cursor <= 64 ->
  Mem.load Mptr m bl 0 = Some (Vptr bi (Ptrofs.repr 8)) ->
  Mem.load Mint64 m bl 8 = Some (Vlong (Int64.repr read_cursor)) ->
  Mem.load Mint64 m bi 0 = Some (Vlong w) ->
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr cursor)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong old) ->
  bl <> bd -> bl <> bw -> bl <> bi -> bd <> bw ->
  Mem.store Mint64 m bl 8 (Vlong (Int64.repr (read_cursor + 8))) = Some mr ->
  Mem.store Mint64 mr bl 8 (Vlong (Int64.repr (read_cursor + 16))) = Some mr2 ->
  Mem.store Mint64 mr2 bd 8 (Vlong (Int64.repr (cursor - 1))) = Some mo ->
  Mem.store Mint64 mo bw 0 (Vlong (add8_carry_at cursor old (read8_at read_cursor w) (read8_at (read_cursor + 8) w))) = Some mc ->
  Mem.store Mint64 mc bw 0 (Vlong (add8_word_at cursor old (read8_at read_cursor w) (read8_at (read_cursor + 8) w))) = Some mw ->
  Mem.store Mint64 mw bd 8 (Vlong (Int64.repr (cursor - 9))) = Some mf ->
  let r := read8_at read_cursor w in
  let s := read8_at (read_cursor + 8) w in
  ClightBigstep.Clight2.exec_stmt ge0 (e_add8 bl)
    (le_add8 bd bs Ptrofs.zero) m (add8_read_stmt _t'1)
    E0 (le_add8_read bd bs Ptrofs.zero r) mr Out_normal /\
  ClightBigstep.Clight2.exec_stmt ge0 (e_add8 bl)
    (le_add8_x bd bs Ptrofs.zero r) mr (add8_read_stmt _t'2)
    E0 (PTree.set _t'2 (Vint s) (le_add8_x bd bs Ptrofs.zero r)) mr2 Out_normal /\
  ClightBigstep.Clight2.exec_stmt ge0 (e_add8 bl)
    (le_add8_ready bd bs Ptrofs.zero r s) mr2 add8_bit_stmt
    E0 (le_add8_ready bd bs Ptrofs.zero r s) mc Out_normal /\
  ClightBigstep.Clight2.exec_stmt ge0 (e_add8 bl)
    (le_add8_ready bd bs Ptrofs.zero r s) mc add8_write_stmt
    E0 (le_add8_ready bd bs Ptrofs.zero r s) mf Out_normal.
Proof.
  intros HRead HCurs HLE HLO HI HE HO HW HLd HLw HLi HDw SR SR2 SO SC SW SF r s.
  assert (HEr : Mem.load Mptr mr2 bd 0 = Some (Vptr bw Ptrofs.zero))
    by (eapply load_store64_other_block; [exact SR2 | auto |]; eapply load_store64_other_block; eauto).
  assert (HOr : Mem.load Mint64 mr2 bd 8 = Some (Vlong (Int64.repr cursor)))
    by (eapply load_store64_other_block; [exact SR2 | auto |]; eapply load_store64_other_block; eauto).
  assert (HWr : Mem.load Mint64 mr2 bw 0 = Some (Vlong old))
    by (eapply load_store64_other_block; [exact SR2 | auto |]; eapply load_store64_other_block; eauto).
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
  assert (HWc : Mem.load Mint64 mc bw 0 = Some (Vlong (add8_carry_at cursor old r s)))
    by (eapply load_store64_same; eauto).
  split.
  - eapply call_add8_read.
    + apply symbol_read8.
    + apply funct_read8.
    + eapply eval_read8_position; eauto; lia.
  - split.
    + eapply call_add8_read.
      * apply symbol_read8.
      * apply funct_read8.
      * eapply eval_read8_position.
        -- lia.
        -- eapply load_edge_store_offset; eauto.
        -- eapply load_store64_same; eauto.
        -- eapply load_store64_other_block; eauto.
        -- replace (read_cursor + 8 + 8) with (read_cursor + 16) by lia. exact SR2.
    + split.
      * eapply call_add8_writeBit with (bit := add8_carry_bit r s)
        (vret := Vint (add8_carry_bit r s)).
        -- reflexivity.
        -- apply eval_add8_carry.
        -- apply cast_add8_carry.
        -- apply symbol_writeBit.
        -- apply funct_writeBit.
        -- change (Mem.store Mint64 mo bw 0 (Vlong (add8_carry_at cursor old r s)) = Some mc) in SC.
        unfold add8_carry_bit, add8_carry_at in *.
        destruct (Int.ltu (Int.sub (Int.repr 255) (add8_u s)) (add8_u r)).
           ++ eapply eval_writeBit_true_position; eauto; lia.
           ++ eapply eval_writeBit_false_position; eauto; lia.
      * eapply call_add8_write with (x := add8_byte r s).
        -- reflexivity.
        -- apply eval_add8_sum.
        -- apply cast_add8_sum.
        -- apply symbol_write8.
        -- apply funct_write8.
        -- replace (cursor - 9) with (cursor - 1 - 8) in SF by lia.
        eapply eval_write8_position; eauto; lia.
Qed.
