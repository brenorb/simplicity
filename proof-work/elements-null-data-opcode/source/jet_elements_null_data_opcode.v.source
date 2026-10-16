(** Entire actual 259-bit opcode result, including the push/non-push tag. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_bit_expr.
Require Import C.jet_elements_null_data_loads C.jet_elements_null_data_small C.jet_elements_null_data_payload.
Require Import C.jet_elements_null_data_nonpush C.jet_elements_effects C.jet_elements_env_load.
Require Import C.jet_output_layout C.jet_output_layout_step C.jet_application_sep C.jet_uint32_array_init.
Require Import C.jet_elements_prim.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Local Notation OpcodeTy := (Ty.Sum (Ty.Prod (Word 1) (Word 8)) (Ty.Sum (Ty.Sum Ty.Unit Ty.Unit) (Word 2))).

Definition elements_opcode_code_value (push : bool) (n : nat) (bit small : bool) : int :=
  if push then Int.repr (Z.of_nat n) else elements_nonpush_code n bit small.

Definition elements_opcode_value (push : bool) (n : nat) (bit small : bool) (h : hash256) : Ty.tySem OpcodeTy :=
  if push then inl (@fromZ (WordToZ 1) (Z.of_nat n), from_hash256 h)
    else inr (elements_nonpush_value n bit small).

Lemma elements_opcode_value_cells push n bit small h :
  @encode OpcodeTy (elements_opcode_value push n bit small h) =
    Some (negb push) :: (if push then
      @encode (Ty.Prod (Word 1) (Word 8)) (@fromZ (WordToZ 1) (Z.of_nat n), from_hash256 h)
      else repeat None 253 ++ @encode (Ty.Sum (Ty.Sum Ty.Unit Ty.Unit) (Word 2)) (elements_nonpush_value n bit small)).
Proof. destruct push; reflexivity. Qed.

Lemma elements_opcode_is_nonpush (push : bool) n bit small :
  (n < if push then 4 else 16)%nat ->
  Int.cmp Clt (Int.repr 3) (elements_opcode_code_value push n bit small) = negb push.
Proof.
  intros Hn. destruct push.
  - unfold elements_opcode_code_value, Int.cmp, Int.lt.
    rewrite (Int.signed_repr (Z.of_nat n)) by
      (change (-2147483648 <= Z.of_nat n <= 2147483647); lia).
    change (Int.signed (Int.repr 3)) with 3.
    destruct (zlt 3 (Z.of_nat n)); [lia|reflexivity].
  - unfold elements_opcode_code_value. destruct small; [|destruct bit; reflexivity].
    unfold elements_nonpush_code, Int.cmp, Int.lt.
    rewrite (Int.signed_repr (Z.of_nat n + 6)) by
      (change (-2147483648 <= Z.of_nat n + 6 <= 2147483647); lia).
    change (Int.signed (Int.repr 3)) with 3.
    destruct (zlt 3 (Z.of_nat n + 6)); [reflexivity|lia].
Qed.

Definition elements_opcode_test : expr :=
  Ebinop Olt (Econst_int (Int.repr 3) tint) (Etempvar _t'39 tint) tint.

Lemma eval_elements_opcode_test (push : bool) n bit small e le m :
  (n < if push then 4 else 16)%nat ->
  le!_t'39 = Some (Vint (elements_opcode_code_value push n bit small)) ->
  eval_expr elements_ge e le m elements_opcode_test (Vint (if negb push then Int.one else Int.zero)).
Proof.
  intros Hn HC. unfold elements_opcode_test.
  eapply eval_Ebinop with (v1 := Vint (Int.repr 3)) (v2 := Vint (elements_opcode_code_value push n bit small)).
  - apply eval_Econst_int.
  - apply eval_Etempvar; exact HC.
  - change (Some (Val.of_bool (Int.cmp Clt (Int.repr 3) (elements_opcode_code_value push n bit small))) =
      Some (Vint (if negb push then Int.one else Int.zero))).
    rewrite elements_opcode_is_nonpush by exact Hn. destruct push; reflexivity.
Qed.

Definition elements_opcode_condition : statement :=
  elements_append_stmt (elements_null_data_reload _t'36 _t'37 _t'38 _t'39)
    (elements_bit_expr_stmt (Some _t'5) elements_opcode_test).

Definition elements_opcode_condition_temps (push : bool) n bit small bt txbase bout outbase bop opbase le :=
  PTree.set _t'5 (Vint (if negb push then Int.one else Int.zero))
    (elements_null_data_reload_temps _t'36 _t'37 _t'38 _t'39
      bt txbase bout outbase bop opbase (elements_opcode_code_value push n bit small) le).

Theorem exec_elements_opcode_condition (push : bool) n bit small e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j :
  (n < if push then 4 else 16)%nat -> e!_writeBit = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j (elements_opcode_code_value push n bit small) ->
  write_frame_at m bd dbase bw edge cur 1 ->
  exists mf, Clight2.exec_stmt elements_ge e le m elements_opcode_condition E0
    (elements_opcode_condition_temps push n bit small bt txbase bout outbase bop opbase le) mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 1 [Some (negb push)].
Proof.
  intros Hn HW HD Henv Hi Hj
    (He0 & HeM & Ht0 & HtM & Ho0 & HoM & Hp0 & HpM & L1 & L2 & L3 & L4) HF.
  set (next := elements_null_data_reload_temps _t'36 _t'37 _t'38 _t'39
    bt txbase bout outbase bop opbase (elements_opcode_code_value push n bit small) le).
  assert (HR : Clight2.exec_stmt elements_ge e le m
    (elements_null_data_reload _t'36 _t'37 _t'38 _t'39) E0 next m Out_normal).
  { unfold next. eapply exec_elements_null_data_reload; eauto.
    intros t Ht. simpl in Ht. repeat destruct Ht as [Ht|Ht]; subst;
      try contradiction; vm_compute; intuition discriminate. }
  assert (HD' : next!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold next. rewrite elements_null_data_reload_temps_other; [exact HD|]. vm_compute; intuition discriminate. }
  assert (HC : next!_t'39 = Some (Vint (elements_opcode_code_value push n bit small))).
  { unfold next, elements_null_data_reload_temps. apply PTree.gss. }
  destruct (exec_elements_bit_expr (negb push) (Some _t'5) elements_opcode_test e next m bd dbase bw edge cur
    eq_refl HW HD' (eval_elements_opcode_test push n bit small e next m Hn HC) HF) as (mf & CALL & EFF).
  exists mf. split; [|exact EFF]. unfold elements_opcode_condition, elements_opcode_condition_temps.
  change E0 with (E0 ** E0). eapply exec_elements_append_stmt; [exact HR|exact CALL].
Qed.

Definition elements_null_data_opcode_block : statement :=
  Ssequence elements_opcode_condition
    (Sifthenelse (Etempvar _t'5 tbool) elements_null_data_nonpush_arm elements_null_data_push_arm).

Theorem exec_elements_null_data_opcode_block (push : bool) n bit small h e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j :
  (n < if push then 4 else 16)%nat -> e!_writeBit = None -> e!_skipBits = None -> e!_writeHash = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j (elements_opcode_code_value push n bit small) ->
  (if push then uint32_array_at m bop (opbase + 36 * Int64.unsigned j) (hash256_reg h) /\
    out_sep bd dbase bw edge cur 259 bop (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32)
    else True) ->
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 259 b lo hi)
    (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j) ->
  write_frame_at m bd dbase bw edge cur 259 ->
  exists le' mf, Clight2.exec_stmt elements_ge e le m elements_null_data_opcode_block E0 le' mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 259 (@encode OpcodeTy (elements_opcode_value push n bit small h)).
Proof.
  intros Hn HW HS HH HD Henv Hi Hj HP HHash HSEP HF.
  pose proof HF as (_ & _ & _ & HCUR & _).
  assert (HF1 : write_frame_at m bd dbase bw edge cur 1).
  { eapply write_frame_at_shorter with (count := 259); [lia|exact HF]. }
  destruct (exec_elements_opcode_condition push n bit small e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j Hn HW HD Henv Hi Hj HP HF1) as (m1 & CC & EC).
  set (next := elements_opcode_condition_temps push n bit small bt txbase bout outbase bop opbase le).
  assert (HF258 : write_frame_at m1 bd dbase bw edge (cur - 1) 258).
  { eapply write_frame_at_after_effect with (m := m) (cells := [Some (negb push)]);
      [reflexivity|lia|exact HF|exact EC]. }
  assert (HSEP1 : Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 1 b lo hi)
    (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j)).
  { eapply Forall_impl; [|exact HSEP]. intros [[b lo] hi] H.
    eapply out_sep_sub with (cursor := cur) (count := 259); [lia|lia|lia|lia|exact H]. }
  assert (HP1 : elements_null_data_path_valid m1 be ebase bt txbase bout outbase bop opbase i j
    (elements_opcode_code_value push n bit small)).
  { eapply elements_null_data_path_valid_after with (cur := cur) (count := 1);
      [lia|lia|exact EC|exact HSEP1|exact HP]. }
  assert (HSEP258 : Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge (cur - 1) 258 b lo hi)
    (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j)).
  { eapply Forall_impl; [|exact HSEP]. intros [[b lo] hi] H.
    eapply out_sep_sub with (cursor := cur) (count := 259); [lia|lia|lia|lia|exact H]. }
  assert (Hother : forall k, In k [_dst; _env; _i; _j] -> next!k = le!k).
  { intros k HK. unfold next, elements_opcode_condition_temps.
    assert (Hneq : k <> _t'5).
    { intros Hk. subst k. vm_compute in HK. intuition discriminate. }
    rewrite PTree.gso by exact Hneq.
    rewrite elements_null_data_reload_temps_other; [reflexivity|].
    intros HB. simpl in HB. repeat destruct HB as [HB|HB]; try contradiction;
      subst k; vm_compute in HK; intuition discriminate. }
  assert (HD' : next!_dst = Some (Vptr bd (Ptrofs.repr dbase))) by (rewrite Hother by (simpl; tauto); exact HD).
  assert (Henv' : next!_env = Some (Vptr be (Ptrofs.repr ebase))) by (rewrite Hother by (simpl; tauto); exact Henv).
  assert (Hi' : next!_i = Some (Vlong i)) by (rewrite Hother by (simpl; tauto); exact Hi).
  assert (Hj' : next!_j = Some (Vlong j)) by (rewrite Hother by (simpl; tauto); exact Hj).
  assert (HC : next!_t'5 = Some (Vint (if negb push then Int.one else Int.zero))).
  { unfold next, elements_opcode_condition_temps. apply PTree.gss. }
  destruct push.
  - destruct HHash as [HA HSH].
    assert (HA1 : uint32_array_at m1 bop (opbase + 36 * Int64.unsigned j) (hash256_reg h)).
    { intros k x HX.
      assert (HK : (k < 8)%nat).
      { rewrite <- (hash256_len h). apply nth_error_Some. rewrite HX. discriminate. }
      rewrite (write_effect_env_load m m1 bd dbase bw edge cur 1 [Some false] cur 259 bop
        (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32)
        Mint32 (opbase + 36 * Int64.unsigned j + 4 * Z.of_nat k))
        by (first [exact EC | exact HSH | change (size_chunk Mint32) with 4; lia | lia]).
      exact (HA k x HX). }
    assert (HSH258 : out_sep bd dbase bw edge (cur - 1) 258 bop
      (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32)).
    { eapply out_sep_sub with (cursor := cur) (count := 259); [lia|lia|lia|lia|exact HSH]. }
    destruct (exec_elements_null_data_push_pair n e next m1 bd dbase bw edge (cur - 1)
      be ebase bt txbase bout outbase bop opbase i j h Hn HW HH HD' Henv' Hi' Hj' HP1 HA1 HSEP258 HSH258 HF258)
      as (mf & CR & ER).
    eexists; exists mf. split.
    + unfold elements_null_data_opcode_block.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact CC|].
      eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
        [apply eval_Etempvar; exact HC|reflexivity|exact CR].
    + rewrite elements_opcode_value_cells. change 259 with (1 + 258).
      change (Some false :: @encode (Ty.Prod (Word 1) (Word 8))
        (@fromZ (WordToZ 1) (Z.of_nat n), from_hash256 h)) with
        ([Some false] ++ @encode (Ty.Prod (Word 1) (Word 8))
          (@fromZ (WordToZ 1) (Z.of_nat n), from_hash256 h)).
      eapply write_effect_seq with (cells1 := [Some false]) (n1 := 1) (n2 := 258);
        [reflexivity|lia|exact HF|exact EC|exact ER].
  - destruct (exec_elements_null_data_nonpush_arm n bit small e next m1 bd dbase bw edge (cur - 1)
      be ebase bt txbase bout outbase bop opbase i j Hn HW HS HD' Henv' Hi' Hj' HP1 HSEP258 HF258)
      as (le' & mf & CR & ER).
    exists le', mf. split.
    + unfold elements_null_data_opcode_block.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact CC|].
      eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true);
        [apply eval_Etempvar; exact HC|reflexivity|exact CR].
    + rewrite elements_opcode_value_cells. change 259 with (1 + 258).
      change (Some true :: repeat None 253 ++ @encode (Ty.Sum (Ty.Sum Ty.Unit Ty.Unit) (Word 2))
        (elements_nonpush_value n bit small)) with
        ([Some true] ++ (repeat None 253 ++ @encode (Ty.Sum (Ty.Sum Ty.Unit Ty.Unit) (Word 2))
          (elements_nonpush_value n bit small))).
      eapply write_effect_seq with (cells1 := [Some true]) (n1 := 1) (n2 := 258);
        [reflexivity|lia|exact HF|exact EC|exact ER].
Qed.

Lemma elements_null_data_opcode_block_source :
  elements_find_head_prefix _t'36 (fn_body f_simplicity_output_null_datum) = Some elements_null_data_opcode_block.
Proof. reflexivity. Qed.

(** Constructor adapters for the existing primitive's parsed null datum.
    [unused_hash] is deliberately unconstrained: non-push opcodes never read it. *)
Definition elements_datum_push (d : txNullDatumF hash256) : bool :=
  match d with Immediate _ | PushData _ | PushData2 _ | PushData4 _ => true | _ => false end.

Definition elements_datum_number (d : txNullDatumF hash256) : nat :=
  match d with
  | Immediate _ => 0 | PushData _ => 1 | PushData2 _ => 2 | PushData4 _ => 3
  | OP1 => 0 | OP2 => 1 | OP3 => 2 | OP4 => 3 | OP5 => 4 | OP6 => 5 | OP7 => 6 | OP8 => 7
  | OP9 => 8 | OP10 => 9 | OP11 => 10 | OP12 => 11 | OP13 => 12 | OP14 => 13 | OP15 => 14 | OP16 => 15
  | _ => 0
  end.

Definition elements_datum_bit (d : txNullDatumF hash256) : bool :=
  match d with OPReserved => true | _ => false end.

Definition elements_datum_small (d : txNullDatumF hash256) : bool :=
  match d with
  | Immediate _ | PushData _ | PushData2 _ | PushData4 _ | OP1Negate | OPReserved => false
  | _ => true
  end.

Definition elements_datum_hash (d : txNullDatumF hash256) (unused_hash : hash256) : hash256 :=
  match d with Immediate h | PushData h | PushData2 h | PushData4 h => h | _ => unused_hash end.

Definition elements_datum_code (d : txNullDatumF hash256) : int :=
  elements_opcode_code_value (elements_datum_push d) (elements_datum_number d)
    (elements_datum_bit d) (elements_datum_small d).

Definition elements_datum_value (d : txNullDatumF hash256) (unused_hash : hash256) : Ty.tySem OpcodeTy :=
  elements_opcode_value (elements_datum_push d) (elements_datum_number d)
    (elements_datum_bit d) (elements_datum_small d) (elements_datum_hash d unused_hash).

Lemma elements_datum_number_bound d :
  (elements_datum_number d < if elements_datum_push d then 4 else 16)%nat.
Proof. destruct d; cbn [elements_datum_number elements_datum_push]; lia. Qed.

(** This adapter is connected to the actual primitive semantics, not a separate
    claim that a chosen replacement specification is mathematically correct. *)
Lemma elements_output_null_datum_present_sem environment (i j : Ty.tySem Word32) txo parsed d unused_hash :
  nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ i)) = Some txo ->
  txNullData (txoScript txo) = Some parsed ->
  nth_error parsed (Z.to_nat (toZ j)) = Some d ->
  Elements.sem Elements.OutputNullDatum (i, j) environment =
    Some (inr (inr (elements_datum_value (mapNullDatum byteStringHash d) unused_hash))).
Proof.
  intros HI HP HJ. cbn [Elements.sem fst snd]. rewrite HI, HP, HJ.
  destruct d; reflexivity.
Qed.

Corollary exec_elements_null_data_datum d unused_hash e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j :
  e!_writeBit = None -> e!_skipBits = None -> e!_writeHash = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j (elements_datum_code d) ->
  (if elements_datum_push d then
    uint32_array_at m bop (opbase + 36 * Int64.unsigned j) (hash256_reg (elements_datum_hash d unused_hash)) /\
    out_sep bd dbase bw edge cur 259 bop (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32)
    else True) ->
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 259 b lo hi)
    (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j) ->
  write_frame_at m bd dbase bw edge cur 259 ->
  exists le' mf, Clight2.exec_stmt elements_ge e le m elements_null_data_opcode_block E0 le' mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 259 (@encode OpcodeTy (elements_datum_value d unused_hash)).
Proof.
  intros HW HS HH HD Henv Hi Hj HP HA HSEP HF.
  exact (exec_elements_null_data_opcode_block (elements_datum_push d) (elements_datum_number d)
    (elements_datum_bit d) (elements_datum_small d) (elements_datum_hash d unused_hash)
    e le m bd dbase bw edge cur be ebase bt txbase bout outbase bop opbase i j
    (elements_datum_number_bound d) HW HS HH HD Henv Hi Hj HP HA HSEP HF).
Qed.
