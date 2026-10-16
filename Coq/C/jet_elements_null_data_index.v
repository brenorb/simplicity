(** Actual opcode-index check, including the empty/out-of-range branch. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets_elements C.jet_elements_linkage C.jet_exec C.jet_elements_prim.
Require Import C.jet_elements_field_eval C.jet_elements_index_eval C.jet_elements_bit_expr.
Require Import C.jet_elements_null_data_loads C.jet_elements_null_data_small C.jet_elements_null_data_payload.
Require Import C.jet_elements_null_data_nonpush C.jet_elements_null_data_opcode C.jet_elements_effects C.jet_elements_env_load.
Require Import C.jet_output_layout C.jet_output_layout_step C.jet_application_sep C.jet_uint32_array_init.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Local Notation OpcodeTy := (Ty.Sum (Ty.Prod (Word 1) (Word 8)) (Ty.Sum (Ty.Sum Ty.Unit Ty.Unit) (Word 2))).

Definition elements_null_data_count_path m be ebase bt txbase bout outbase i count : Prop :=
  0 <= ebase /\ ebase + 8 <= Ptrofs.max_unsigned /\
  0 <= txbase /\ txbase + 16 <= Ptrofs.max_unsigned /\
  0 <= outbase /\ outbase + 248 * Int64.unsigned i + 240 <= Ptrofs.max_unsigned /\
  Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) /\
  Mem.load Mptr m bt (txbase + 8) = Some (Vptr bout (Ptrofs.repr outbase)) /\
  Mem.load Mint64 m bout (outbase + 248 * Int64.unsigned i + 232) = Some (Vlong count).

Definition elements_null_data_count_reload : statement :=
  Ssequence
    (Sset _t'40 (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
      _tx (tptr (Tstruct _elementsTransaction noattr))))
    (Ssequence
      (Sset _t'41 (Efield (Ederef (Etempvar _t'40 (tptr (Tstruct _elementsTransaction noattr)))
        (Tstruct _elementsTransaction noattr)) _output (tptr (Tstruct _sigOutput noattr))))
      (Sset _t'42 (Efield (Efield (elements_indexed_deref _t'41 _i _sigOutput) _pnd
        (Tstruct _parsedNullData noattr)) _len tulong))).

Definition elements_null_data_index_test : expr :=
  Ebinop Olt (Etempvar _j tulong) (Etempvar _t'42 tulong) tint.

Definition elements_null_data_index_condition : statement :=
  elements_append_stmt elements_null_data_count_reload
    (elements_bit_expr_stmt (Some _t'6) elements_null_data_index_test).

Definition elements_null_data_count_temps bt txbase bout outbase count le :=
  PTree.set _t'42 (Vlong count) (PTree.set _t'41 (Vptr bout (Ptrofs.repr outbase))
    (PTree.set _t'40 (Vptr bt (Ptrofs.repr txbase)) le)).

Definition elements_null_data_index_temps bt txbase bout outbase j count le :=
  PTree.set _t'6 (Vint (if Int64.ltu j count then Int.one else Int.zero))
    (elements_null_data_count_temps bt txbase bout outbase count le).

Lemma eval_elements_null_data_index_test e le m j count :
  le!_j = Some (Vlong j) -> le!_t'42 = Some (Vlong count) ->
  eval_expr elements_ge e le m elements_null_data_index_test
    (Vint (if Int64.ltu j count then Int.one else Int.zero)).
Proof.
  intros HJ HC. unfold elements_null_data_index_test.
  eapply eval_Ebinop with (v1 := Vlong j) (v2 := Vlong count).
  - apply eval_Etempvar; exact HJ.
  - apply eval_Etempvar; exact HC.
  - change (Some (Val.of_bool (Int64.ltu j count)) = Some (Vint (if Int64.ltu j count then Int.one else Int.zero))).
    destruct (Int64.ltu j count); reflexivity.
Qed.

Theorem exec_elements_null_data_index_condition e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase i j count :
  e!_writeBit = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  elements_null_data_count_path m be ebase bt txbase bout outbase i count ->
  write_frame_at m bd dbase bw edge cur 1 ->
  exists mf, Clight2.exec_stmt elements_ge e le m elements_null_data_index_condition E0
    (elements_null_data_index_temps bt txbase bout outbase j count le) mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 1 [Some (Int64.ltu j count)].
Proof.
  intros HW HD Henv Hi Hj (He0 & HeM & Ht0 & HtM & Ho0 & HoM & L1 & L2 & L3) HF.
  set (le1 := PTree.set _t'40 (Vptr bt (Ptrofs.repr txbase)) le).
  set (le2 := PTree.set _t'41 (Vptr bout (Ptrofs.repr outbase)) le1).
  set (next := elements_null_data_count_temps bt txbase bout outbase count le).
  assert (HR : Clight2.exec_stmt elements_ge e le m elements_null_data_count_reload E0 next m Out_normal).
  { unfold elements_null_data_count_reload, next, elements_null_data_count_temps. fold le1 le2.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le1).
    - apply exec_set. eapply eval_elements_field_value with (sid := _txEnv) (delta := 0) (chunk := Mptr).
      + reflexivity.
      + exact elements_txEnv_tx.
      + reflexivity.
      + apply eval_elements_deref_struct; exact Henv.
      + rewrite elements_ptr_add_repr by lia. replace (ebase + 0) with ebase by lia.
        apply elements_loadv_repr; [lia|exact L1].
    - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le2).
      + apply exec_set. eapply eval_elements_field_value with (sid := _elementsTransaction) (delta := 8) (chunk := Mptr).
        * reflexivity.
        * exact elements_elementsTransaction_output.
        * reflexivity.
        * apply eval_elements_deref_struct. unfold le1; apply PTree.gss.
        * rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact L2].
      + apply exec_set.
        eapply eval_elements_indexed_nested_value with (sz := 248) (d1 := 224) (d2 := 8)
          (chunk := Mint64) (base := outbase) (r := i);
          [exact elements_sizeof_sigOutput|exact elements_sigOutput_pnd|exact elements_parsedNullData_len|
           reflexivity|unfold le2; apply PTree.gss| |exact Ho0|lia|lia|lia|lia|].
        * unfold le2, le1. rewrite !PTree.gso by discriminate. exact Hi.
        * replace (outbase + 248 * Int64.unsigned i + 224 + 8) with (outbase + 248 * Int64.unsigned i + 232) by lia.
          exact L3. }
  assert (HD' : next!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold next, elements_null_data_count_temps. rewrite !PTree.gso by discriminate. exact HD. }
  assert (HJ' : next!_j = Some (Vlong j)).
  { unfold next, elements_null_data_count_temps. rewrite !PTree.gso by discriminate. exact Hj. }
  assert (HC : next!_t'42 = Some (Vlong count)).
  { unfold next, elements_null_data_count_temps. apply PTree.gss. }
  destruct (exec_elements_bit_expr (Int64.ltu j count) (Some _t'6) elements_null_data_index_test e next m
    bd dbase bw edge cur eq_refl HW HD' (eval_elements_null_data_index_test e next m j count HJ' HC) HF)
    as (mf & CALL & EFF).
  exists mf. split; [|exact EFF]. unfold elements_null_data_index_condition, elements_null_data_index_temps.
  change E0 with (E0 ** E0). eapply exec_elements_append_stmt; [exact HR|exact CALL].
Qed.

Lemma int64_index_below_list_length {A : Type} (xs : list A) j :
  Z.of_nat (length xs) <= Int64.max_unsigned ->
  Int64.ltu j (Int64.repr (Z.of_nat (length xs))) =
    match nth_error xs (Z.to_nat (Int64.unsigned j)) with Some _ => true | None => false end.
Proof.
  intros Hlen. pose proof (Int64.unsigned_range j) as HJ.
  unfold Int64.ltu. rewrite Int64.unsigned_repr by lia.
  destruct (nth_error xs (Z.to_nat (Int64.unsigned j))) as [x|] eqn:HX.
  - assert (HK : (Z.to_nat (Int64.unsigned j) < length xs)%nat).
    { apply nth_error_Some. rewrite HX. discriminate. }
    destruct (zlt (Int64.unsigned j) (Z.of_nat (length xs))); [reflexivity|lia].
  - apply nth_error_None in HX.
    destruct (zlt (Int64.unsigned j) (Z.of_nat (length xs))); [lia|reflexivity].
Qed.

Definition elements_null_data_index_value (parsed : list (txNullDatumF (list byte))) j unused_hash :
    Ty.tySem (Ty.Sum Ty.Unit OpcodeTy) :=
  match nth_error parsed (Z.to_nat (Int64.unsigned j)) with
  | Some d => inr (elements_datum_value (mapNullDatum byteStringHash d) unused_hash)
  | None => inl tt
  end.

Definition elements_null_data_index_selected m bd dbase bw edge cur be ebase bt txbase bout outbase i j
    (parsed : list (txNullDatumF (list byte))) unused_hash : Prop :=
  forall d, nth_error parsed (Z.to_nat (Int64.unsigned j)) = Some d ->
  exists bop opbase,
    elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j
      (elements_datum_code (mapNullDatum byteStringHash d)) /\
    Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 260 b lo hi)
      (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j) /\
    (if elements_datum_push (mapNullDatum byteStringHash d) then
      uint32_array_at m bop (opbase + 36 * Int64.unsigned j)
        (hash256_reg (elements_datum_hash (mapNullDatum byteStringHash d) unused_hash)) /\
      out_sep bd dbase bw edge cur 260 bop (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32)
      else True).

Definition elements_null_data_missing_count : expr :=
  Ebinop Oadd (Ebinop Oadd (Econst_int (Int.repr 1) tint) (Econst_int (Int.repr 2) tint) tint)
    (Econst_int (Int.repr 256) tint) tint.

Lemma eval_elements_null_data_missing_count e le m :
  eval_expr elements_ge e le m elements_null_data_missing_count (Vint (Int.repr 259)).
Proof.
  unfold elements_null_data_missing_count.
  eapply eval_Ebinop with (v1 := Vint (Int.repr 3)) (v2 := Vint (Int.repr 256)).
  - eapply eval_Ebinop with (v1 := Vint (Int.repr 1)) (v2 := Vint (Int.repr 2));
      [apply eval_Econst_int|apply eval_Econst_int|reflexivity].
  - apply eval_Econst_int.
  - reflexivity.
Qed.

Definition elements_null_data_index_block : statement :=
  Ssequence elements_null_data_index_condition
    (Sifthenelse (Etempvar _t'6 tbool) elements_null_data_opcode_block
      (elements_skip_expr_stmt elements_null_data_missing_count)).

Theorem exec_elements_null_data_index_block parsed unused_hash e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase i j :
  Z.of_nat (length parsed) <= Int64.max_unsigned ->
  e!_writeBit = None -> e!_skipBits = None -> e!_writeHash = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  elements_null_data_count_path m be ebase bt txbase bout outbase i (Int64.repr (Z.of_nat (length parsed))) ->
  elements_null_data_index_selected m bd dbase bw edge cur be ebase bt txbase bout outbase i j parsed unused_hash ->
  write_frame_at m bd dbase bw edge cur 260 ->
  exists le' mf, Clight2.exec_stmt elements_ge e le m elements_null_data_index_block E0 le' mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 260
      (@encode (Ty.Sum Ty.Unit OpcodeTy) (elements_null_data_index_value parsed j unused_hash)).
Proof.
  intros Hlen HW HS HH HD Henv Hi Hj HP Hselected HF.
  pose proof HF as (_ & _ & _ & HCUR & _).
  set (count := Int64.repr (Z.of_nat (length parsed))).
  assert (HF1 : write_frame_at m bd dbase bw edge cur 1).
  { eapply write_frame_at_shorter with (count := 260); [lia|exact HF]. }
  destruct (exec_elements_null_data_index_condition e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase i j count HW HD Henv Hi Hj HP HF1) as (m1 & CC & EC).
  set (next := elements_null_data_index_temps bt txbase bout outbase j count le).
  assert (HF259 : write_frame_at m1 bd dbase bw edge (cur - 1) 259).
  { eapply write_frame_at_after_effect with (m := m) (cells := [Some (Int64.ltu j count)]);
      [reflexivity|lia|exact HF|exact EC]. }
  assert (Hother : forall k, In k [_dst; _env; _i; _j] -> next!k = le!k).
  { intros k HK. unfold next, elements_null_data_index_temps, elements_null_data_count_temps.
    assert (Hneq : k <> _t'6 /\ k <> _t'42 /\ k <> _t'41 /\ k <> _t'40).
    { repeat split; intros Hk; subst k; vm_compute in HK; intuition discriminate. }
    rewrite !PTree.gso by tauto. reflexivity. }
  assert (HD' : next!_dst = Some (Vptr bd (Ptrofs.repr dbase))) by (rewrite Hother by (simpl; tauto); exact HD).
  assert (Henv' : next!_env = Some (Vptr be (Ptrofs.repr ebase))) by (rewrite Hother by (simpl; tauto); exact Henv).
  assert (Hi' : next!_i = Some (Vlong i)) by (rewrite Hother by (simpl; tauto); exact Hi).
  assert (Hj' : next!_j = Some (Vlong j)) by (rewrite Hother by (simpl; tauto); exact Hj).
  assert (HC : next!_t'6 = Some (Vint (if Int64.ltu j count then Int.one else Int.zero))).
  { unfold next, elements_null_data_index_temps. apply PTree.gss. }
  pose proof (int64_index_below_list_length parsed j Hlen) as Htest. fold count in Htest.
  unfold elements_null_data_index_value.
  destruct (nth_error parsed (Z.to_nat (Int64.unsigned j))) as [d|] eqn:HDatum.
  - destruct (Hselected d HDatum) as (bop & opbase & HPath & HSEP & HHash).
    set (datum := mapNullDatum byteStringHash d) in *.
    assert (HSEP1 : Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 1 b lo hi)
      (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j)).
    { eapply Forall_impl; [|exact HSEP]. intros [[b lo] hi] H.
      eapply out_sep_sub with (cursor := cur) (count := 260); [lia|lia|lia|lia|exact H]. }
    assert (HP1 : elements_null_data_path_valid m1 be ebase bt txbase bout outbase bop opbase i j (elements_datum_code datum)).
    { eapply elements_null_data_path_valid_after with (cur := cur) (count := 1);
        [lia|lia|exact EC|exact HSEP1|exact HPath]. }
    assert (HSEP259 : Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge (cur - 1) 259 b lo hi)
      (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j)).
    { eapply Forall_impl; [|exact HSEP]. intros [[b lo] hi] H.
      eapply out_sep_sub with (cursor := cur) (count := 260); [lia|lia|lia|lia|exact H]. }
    assert (HHash1 : if elements_datum_push datum then
      uint32_array_at m1 bop (opbase + 36 * Int64.unsigned j) (hash256_reg (elements_datum_hash datum unused_hash)) /\
      out_sep bd dbase bw edge (cur - 1) 259 bop (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32)
      else True).
    { destruct (elements_datum_push datum); [|exact I]. destruct HHash as [HA HSH]. split.
      - intros k x HX.
        assert (HK : (k < 8)%nat).
        { rewrite <- (hash256_len (elements_datum_hash datum unused_hash)). apply nth_error_Some. rewrite HX. discriminate. }
        rewrite (write_effect_env_load m m1 bd dbase bw edge cur 1 [Some (Int64.ltu j count)] cur 260 bop
          (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32)
          Mint32 (opbase + 36 * Int64.unsigned j + 4 * Z.of_nat k))
          by (first [exact EC | exact HSH | change (size_chunk Mint32) with 4; lia | lia]).
        exact (HA k x HX).
      - eapply out_sep_sub with (cursor := cur) (count := 260); [lia|lia|lia|lia|exact HSH]. }
    destruct (exec_elements_null_data_datum datum unused_hash e next m1 bd dbase bw edge (cur - 1)
      be ebase bt txbase bout outbase bop opbase i j HW HS HH HD' Henv' Hi' Hj' HP1 HHash1 HSEP259 HF259)
      as (le' & mf & CR & ER).
    exists le', mf. split.
    + unfold elements_null_data_index_block.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact CC|].
      rewrite Htest in HC.
      eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true);
        [apply eval_Etempvar; exact HC|reflexivity|exact CR].
    + change (@encode (Ty.Sum Ty.Unit OpcodeTy) (inr (elements_datum_value datum unused_hash))) with
        ([Some true] ++ @encode OpcodeTy (elements_datum_value datum unused_hash)).
      change 260 with (1 + 259).
      rewrite Htest in EC.
      eapply write_effect_seq with (cells1 := [Some true]) (n1 := 1) (n2 := 259);
        [reflexivity|lia|exact HF|exact EC|exact ER].
  - destruct (exec_elements_skip_expr 259 elements_null_data_missing_count e next m1 bd dbase bw edge (cur - 1)
      ltac:(change (0 <= 259 <= 2147483647); lia) eq_refl HS HD'
      (eval_elements_null_data_missing_count e next m1) HF259) as (mf & CS & ES).
    exists next, mf. split.
    + unfold elements_null_data_index_block.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact CC|].
      rewrite Htest in HC.
      eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
        [apply eval_Etempvar; exact HC|reflexivity|exact CS].
    + change (@encode (Ty.Sum Ty.Unit OpcodeTy) (inl tt)) with ([Some false] ++ repeat None 259).
      change 260 with (1 + 259).
      rewrite Htest in EC.
      eapply write_effect_seq with (cells1 := [Some false]) (n1 := 1) (n2 := 259);
        [reflexivity|lia|exact HF|exact EC|exact ES].
Qed.

Lemma elements_null_data_index_block_source :
  elements_find_head_prefix _t'40 (fn_body f_simplicity_output_null_datum) = Some elements_null_data_index_block.
Proof. reflexivity. Qed.

Lemma elements_null_data_missing_selected m bd dbase bw edge cur be ebase bt txbase bout outbase i j parsed unused_hash :
  nth_error parsed (Z.to_nat (Int64.unsigned j)) = None ->
  elements_null_data_index_selected m bd dbase bw edge cur be ebase bt txbase bout outbase i j parsed unused_hash.
Proof.
  intros Hmissing d HD. rewrite Hmissing in HD. discriminate.
Qed.

Lemma elements_output_null_datum_parsed_sem environment (iw jw : Ty.tySem Word32) txo parsed j unused_hash :
  nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ iw)) = Some txo ->
  txNullData (txoScript txo) = Some parsed -> Int64.unsigned j = toZ jw ->
  Elements.sem Elements.OutputNullDatum (iw, jw) environment =
    Some (inr (elements_null_data_index_value parsed j unused_hash)).
Proof.
  intros HI HP HJ. unfold elements_null_data_index_value.
  destruct (nth_error parsed (Z.to_nat (Int64.unsigned j))) as [d|] eqn:HD.
  - eapply elements_output_null_datum_present_sem; [exact HI|exact HP|].
    rewrite <- HJ. exact HD.
  - cbn [Elements.sem fst snd]. rewrite HI, HP. rewrite <- HJ, HD. reflexivity.
Qed.
