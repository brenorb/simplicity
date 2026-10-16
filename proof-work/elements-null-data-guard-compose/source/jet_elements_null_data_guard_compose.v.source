(** The outer tag, conditional second read and complete payload.
    Full initial footprints protect data read after the first tag. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_prim C.jet_elements_bit_expr.
Require Import C.jet_elements_null_data_output_guard C.jet_elements_null_data_read_index.
Require Import C.jet_elements_null_data_loads C.jet_elements_null_data_small C.jet_elements_null_data_payload.
Require Import C.jet_elements_null_data_opcode C.jet_elements_null_data_index C.jet_elements_effects.
Require Import C.jet_elements_null_data_nonpush C.jet_output_layout_step.
Require Import C.jet_elements_env_load C.jet_frame_layout C.jet_input_layout C.jet_output_layout.
Require Import C.jet_write_layout C.jet_uint32_array_init C.jet_encoding C.jet_application_sep.
Require Import C.jet_read_after_write C.jet_word_repr.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Local Notation OpcodeTy := (Ty.Sum (Ty.Prod (Word 1) (Word 8)) (Ty.Sum (Ty.Sum Ty.Unit Ty.Unit) (Word 2))).

Definition elements_null_data_selected_footprint m bl bd dbase bw edge cur count
    be ebase bt txbase bout outbase i j (parsed : list (txNullDatumF (list byte))) unused_hash : Prop :=
  forall d, nth_error parsed (Z.to_nat (Int64.unsigned j)) = Some d ->
  exists bop opbase,
    bl <> bop /\
    elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j
      (elements_datum_code (mapNullDatum byteStringHash d)) /\
    Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur count b lo hi)
      (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j) /\
    (if elements_datum_push (mapNullDatum byteStringHash d) then
      uint32_array_at m bop (opbase + 36 * Int64.unsigned j)
        (hash256_reg (elements_datum_hash (mapNullDatum byteStringHash d) unused_hash)) /\
      out_sep bd dbase bw edge cur count bop (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32)
      else True).

Lemma elements_null_data_selected_after_tag m m1 bl bd dbase bw edge cur bit
    be ebase bt txbase bout outbase i j parsed unused_hash :
  261 <= cur -> write_effect m m1 bd dbase bw edge cur 1 [Some bit] ->
  elements_null_data_selected_footprint m bl bd dbase bw edge cur 261
    be ebase bt txbase bout outbase i j parsed unused_hash ->
  elements_null_data_selected_private m1 bl bd dbase bw edge (cur - 1)
    be ebase bt txbase bout outbase i j parsed unused_hash.
Proof.
  intros Hcur HE Hsel d HD.
  destruct (Hsel d HD) as (bop & opbase & Hbl & HP & HS & HH).
  exists bop, opbase. split; [exact Hbl|]. split.
  - eapply elements_null_data_path_valid_after with (cur := cur) (count := 1);
      [lia|lia|exact HE| |exact HP].
    eapply Forall_impl; [|exact HS]. intros [[b lo] hi] H.
    eapply out_sep_sub with (cursor := cur) (count := 261); [lia|lia|lia|lia|exact H].
  - split.
    + eapply Forall_impl; [|exact HS]. intros [[b lo] hi] H.
      eapply out_sep_sub with (cursor := cur) (count := 261); [lia|lia|lia|lia|exact H].
    + destruct (elements_datum_push (mapNullDatum byteStringHash d)); [|exact I].
      destruct HH as [HA Hsep]. split.
      * intros k x HX.
        assert (HK : (k < 8)%nat).
        { rewrite <- (hash256_len (elements_datum_hash (mapNullDatum byteStringHash d) unused_hash)).
          apply nth_error_Some. rewrite HX. discriminate. }
        rewrite (write_effect_env_load m m1 bd dbase bw edge cur 1 [Some bit] cur 261 bop
          (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32)
          Mint32 (opbase + 36 * Int64.unsigned j + 4 * Z.of_nat k))
          by (first [exact HE | exact Hsep | change (size_chunk Mint32) with 4; lia | lia]).
        exact (HA k x HX).
      * eapply out_sep_sub with (cursor := cur) (count := 261); [lia|lia|lia|lia|exact Hsep].
Qed.



Definition elements_null_data_count_footprint be ebase bt txbase bout outbase i : list (block * Z * Z) :=
  [(be, ebase, ebase + 8); (bt, txbase + 8, txbase + 16);
   (bout, outbase + 248 * Int64.unsigned i + 232, outbase + 248 * Int64.unsigned i + 240)].

Lemma elements_null_data_count_after_tag m m1 bd dbase bw edge cur bit
    be ebase bt txbase bout outbase i count :
  261 <= cur -> write_effect m m1 bd dbase bw edge cur 1 [Some bit] ->
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 261 b lo hi)
    (elements_null_data_count_footprint be ebase bt txbase bout outbase i) ->
  elements_null_data_count_path m be ebase bt txbase bout outbase i count ->
  elements_null_data_count_path m1 be ebase bt txbase bout outbase i count.
Proof.
  intros HC HE HS (He0 & HeM & Ht0 & HtM & Ho0 & HoM & L1 & L2 & L3).
  unfold elements_null_data_count_footprint in HS.
  inversion HS as [|? ? S1 HS1]; subst. inversion HS1 as [|? ? S2 HS2]; subst.
  inversion HS2 as [|? ? S3 HS3]; subst. cbn beta iota in S1, S2, S3.
  unfold elements_null_data_count_path. do 6 (split; [assumption|]).
  split.
  - rewrite (write_effect_env_load m m1 bd dbase bw edge cur 1 [Some bit] cur 261
      be ebase (ebase + 8) Mptr ebase)
      by (first [exact HE | exact S1 | change (size_chunk Mptr) with 8; lia | lia]). exact L1.
  - split.
    + rewrite (write_effect_env_load m m1 bd dbase bw edge cur 1 [Some bit] cur 261
        bt (txbase + 8) (txbase + 16) Mptr (txbase + 8))
        by (first [exact HE | exact S2 | change (size_chunk Mptr) with 8; lia | lia]). exact L2.
    + rewrite (write_effect_env_load m m1 bd dbase bw edge cur 1 [Some bit] cur 261
        bout (outbase + 248 * Int64.unsigned i + 232) (outbase + 248 * Int64.unsigned i + 240)
        Mint64 (outbase + 248 * Int64.unsigned i + 232))
        by (first [exact HE | exact S3 | change (size_chunk Mint64) with 8; lia | lia]). exact L3.
Qed.

Definition elements_null_data_absent_count : expr :=
  Ebinop Oadd (Ebinop Oadd (Ebinop Oadd (Econst_int (Int.repr 1) tint)
    (Econst_int (Int.repr 1) tint) tint) (Econst_int (Int.repr 2) tint) tint)
    (Econst_int (Int.repr 256) tint) tint.

Lemma eval_elements_null_data_absent_count e le m :
  eval_expr elements_ge e le m elements_null_data_absent_count (Vint (Int.repr 260)).
Proof.
  unfold elements_null_data_absent_count.
  eapply eval_Ebinop with (v1 := Vint (Int.repr 4)) (v2 := Vint (Int.repr 256)).
  - eapply eval_Ebinop with (v1 := Vint (Int.repr 2)) (v2 := Vint (Int.repr 2)).
    + eapply eval_Ebinop with (v1 := Vint (Int.repr 1)) (v2 := Vint (Int.repr 1));
        [apply eval_Econst_int|apply eval_Econst_int|reflexivity].
    + apply eval_Econst_int.
    + reflexivity.
  - apply eval_Econst_int.
  - reflexivity.
Qed.

Definition elements_null_data_guard_block : statement :=
  Ssequence elements_null_data_output_guard
    (Sifthenelse (Etempvar _t'8 tbool) elements_null_data_read_index_block
      (elements_skip_expr_stmt elements_null_data_absent_count)).

Lemma elements_null_data_guard_block_source :
  match fn_body f_simplicity_output_null_datum with
  | Ssequence _ (Ssequence _ (Ssequence block _)) => block
  | _ => Sskip
  end = elements_null_data_guard_block.
Proof. reflexivity. Qed.

Definition elements_null_data_guard_value (parsed : list (txNullDatumF (list byte))) unused_hash
    (go : bool) (jw : Ty.tySem Word32) : Ty.tySem (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit OpcodeTy)) :=
  if go then inr (elements_null_data_index_value parsed (Int64.repr (toZ jw)) unused_hash) else inl tt.

Lemma word32_int64_unsigned (jw : Ty.tySem Word32) :
  Int64.unsigned (Int64.repr (toZ jw)) = toZ jw.
Proof.
  apply Int64.unsigned_repr. pose proof (word_toZ_range 5 jw) as HR.
  change (0 <= toZ jw < 4294967296) in HR.
  change (0 <= toZ jw <= 18446744073709551615). lia.
Qed.

Theorem exec_elements_null_data_guard_absent parsed unused_hash (jw : Ty.tySem Word32)
    e le m bd dbase bw edge cur be ebase bt txbase bout outbase i count flag :
  e!_writeBit = None -> e!_skipBits = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) ->
  elements_null_data_output_rep m be ebase bt txbase bout outbase i count flag ->
  andb (Int64.ltu i count) flag = false ->
  write_frame_at m bd dbase bw edge cur 261 ->
  exists le' mf, Clight2.exec_stmt elements_ge e le m elements_null_data_guard_block E0 le' mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 261
      (@encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit OpcodeTy)) (elements_null_data_guard_value parsed unused_hash false jw)).
Proof.
  intros HW HS HD Henv Hi HP Hfalse HF.
  assert (HF1 : write_frame_at m bd dbase bw edge cur 1) by
    (eapply write_frame_at_shorter with (count := 261); [lia|exact HF]).
  destruct (exec_elements_null_data_output_guard e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase i count flag HW HD Henv Hi HP HF1) as (m1 & CG & EG).
  set (next := elements_null_data_output_guard_temps bt txbase bout outbase i count flag le).
  assert (HD' : next!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold next. rewrite elements_null_data_output_guard_other; [exact HD|]. vm_compute; intuition discriminate. }
  assert (HC : next!_t'8 = Some (Vint Int.zero)).
  { unfold next. rewrite elements_null_data_output_guard_value, Hfalse. reflexivity. }
  rewrite Hfalse in EG.
  assert (HF260 : write_frame_at m1 bd dbase bw edge (cur - 1) 260).
  { eapply write_frame_at_after_effect with (m := m) (cells := [Some false]);
      [reflexivity|lia|exact HF|exact EG]. }
  destruct (exec_elements_skip_expr 260 elements_null_data_absent_count e next m1 bd dbase bw edge (cur - 1)
    ltac:(change (0 <= 260 <= 2147483647); lia) eq_refl HS HD'
    (eval_elements_null_data_absent_count e next m1) HF260) as (mf & CS & ES).
  exists next, mf. split.
  - unfold elements_null_data_guard_block.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact CG|].
    eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
      [apply eval_Etempvar; exact HC|reflexivity|exact CS].
  - change 261 with (1 + 260).
    change (@encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit OpcodeTy)) (elements_null_data_guard_value parsed unused_hash false jw))
      with ([Some false] ++ repeat None 260).
    eapply write_effect_seq with (cells1 := [Some false]) (n1 := 1) (n2 := 260);
      [reflexivity|lia|exact HF|exact EG|exact ES].
Qed.


Theorem exec_elements_null_data_guard_present parsed unused_hash (jw : Ty.tySem Word32)
    e le m bl bd dbase bw edge cur bi inedge rc be ebase bt txbase bout outbase i count flag :
  e!_simplicity_read32 = None -> e!_src = Some (bl, Tstruct _frameItem noattr) ->
  e!_writeBit = None -> e!_skipBits = None -> e!_writeHash = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) ->
  elements_null_data_output_rep m be ebase bt txbase bout outbase i count flag ->
  andb (Int64.ltu i count) flag = true ->
  0 <= rc <= Int64.max_unsigned - 32 ->
  frame_fields_at m bl 0 bi inedge rc -> frame_input_word_at m bi inedge rc jw ->
  Mem.valid_access m Mint64 bl 8 Writable ->
  bl <> bi -> bl <> bd -> bl <> bw -> bl <> be -> bl <> bt -> bl <> bout ->
  (forall k, 0 <= k < 32 -> out_sep bd dbase bw edge cur 261 bi
    (inedge - 8 * (1 + (rc + k) / 64)) (inedge - 8 * (1 + (rc + k) / 64) + 8)) ->
  Z.of_nat (length parsed) <= Int64.max_unsigned ->
  elements_null_data_count_path m be ebase bt txbase bout outbase i (Int64.repr (Z.of_nat (length parsed))) ->
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 261 b lo hi)
    (elements_null_data_count_footprint be ebase bt txbase bout outbase i) ->
  (forall r, Int64.unsigned r = toZ jw ->
    elements_null_data_selected_footprint m bl bd dbase bw edge cur 261
      be ebase bt txbase bout outbase i r parsed unused_hash) ->
  write_frame_at m bd dbase bw edge cur 261 ->
  exists le' mf, Clight2.exec_stmt elements_ge e le m elements_null_data_guard_block E0 le' mf Out_normal /\
    write_effect_private bl m mf bd dbase bw edge cur 261
      (@encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit OpcodeTy)) (elements_null_data_guard_value parsed unused_hash true jw)).
Proof.
  intros HRd HSrc HW HS HH HD Henv Hi HP Htrue Hrc HFields HInput HAccess
    Hli Hld Hlw Hle Hlt Hlo HInputSep Hlen HCount HCountSep HSelected HF.
  pose proof HF as (_ & _ & _ & Hcur & _).
  assert (HF1 : write_frame_at m bd dbase bw edge cur 1) by
    (eapply write_frame_at_shorter with (count := 261); [lia|exact HF]).
  destruct (exec_elements_null_data_output_guard e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase i count flag HW HD Henv Hi HP HF1) as (m1 & CG & EG).
  rewrite Htrue in EG.
  set (next := elements_null_data_output_guard_temps bt txbase bout outbase i count flag le).
  assert (Hother : forall k, In k [_dst; _env; _i] -> next!k = le!k).
  { intros k HK. unfold next. apply elements_null_data_output_guard_other.
    destruct HK as [<-|[<-|[<-|[]]]]; vm_compute; intuition discriminate. }
  assert (HD' : next!_dst = Some (Vptr bd (Ptrofs.repr dbase))) by (rewrite Hother by (simpl; tauto); exact HD).
  assert (Henv' : next!_env = Some (Vptr be (Ptrofs.repr ebase))) by (rewrite Hother by (simpl; tauto); exact Henv).
  assert (Hi' : next!_i = Some (Vlong i)) by (rewrite Hother by (simpl; tauto); exact Hi).
  assert (HC : next!_t'8 = Some (Vint Int.one)).
  { unfold next. rewrite elements_null_data_output_guard_value, Htrue. reflexivity. }
  assert (HF260 : write_frame_at m1 bd dbase bw edge (cur - 1) 260).
  { eapply write_frame_at_after_effect with (m := m) (cells := [Some true]);
      [reflexivity|lia|exact HF|exact EG]. }
  assert (HFields1 : frame_fields_at m1 bl 0 bi inedge rc).
  { exact (write_effect_keeps_private_read_frame m m1 bd dbase bw edge cur 1 [Some true]
      bl 0 bi inedge rc Hld Hlw EG HFields). }
  assert (HAccess1 : Mem.valid_access m1 Mint64 bl 8 Writable).
  { exact (write_effect_keeps_valid_access m m1 bd dbase bw edge cur 1 [Some true]
      Mint64 bl 8 Writable EG HAccess). }
  assert (HInput1 : frame_input_word_at m1 bi inedge rc jw).
  { eapply write_effect_input_bits_preserved with (count := 1) (cur := cur);
      [lia|lia|exact EG| |exact HInput].
    intros k HK. rewrite frame_input_word_bits_length in HK. cbn in HK.
    eapply out_sep_sub with (cursor := cur) (count := 261); [lia|lia|lia|lia|].
    apply HInputSep; exact HK. }
  assert (HCount1 : elements_null_data_count_path m1 be ebase bt txbase bout outbase i
    (Int64.repr (Z.of_nat (length parsed)))).
  { eapply elements_null_data_count_after_tag with (cur := cur); [lia|exact EG|exact HCountSep|exact HCount]. }
  assert (HSelected1 : forall r, Int64.unsigned r = toZ jw ->
    elements_null_data_selected_private m1 bl bd dbase bw edge (cur - 1)
      be ebase bt txbase bout outbase i r parsed unused_hash).
  { intros r HR. eapply elements_null_data_selected_after_tag; [lia|exact EG|apply HSelected; exact HR]. }
  destruct (exec_elements_null_data_read_index_block parsed unused_hash e next m1 bl bd dbase bw edge (cur - 1)
    bi inedge rc jw be ebase bt txbase bout outbase i HRd HSrc HW HS HH HD' Henv' Hi' Hrc
    HFields1 HInput1 HAccess1 Hli Hld Hlw Hle Hlt Hlo Hlen HCount1 HSelected1 HF260)
    as (le' & mf & r & HR & CR & ER & mr & HM & HPerm & HValid & E2).
  assert (Hr : r = Int64.repr (toZ jw)).
  { rewrite <- (Int64.repr_unsigned r) at 1. rewrite HR. reflexivity. }
  subst r. exists le', mf. split.
  - unfold elements_null_data_guard_block.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact CG|].
    eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true);
      [apply eval_Etempvar; exact HC|reflexivity|exact CR].
  - change 261 with (1 + 260).
    change (@encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit OpcodeTy)) (elements_null_data_guard_value parsed unused_hash true jw))
      with ([Some true] ++ @encode (Ty.Sum Ty.Unit OpcodeTy)
        (elements_null_data_index_value parsed (Int64.repr (toZ jw)) unused_hash)).
    eapply write_effect_private_interleaved with (m1 := m1) (mr := mr);
      [exact Hlw|lia|exact HF|exact EG|exact HM|exact HPerm|exact HValid|exact E2].
Qed.


Definition elements_null_data_guard_ready m bl bd dbase bw edge cur bi inedge rc
    be ebase bt txbase bout outbase i (jw : Ty.tySem Word32) parsed unused_hash : Prop :=
  0 <= rc <= Int64.max_unsigned - 32 /\
  frame_fields_at m bl 0 bi inedge rc /\ frame_input_word_at m bi inedge rc jw /\
  Mem.valid_access m Mint64 bl 8 Writable /\
  bl <> bi /\ bl <> bd /\ bl <> bw /\ bl <> be /\ bl <> bt /\ bl <> bout /\
  (forall k, 0 <= k < 32 -> out_sep bd dbase bw edge cur 261 bi
    (inedge - 8 * (1 + (rc + k) / 64)) (inedge - 8 * (1 + (rc + k) / 64) + 8)) /\
  Z.of_nat (length parsed) <= Int64.max_unsigned /\
  elements_null_data_count_path m be ebase bt txbase bout outbase i (Int64.repr (Z.of_nat (length parsed))) /\
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 261 b lo hi)
    (elements_null_data_count_footprint be ebase bt txbase bout outbase i) /\
  elements_null_data_selected_footprint m bl bd dbase bw edge cur 261
    be ebase bt txbase bout outbase i (Int64.repr (toZ jw)) parsed unused_hash.

Theorem exec_elements_null_data_guard_block parsed unused_hash (jw : Ty.tySem Word32)
    e le m bl bd dbase bw edge cur bi inedge rc be ebase bt txbase bout outbase i count flag :
  e!_simplicity_read32 = None -> e!_src = Some (bl, Tstruct _frameItem noattr) ->
  e!_writeBit = None -> e!_skipBits = None -> e!_writeHash = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) ->
  elements_null_data_output_rep m be ebase bt txbase bout outbase i count flag ->
  (andb (Int64.ltu i count) flag = true ->
    elements_null_data_guard_ready m bl bd dbase bw edge cur bi inedge rc
      be ebase bt txbase bout outbase i jw parsed unused_hash) ->
  write_frame_at m bd dbase bw edge cur 261 ->
  exists le' mf, Clight2.exec_stmt elements_ge e le m elements_null_data_guard_block E0 le' mf Out_normal /\
    write_effect_private bl m mf bd dbase bw edge cur 261
      (@encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit OpcodeTy))
        (elements_null_data_guard_value parsed unused_hash (andb (Int64.ltu i count) flag) jw)).
Proof.
  intros HRd HSrc HW HS HH HD Henv Hi HP HReady HF.
  destruct (andb (Int64.ltu i count) flag) eqn:HG.
  - specialize (HReady eq_refl) as
      (Hrc & HFields & HInput & HAccess & Hli & Hld & Hlw & Hle & Hlt & Hlo & HInputSep & Hlen & HCount & HCountSep & HSelected).
    eapply exec_elements_null_data_guard_present;
      [exact HRd|exact HSrc|exact HW|exact HS|exact HH|exact HD|exact Henv|exact Hi|
       exact HP|exact HG|exact Hrc|exact HFields|exact HInput|exact HAccess|
       exact Hli|exact Hld|exact Hlw|exact Hle|exact Hlt|exact Hlo|
       exact HInputSep|exact Hlen|exact HCount|exact HCountSep| |exact HF].
    intros r HR. replace r with (Int64.repr (toZ jw)); [exact HSelected|].
    rewrite <- HR. apply Int64.repr_unsigned.
  - destruct (exec_elements_null_data_guard_absent parsed unused_hash jw e le m bd dbase bw edge cur
      be ebase bt txbase bout outbase i count flag HW HS HD Henv Hi HP HG HF) as (le' & mf & HC & HE).
    exists le', mf. split; [exact HC|].
    destruct HE as (HO & HPfx & HFields & HLoads & HPerm & HValid).
    unfold write_effect_private. do 3 (split; [assumption|]).
    split; [intros chunk b ofs Hb Hbd Hbw; apply HLoads; assumption|].
    split; assumption.
Qed.

Lemma elements_output_null_datum_guard_sem environment (iw jw : Ty.tySem Word32) parsed unused_hash (go : bool) :
  (match nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ iw)) with
   | Some txo => txNullData (txoScript txo)
   | None => None
   end) = (if go then Some parsed else None) ->
  Elements.sem Elements.OutputNullDatum (iw, jw) environment =
    Some (elements_null_data_guard_value parsed unused_hash go jw).
Proof.
  intros HP. destruct go.
  - destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ iw))) as [txo|] eqn:HO;
      [|discriminate].
    unfold elements_null_data_guard_value.
    eapply elements_output_null_datum_parsed_sem; [exact HO|exact HP|apply word32_int64_unsigned].
  - unfold elements_null_data_guard_value. cbn [Elements.sem fst snd].
    destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ iw))) as [txo|] eqn:HO;
      [rewrite HP; reflexivity|reflexivity].
Qed.
