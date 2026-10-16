(** Actual entry, source copy, both readers, output and local free.
    Unread-input/output separation is explicit, not hidden in the environment. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Maps Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_prim C.jet_elements_wrapper.
Require Import C.jet_elements_version_exec C.jet_elements_null_data_rest C.jet_elements_null_data_guard_compose.
Require Import C.jet_elements_null_data_output_guard C.jet_elements_null_data_loads C.jet_elements_null_data_small.
Require Import C.jet_elements_null_data_payload C.jet_elements_null_data_opcode C.jet_elements_null_data_index.
Require Import C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_write_layout C.jet_uint32_array_init C.jet_encoding C.jet_application_sep.
Require Import C.jet_wide C.jet_complement_wide_layout C.jet_bitmachine_rep.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Local Notation OpcodeTy := (Ty.Sum (Ty.Prod (Word 1) (Word 8)) (Ty.Sum (Ty.Sum Ty.Unit Ty.Unit) (Word 2))).

(** No reference to a not-yet-allocated private block. *)
Definition elements_null_data_selected_initial m bd dbase bw edge cur count
    be ebase bt txbase bout outbase i j (parsed : list (txNullDatumF (list byte))) unused_hash : Prop :=
  forall d, nth_error parsed (Z.to_nat (Int64.unsigned j)) = Some d ->
  exists bop opbase,
    elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j
      (elements_datum_code (mapNullDatum byteStringHash d)) /\
    Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur count b lo hi)
      (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j) /\
    (if elements_datum_push (mapNullDatum byteStringHash d) then
      uint32_array_at m bop (opbase + 36 * Int64.unsigned j)
        (hash256_reg (elements_datum_hash (mapNullDatum byteStringHash d) unused_hash)) /\
      out_sep bd dbase bw edge cur count bop (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32)
      else True).

Lemma elements_null_data_selected_initial_alloc m ma mc bl bd dbase bw edge cur count
    be ebase bt txbase bout outbase i j parsed unused_hash :
  Mem.alloc m 0 16 = (ma, bl) ->
  (forall chunk b ofs v, Mem.load chunk m b ofs = Some v -> Mem.load chunk mc b ofs = Some v) ->
  elements_null_data_selected_initial m bd dbase bw edge cur count
    be ebase bt txbase bout outbase i j parsed unused_hash ->
  elements_null_data_selected_footprint mc bl bd dbase bw edge cur count
    be ebase bt txbase bout outbase i j parsed unused_hash.
Proof.
  intros HA HM Hsel d HD.
  destruct (Hsel d HD) as (bop & opbase & HP & HS & HH).
  pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HCode).
  exists bop, opbase. split; [eapply fresh_frame_not_loaded; eassumption|]. split.
  - destruct HP as (He0 & HeM & Ht0 & HtM & Ho0 & HoM & Hp0 & HpM & L1 & L2 & L3 & L4).
    unfold elements_null_data_path_valid. do 8 (split; [assumption|]).
    unfold elements_null_data_path_loads. repeat split; apply HM; assumption.
  - split; [exact HS|]. destruct (elements_datum_push (mapNullDatum byteStringHash d)); [|exact I].
    destruct HH as [HX Hsep]. split; [|exact Hsep]. intros k x Hnth. apply HM. exact (HX k x Hnth).
Qed.


Lemma elements_null_data_output_rep_mono m mc be ebase bt txbase bout outbase i count flag :
  (forall chunk b ofs v, Mem.load chunk m b ofs = Some v -> Mem.load chunk mc b ofs = Some v) ->
  elements_null_data_output_rep m be ebase bt txbase bout outbase i count flag ->
  elements_null_data_output_rep mc be ebase bt txbase bout outbase i count flag.
Proof.
  intros HM (He0 & HeM & Ht0 & HtM & L1 & L2 & Hmore).
  unfold elements_null_data_output_rep. do 4 (split; [assumption|]).
  split; [apply HM; exact L1|]. split; [apply HM; exact L2|].
  intros HC. specialize (Hmore HC) as (Ho0 & HoM & L3 & L4).
  do 2 (split; [assumption|]). split; apply HM; assumption.
Qed.

Lemma elements_null_data_count_path_mono m mc be ebase bt txbase bout outbase i count :
  (forall chunk b ofs v, Mem.load chunk m b ofs = Some v -> Mem.load chunk mc b ofs = Some v) ->
  elements_null_data_count_path m be ebase bt txbase bout outbase i count ->
  elements_null_data_count_path mc be ebase bt txbase bout outbase i count.
Proof.
  intros HM (He0 & HeM & Ht0 & HtM & Ho0 & HoM & L1 & L2 & L3).
  unfold elements_null_data_count_path. do 6 (split; [assumption|]).
  split; [apply HM; exact L1|]. split; apply HM; assumption.
Qed.

Definition elements_null_data_layout_payload m bd dbase bw edge cur bi inedge rc
    be ebase bt txbase bout outbase i (jw : Ty.tySem Word32) parsed unused_hash : Prop :=
  frame_input_word_at m bi inedge (rc + 32) jw /\
  (forall k, 0 <= k < 32 -> out_sep bd dbase bw edge cur 261 bi
    (inedge - 8 * (1 + (rc + 32 + k) / 64)) (inedge - 8 * (1 + (rc + 32 + k) / 64) + 8)) /\
  Z.of_nat (length parsed) <= Int64.max_unsigned /\
  elements_null_data_count_path m be ebase bt txbase bout outbase i (Int64.repr (Z.of_nat (length parsed))) /\
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 261 b lo hi)
    (elements_null_data_count_footprint be ebase bt txbase bout outbase i) /\
  elements_null_data_selected_initial m bd dbase bw edge cur 261
    be ebase bt txbase bout outbase i (Int64.repr (toZ jw)) parsed unused_hash.

Lemma elements_null_data_layout_payload_alloc m ma mc bl bd dbase bw edge cur bi inedge rc
    be ebase bt txbase bout outbase i jw parsed unused_hash :
  Mem.alloc m 0 16 = (ma, bl) ->
  (forall chunk b ofs v, Mem.load chunk m b ofs = Some v -> Mem.load chunk mc b ofs = Some v) ->
  elements_null_data_layout_payload m bd dbase bw edge cur bi inedge rc
    be ebase bt txbase bout outbase i jw parsed unused_hash ->
  elements_null_data_rest_payload mc bl bd dbase bw edge cur bi inedge rc
    be ebase bt txbase bout outbase i jw parsed unused_hash.
Proof.
  intros HA HM (HJ & HSep & Hlen & HCount & HCsep & HSelected).
  unfold elements_null_data_rest_payload. split.
  - eapply frame_input_bits_at_preserved; [|exact HJ]. intros ofs w HL. apply HM; exact HL.
  - split; [exact HSep|]. split; [exact Hlen|]. split.
    + eapply elements_null_data_count_path_mono; eassumption.
    + split; [exact HCsep|]. eapply elements_null_data_selected_initial_alloc; eassumption.
Qed.

Lemma elements_null_data_layout_shape :
  elements_wrapper_shape f_simplicity_output_null_datum elements_null_data_rest.
Proof.
  repeat split; try reflexivity.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

(** Internal form with a real output block. The nullable corollary below
    removes that premise in the out-of-range case. *)
Theorem eval_elements_null_data_output_block parsed unused_hash (iw jw : Ty.tySem Word32)
    m bd dbase bs sbase bi bw edge cur inedge rc be ebase bt txbase bout outbase count flag :
  frame_base_valid sbase -> (8 | sbase) ->
  frame_fields_at m bs sbase bi inedge rc -> frame_input_word_at m bi inedge rc iw ->
  0 <= rc <= Int64.max_unsigned - 64 -> Mem.valid_block m bout ->
  elements_null_data_output_rep m be ebase bt txbase bout outbase (Int64.repr (toZ iw)) count flag ->
  (andb (Int64.ltu (Int64.repr (toZ iw)) count) flag = true ->
    elements_null_data_layout_payload m bd dbase bw edge cur bi inedge rc
      be ebase bt txbase bout outbase (Int64.repr (toZ iw)) jw parsed unused_hash) ->
  write_frame_at m bd dbase bw edge cur 261 ->
  exists mf,
    Clight2.eval_funcall elements_ge m (Internal f_simplicity_output_null_datum)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); Vptr be (Ptrofs.repr ebase)] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw edge cur
      (@encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit OpcodeTy))
        (elements_null_data_guard_value parsed unused_hash (andb (Int64.ltu (Int64.repr (toZ iw)) count) flag) jw)) /\
    write_prefix_at m mf bw edge cur /\ frame_fields_at mf bd dbase bw edge (cur - 261) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cur - 261) / 64) \/ write_word_address edge cur + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HAlign HFields HInput Hrc Vout HOutput HPayload HF.
  pose proof HFields as [HSE HSO].
  destruct (frame_loadbytes_at m bs sbase _ _ HSE HSO) as [bytes HB].
  eapply elements_wrapper_layout with (rest := elements_null_data_rest) (bytes := bytes);
    [exact elements_null_data_layout_shape|exact HSbase|exact HAlign|exact HB|lia|exact HF|].
  intros ma mc bl HA SC HM HP HFC.
  assert (Vs : Mem.valid_block m bs) by (eapply load_valid_block; exact HSE).
  assert (HBa : Mem.loadbytes ma bs sbase 16 = Some bytes) by
    (erewrite Mem.loadbytes_alloc_unchanged; eauto).
  assert (HSEa : Mem.load Mptr ma bs sbase = Some (Vptr bi (Ptrofs.repr inedge))) by
    (eapply Mem.load_alloc_other; eauto).
  assert (HSOa : Mem.load Mint64 ma bs (sbase + 8) = Some (Vlong (Int64.repr rc))) by
    (eapply Mem.load_alloc_other; eauto).
  destruct (frame_copy_fields_at ma mc bs sbase bl bytes _ _ HBa SC HSEa HSOa) as [HLE HLO].
  assert (HInputC : frame_input_word_at mc bi inedge rc iw).
  { eapply frame_input_bits_at_preserved; [|exact HInput]. intros ofs w HL. apply HM; exact HL. }
  assert (PLC : Mem.valid_access mc Mint64 bl 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC|].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA|lia|cbn; lia|]. exists 1; reflexivity. }
  destruct (wide_input_first_load W32 m bi inedge rc iw HInput) as [wi Hwi].
  pose proof HF as (_ & HDF & _).
  destruct (write_frame_at_head m bd dbase bw edge cur 261 ltac:(lia) HF) as (_ & _ & _ & wo & Hwo).
  pose proof HOutput as (_ & _ & _ & _ & HE & HT & _).
  assert (Hli : bl <> bi) by (eapply fresh_frame_not_loaded; eauto).
  assert (Hld : bl <> bd) by (destruct HDF as [HDE HDO]; eapply fresh_frame_not_loaded; eauto).
  assert (Hlw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
  assert (Hle : bl <> be) by (eapply fresh_frame_not_loaded; eauto).
  assert (Hlt : bl <> bt) by (eapply fresh_frame_not_loaded; eauto).
  assert (Hlo : bl <> bout) by (intro EQ; subst bout; exact (Mem.fresh_block_alloc _ _ _ _ _ HA Vout)).
  assert (HOutputC : elements_null_data_output_rep mc be ebase bt txbase bout outbase (Int64.repr (toZ iw)) count flag).
  { eapply elements_null_data_output_rep_mono; eassumption. }
  assert (HPayloadC : andb (Int64.ltu (Int64.repr (toZ iw)) count) flag = true ->
    elements_null_data_rest_payload mc bl bd dbase bw edge cur bi inedge rc
      be ebase bt txbase bout outbase (Int64.repr (toZ iw)) jw parsed unused_hash).
  { intros HG. eapply elements_null_data_layout_payload_alloc; [exact HA|exact HM|apply HPayload; exact HG]. }
  destruct (exec_elements_null_data_rest parsed unused_hash iw jw (elements_version_locals bl)
    (elements_wrapper_temps f_simplicity_output_null_datum (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase)
    mc bl bd dbase bw edge cur bi inedge rc be ebase bt txbase bout outbase count flag
    eq_refl eq_refl eq_refl eq_refl eq_refl
    ltac:(unfold elements_wrapper_temps; rewrite !PTree.gso by discriminate; apply PTree.gss)
    ltac:(unfold elements_wrapper_temps; apply PTree.gss)
    Hrc (conj HLE HLO) HInputC PLC Hli Hld Hlw Hle Hlt Hlo HOutputC HPayloadC HFC)
    as (le' & me & HC & HEff).
  exists le', me. exact (conj HC HEff).
Qed.


Theorem eval_elements_null_data_nullable_layout parsed unused_hash (iw jw : Ty.tySem Word32)
    m bd dbase bs sbase bi bw edge cur inedge rc be ebase bt txbase bout outbase count flag :
  frame_base_valid sbase -> (8 | sbase) ->
  frame_fields_at m bs sbase bi inedge rc -> frame_input_word_at m bi inedge rc iw ->
  0 <= rc <= Int64.max_unsigned - 64 ->
  elements_null_data_output_rep m be ebase bt txbase bout outbase (Int64.repr (toZ iw)) count flag ->
  (andb (Int64.ltu (Int64.repr (toZ iw)) count) flag = true ->
    elements_null_data_layout_payload m bd dbase bw edge cur bi inedge rc
      be ebase bt txbase bout outbase (Int64.repr (toZ iw)) jw parsed unused_hash) ->
  write_frame_at m bd dbase bw edge cur 261 ->
  exists mf,
    Clight2.eval_funcall elements_ge m (Internal f_simplicity_output_null_datum)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); Vptr be (Ptrofs.repr ebase)] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw edge cur
      (@encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit OpcodeTy))
        (elements_null_data_guard_value parsed unused_hash (andb (Int64.ltu (Int64.repr (toZ iw)) count) flag) jw)) /\
    write_prefix_at m mf bw edge cur /\ frame_fields_at mf bd dbase bw edge (cur - 261) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cur - 261) / 64) \/ write_word_address edge cur + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HS HA HFields HInput Hrc HOutput HPayload HF.
  destruct (Int64.ltu (Int64.repr (toZ iw)) count) eqn:HR.
  - rewrite <- HR.
    eapply eval_elements_null_data_output_block with (iw := iw) (jw := jw) (bout := bout) (outbase := outbase);
      [exact HS|exact HA|exact HFields|exact HInput|exact Hrc| |exact HOutput| |exact HF].
    + destruct HOutput as (_ & _ & _ & _ & _ & _ & Hmore).
      specialize (Hmore HR) as (_ & _ & _ & HL). eapply load_valid_block; exact HL.
    + rewrite HR. exact HPayload.
  - pose proof HOutput as (He0 & HeM & Ht0 & HtM & HE & HT & _).
    assert (HOutput0 : elements_null_data_output_rep m be ebase bt txbase bt 0 (Int64.repr (toZ iw)) count flag).
    { eapply elements_null_data_output_rep_out_of_range; eassumption. }
    rewrite <- HR.
    eapply eval_elements_null_data_output_block with (iw := iw) (jw := jw) (bout := bt) (outbase := 0);
      [exact HS|exact HA|exact HFields|exact HInput|exact Hrc| |exact HOutput0| |exact HF].
    + eapply load_valid_block; exact HT.
    + rewrite HR. intros HG. discriminate.
Qed.

Definition elements_output_null_datum_spec {alg : Primitive.Algebra} :
    alg (Ty.Prod Word32 Word32) (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit OpcodeTy)) :=
  Primitive.Combinators.prim Elements.OutputNullDatum.

Theorem elements_output_null_datum_initial_equivalence environment parsed unused_hash (iw jw : Ty.tySem Word32)
    m bd dbase bs sbase bi bw edge cur inedge rc be ebase bt txbase bout outbase count flag :
  frame_base_valid sbase -> (8 | sbase) ->
  frame_fields_at m bs sbase bi inedge rc -> frame_input_word_at m bi inedge rc iw ->
  0 <= rc <= Int64.max_unsigned - 64 ->
  elements_null_data_output_rep m be ebase bt txbase bout outbase (Int64.repr (toZ iw)) count flag ->
  (andb (Int64.ltu (Int64.repr (toZ iw)) count) flag = true ->
    elements_null_data_layout_payload m bd dbase bw edge cur bi inedge rc
      be ebase bt txbase bout outbase (Int64.repr (toZ iw)) jw parsed unused_hash) ->
  (match nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ iw)) with
   | Some txo => txNullData (txoScript txo)
   | None => None
   end) = (if andb (Int64.ltu (Int64.repr (toZ iw)) count) flag then Some parsed else None) ->
  write_frame_at m bd dbase bw edge cur 261 ->
  exists mf value,
    @elements_output_null_datum_spec (PrimitivePrimSem option_Monad_Zero) (iw, jw) environment = Some value /\
    Clight2.eval_funcall elements_ge m (Internal f_simplicity_output_null_datum)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); Vptr be (Ptrofs.repr ebase)] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw edge cur (@encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit OpcodeTy)) value) /\
    write_prefix_at m mf bw edge cur /\ frame_fields_at mf bd dbase bw edge (cur - 261) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cur - 261) / 64) \/ write_word_address edge cur + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HS HA HFields HInput Hrc HOutput HPayload HLogical HF.
  destruct (eval_elements_null_data_nullable_layout parsed unused_hash iw jw m bd dbase bs sbase bi bw edge cur
    inedge rc be ebase bt txbase bout outbase count flag HS HA HFields HInput Hrc HOutput HPayload HF) as (mf & HE).
  exists mf, (elements_null_data_guard_value parsed unused_hash (andb (Int64.ltu (Int64.repr (toZ iw)) count) flag) jw).
  split; [|exact HE].
  change (Elements.sem Elements.OutputNullDatum (iw, jw) environment =
    Some (elements_null_data_guard_value parsed unused_hash
      (andb (Int64.ltu (Int64.repr (toZ iw)) count) flag) jw)).
  apply elements_output_null_datum_guard_sem; exact HLogical.
Qed.
