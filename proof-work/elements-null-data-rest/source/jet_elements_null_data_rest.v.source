(** Both actual input reads, the full output block and the return statement.
    Function entry, the by-value copy and free are supplied by the wrapper. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_prim C.jet_elements_current_reader.
Require Import C.jet_elements_null_data_output_guard C.jet_elements_null_data_read_index.
Require Import C.jet_elements_null_data_guard_compose C.jet_elements_null_data_loads.
Require Import C.jet_elements_null_data_small C.jet_elements_null_data_payload C.jet_elements_null_data_opcode.
Require Import C.jet_elements_null_data_index C.jet_elements_effects C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_write_layout C.jet_uint32_array_init C.jet_encoding C.jet_application_sep.
Require Import C.jet_elements_wrapper.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Local Notation OpcodeTy := (Ty.Sum (Ty.Prod (Word 1) (Word 8)) (Ty.Sum (Ty.Sum Ty.Unit Ty.Unit) (Word 2))).

Lemma write_effect_private_lift_source m mr mf bl bd dbase bw edge cur n cells :
  bl <> bw ->
  (forall chunk b ofs, b <> bl -> Mem.load chunk mr b ofs = Mem.load chunk m b ofs) ->
  (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr b ofs kind p) ->
  (forall b, Mem.valid_block m b -> Mem.valid_block mr b) ->
  write_effect_private bl mr mf bd dbase bw edge cur n cells ->
  write_effect_private bl m mf bd dbase bw edge cur n cells.
Proof.
  intros Hbl HM HP HV (HO & HPfx & HF & HL & HPerm & HValid).
  unfold write_effect_private. split; [exact HO|]. split.
  - eapply write_prefix_at_preserved with (mr := mr) (me := mf); [|intros; assumption|exact HPfx].
    intros ofs w HW. rewrite HM by congruence. exact HW.
  - split; [exact HF|]. split.
    + intros chunk b ofs Hb Hd Hw. rewrite HL by assumption. apply HM; exact Hb.
    + split; [intros; apply HPerm, HP; assumption|intros; apply HValid, HV; assumption].
Qed.

Lemma elements_null_data_output_rep_read_preserved m mr bl be ebase bt txbase bout outbase i count flag :
  bl <> be -> bl <> bt -> bl <> bout ->
  (forall chunk b ofs, b <> bl -> Mem.load chunk mr b ofs = Mem.load chunk m b ofs) ->
  elements_null_data_output_rep m be ebase bt txbase bout outbase i count flag ->
  elements_null_data_output_rep mr be ebase bt txbase bout outbase i count flag.
Proof.
  intros He Ht Ho HM (He0 & HeM & Ht0 & HtM & L1 & L2 & Hmore).
  unfold elements_null_data_output_rep. do 4 (split; [assumption|]).
  split; [rewrite HM by congruence; exact L1|].
  split; [rewrite HM by congruence; exact L2|].
  intros HC. specialize (Hmore HC) as (Ho0 & HoM & L3 & L4).
  do 2 (split; [assumption|]). split; rewrite HM by congruence; assumption.
Qed.

Lemma elements_null_data_selected_footprint_read_preserved m mr bl bd dbase bw edge cur n
    be ebase bt txbase bout outbase i j parsed unused_hash :
  bl <> be -> bl <> bt -> bl <> bout ->
  (forall chunk b ofs, b <> bl -> Mem.load chunk mr b ofs = Mem.load chunk m b ofs) ->
  elements_null_data_selected_footprint m bl bd dbase bw edge cur n
    be ebase bt txbase bout outbase i j parsed unused_hash ->
  elements_null_data_selected_footprint mr bl bd dbase bw edge cur n
    be ebase bt txbase bout outbase i j parsed unused_hash.
Proof.
  intros He Ht Ho HM Hsel d HD.
  destruct (Hsel d HD) as (bop & opbase & Hbl & HP & HS & HH).
  exists bop, opbase. split; [exact Hbl|]. split.
  - eapply elements_null_data_path_read_preserved; eassumption.
  - split; [exact HS|]. destruct (elements_datum_push (mapNullDatum byteStringHash d)); [|exact I].
    destruct HH as [HA Hsep]. split; [|exact Hsep].
    intros k x HX. rewrite HM by congruence. exact (HA k x HX).
Qed.

Definition elements_null_data_rest : statement :=
  Ssequence (elements_read32_current_stmt _t'1 _i) (elements_simple_rest elements_null_data_guard_block).

Lemma elements_null_data_rest_source :
  fn_body f_simplicity_output_null_datum = elements_wrapper_body elements_null_data_rest.
Proof. reflexivity. Qed.

(** Only the true branch needs a second logical word and parsed-opcode data.
    The fields here all concern the initial memory, not a desired intermediate. *)
Definition elements_null_data_rest_payload m bl bd dbase bw edge cur bi inedge rc
    be ebase bt txbase bout outbase i (jw : Ty.tySem Word32) parsed unused_hash : Prop :=
  frame_input_word_at m bi inedge (rc + 32) jw /\
  (forall k, 0 <= k < 32 -> out_sep bd dbase bw edge cur 261 bi
    (inedge - 8 * (1 + (rc + 32 + k) / 64)) (inedge - 8 * (1 + (rc + 32 + k) / 64) + 8)) /\
  Z.of_nat (length parsed) <= Int64.max_unsigned /\
  elements_null_data_count_path m be ebase bt txbase bout outbase i (Int64.repr (Z.of_nat (length parsed))) /\
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 261 b lo hi)
    (elements_null_data_count_footprint be ebase bt txbase bout outbase i) /\
  elements_null_data_selected_footprint m bl bd dbase bw edge cur 261
    be ebase bt txbase bout outbase i (Int64.repr (toZ jw)) parsed unused_hash.

Theorem exec_elements_null_data_rest parsed unused_hash (iw jw : Ty.tySem Word32)
    e le m bl bd dbase bw edge cur bi inedge rc be ebase bt txbase bout outbase count flag :
  e!_simplicity_read32 = None -> e!_src = Some (bl, Tstruct _frameItem noattr) ->
  e!_writeBit = None -> e!_skipBits = None -> e!_writeHash = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) -> le!_env = Some (Vptr be (Ptrofs.repr ebase)) ->
  0 <= rc <= Int64.max_unsigned - 64 ->
  frame_fields_at m bl 0 bi inedge rc -> frame_input_word_at m bi inedge rc iw ->
  Mem.valid_access m Mint64 bl 8 Writable ->
  bl <> bi -> bl <> bd -> bl <> bw -> bl <> be -> bl <> bt -> bl <> bout ->
  elements_null_data_output_rep m be ebase bt txbase bout outbase (Int64.repr (toZ iw)) count flag ->
  (andb (Int64.ltu (Int64.repr (toZ iw)) count) flag = true ->
    elements_null_data_rest_payload m bl bd dbase bw edge cur bi inedge rc
      be ebase bt txbase bout outbase (Int64.repr (toZ iw)) jw parsed unused_hash) ->
  write_frame_at m bd dbase bw edge cur 261 ->
  exists le' mf, Clight2.exec_stmt elements_ge e le m elements_null_data_rest E0 le' mf elements_returned_one /\
    write_effect_private bl m mf bd dbase bw edge cur 261
      (@encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit OpcodeTy))
        (elements_null_data_guard_value parsed unused_hash
          (andb (Int64.ltu (Int64.repr (toZ iw)) count) flag) jw)).
Proof.
  intros HRd HSrc HW HS HH HD Henv Hrc HFields HInput HAccess Hli Hld Hlw Hle Hlt Hlo HOutput HPayload HF.
  destruct (exec_elements_read32_current _t'1 _i e le m bl bi inedge rc iw HRd HSrc
    ltac:(lia) HFields HInput HAccess Hli) as (mr & r & CR & HR & HFieldsR & HL & HP & HV).
  assert (Hr : r = Int64.repr (toZ iw)).
  { rewrite <- (Int64.repr_unsigned r) at 1. rewrite HR. reflexivity. }
  subst r.
  assert (HM : forall chunk b ofs, b <> bl -> Mem.load chunk mr b ofs = Mem.load chunk m b ofs).
  { intros chunk b ofs Hb. apply HL. left; exact Hb. }
  set (next := PTree.set _i (Vlong (Int64.repr (toZ iw))) (PTree.set _t'1 (Vlong (Int64.repr (toZ iw))) le)).
  assert (HD' : next!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold next. rewrite !PTree.gso by discriminate. exact HD. }
  assert (Henv' : next!_env = Some (Vptr be (Ptrofs.repr ebase))).
  { unfold next. rewrite !PTree.gso by discriminate. exact Henv. }
  assert (Hi' : next!_i = Some (Vlong (Int64.repr (toZ iw)))).
  { unfold next. apply PTree.gss. }
  assert (HOutputR : elements_null_data_output_rep mr be ebase bt txbase bout outbase (Int64.repr (toZ iw)) count flag).
  { eapply elements_null_data_output_rep_read_preserved; eassumption. }
  assert (HFRead : write_frame_at mr bd dbase bw edge cur 261).
  { eapply write_frame_at_preserved with (m := m); [|exact HP|exact HF].
    intros chunk b ofs v Hb HLoad. rewrite HM; [exact HLoad|]. destruct Hb; subst; congruence. }
  assert (HReady : andb (Int64.ltu (Int64.repr (toZ iw)) count) flag = true ->
    elements_null_data_guard_ready mr bl bd dbase bw edge cur bi inedge (rc + 32)
      be ebase bt txbase bout outbase (Int64.repr (toZ iw)) jw parsed unused_hash).
  { intros HG. specialize (HPayload HG) as (HJ & HJSep & Hlen & HCount & HCountSep & HSelected).
    unfold elements_null_data_guard_ready. split; [lia|]. split; [exact HFieldsR|]. split.
    - eapply frame_input_bits_at_preserved; [|exact HJ].
      intros ofs w HLoad. rewrite HM by congruence. exact HLoad.
    - split.
      + destruct HAccess as [HA Halign]. split; [|exact Halign]. intros k HK. apply HP, HA; exact HK.
      + do 6 (split; [assumption|]). split; [exact HJSep|]. split; [exact Hlen|]. split.
        * eapply elements_null_data_count_path_read_preserved; eassumption.
        * split; [exact HCountSep|].
          eapply elements_null_data_selected_footprint_read_preserved; eassumption. }
  destruct (exec_elements_null_data_guard_block parsed unused_hash jw e next mr bl bd dbase bw edge cur
    bi inedge (rc + 32) be ebase bt txbase bout outbase (Int64.repr (toZ iw)) count flag
    HRd HSrc HW HS HH HD' Henv' Hi' HOutputR HReady HFRead) as (le' & mf & CG & EG).
  exists le', mf. split.
  - unfold elements_null_data_rest.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact CR|].
    apply exec_elements_simple_rest; exact CG.
  - eapply write_effect_private_lift_source; [exact Hlw|exact HM|exact HP|exact HV|exact EG].
Qed.
