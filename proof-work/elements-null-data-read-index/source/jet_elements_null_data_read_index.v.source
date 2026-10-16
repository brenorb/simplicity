(** The actual second read followed by the opcode-index block.
    The local source cursor changes; public framing excludes that private block
    until the wrapper's actual free discharges it. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Maps Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_prim C.jet_elements_current_reader.
Require Import C.jet_elements_null_data_loads C.jet_elements_null_data_small C.jet_elements_null_data_payload.
Require Import C.jet_elements_null_data_opcode C.jet_elements_null_data_index C.jet_elements_effects.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_write_layout C.jet_uint32_array_init.
Require Import C.jet_elements_wrapper C.jet_application_sep.
Require Import C.jet_encoding.
Require Import C.jet_output_sequence_step.
Require C.jet_bitmachine_rep.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Local Notation OpcodeTy := (Ty.Sum (Ty.Prod (Word 1) (Word 8)) (Ty.Sum (Ty.Sum Ty.Unit Ty.Unit) (Word 2))).

Definition write_effect_private bl m mf bd dbase bw edge cur count cells : Prop :=
  frame_output_cells_at mf bw edge cur cells /\ write_prefix_at m mf bw edge cur /\
  frame_fields_at mf bd dbase bw edge (cur - count) /\
  (forall chunk b ofs, b <> bl ->
    (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
    (b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cur - count) / 64) \/
      write_word_address edge cur + 8 <= ofs) ->
    Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
  (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
  (forall b, Mem.valid_block m b -> Mem.valid_block mf b).

Lemma write_effect_private_interleaved m m1 mr mf bl bd dbase bw edge cur n bit cells :
  bl <> bw -> 0 <= n -> write_frame_at m bd dbase bw edge cur (1 + n) ->
  write_effect m m1 bd dbase bw edge cur 1 [Some bit] ->
  (forall chunk b ofs, b <> bl -> Mem.load chunk mr b ofs = Mem.load chunk m1 b ofs) ->
  (forall b ofs kind p, Mem.perm m1 b ofs kind p -> Mem.perm mr b ofs kind p) ->
  (forall b, Mem.valid_block m1 b -> Mem.valid_block mr b) ->
  write_effect mr mf bd dbase bw edge (cur - 1) n cells ->
  write_effect_private bl m mf bd dbase bw edge cur (1 + n) ([Some bit] ++ cells).
Proof.
  intros Hbl Hn HF (O1 & P1 & F1 & L1 & PM1 & V1) HM HP HV (O2 & P2 & F2 & L2 & PM2 & V2).
  pose proof HF as (_ & _ & _ & HCur & _).
  assert (KI : forall ofs w, Mem.load Mint64 m1 bw ofs = Some (Vlong w) ->
    Mem.load Mint64 mr bw ofs = Some (Vlong w)).
  { intros ofs w HL. rewrite HM by congruence. exact HL. }
  unfold write_effect_private. split.
  - apply frame_output_cells_at_app. split.
    + eapply frame_output_cells_prefix_preserved with (m := mr) (bf := bd) (base := dbase)
        (cursor := cur - 1) (low := edge + 8 * ((cur - 1 - n) / 64)).
      * intros k HK. pose proof HF as (_ & _ & _ & _ & _ & _ & HWords).
        destruct (HWords (Z.of_nat k) ltac:(cbn [length] in HK; lia)) as (_ & _ & HD & _). exact HD.
      * cbn [length]. lia.
      * exact P2.
      * exact L2.
      * eapply frame_output_cells_load_preserved; [exact KI|exact O1].
    + cbn [length]. exact O2.
  - split.
    + assert (P1R : write_prefix_at m mr bw edge cur).
      { eapply write_prefix_at_preserved with (mr := m) (me := m1);
          [intros; assumption|exact KI|exact P1]. }
      eapply write_prefix_at_chain with (mi := mr) (bf := bd) (base := dbase)
        (next := cur - 1) (low := edge + 8 * ((cur - 1 - n) / 64));
        [apply (write_frame_at_head_separate m bd dbase bw edge cur (1 + n) ltac:(lia) HF)|lia|
         exact P1R|exact P2|exact L2].
    + split.
      * replace (cur - (1 + n)) with (cur - 1 - n) by lia. exact F2.
      * split.
        -- intros chunk b ofs HB HD HW.
           assert (HW2 : b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cur - 1 - n) / 64) \/
             write_word_address edge (cur - 1) + 8 <= ofs).
           { destruct HW as [H|[H|H]]; [left; exact H|right; left; replace (cur - 1 - n) with (cur - (1+n)) by lia; exact H|].
             right; right. unfold write_word_address in *.
             pose proof (Z.div_le_mono (cur - 1 - 1) (cur - 1) 64 ltac:(lia) ltac:(lia)). lia. }
           rewrite (L2 chunk b ofs HD HW2), HM by exact HB.
           assert (HW1 : b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cur - 1) / 64) \/
             write_word_address edge cur + 8 <= ofs).
           { destruct HW as [H|[H|H]]; [left; exact H| |right; right; exact H].
             right; left. pose proof (Z.div_le_mono (cur - (1+n)) (cur - 1) 64 ltac:(lia) ltac:(lia)). lia. }
           apply L1; assumption.
        -- split; [intros; apply PM2, HP, PM1; assumption|intros; apply V2, HV, V1; assumption].
Qed.

Lemma elements_null_data_count_path_read_preserved m mr bl be ebase bt txbase bout outbase i count :
  bl <> be -> bl <> bt -> bl <> bout ->
  (forall chunk b ofs, b <> bl -> Mem.load chunk mr b ofs = Mem.load chunk m b ofs) ->
  elements_null_data_count_path m be ebase bt txbase bout outbase i count ->
  elements_null_data_count_path mr be ebase bt txbase bout outbase i count.
Proof.
  intros He Ht Ho HM (He0 & HeM & Ht0 & HtM & Ho0 & HoM & L1 & L2 & L3).
  unfold elements_null_data_count_path. do 6 (split; [assumption|]).
  split; [rewrite HM by congruence; exact L1|].
  split; [rewrite HM by congruence; exact L2|rewrite HM by congruence; exact L3].
Qed.

Lemma elements_null_data_path_read_preserved m mr bl be ebase bt txbase bout outbase bop opbase i j code :
  bl <> be -> bl <> bt -> bl <> bout -> bl <> bop ->
  (forall chunk b ofs, b <> bl -> Mem.load chunk mr b ofs = Mem.load chunk m b ofs) ->
  elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j code ->
  elements_null_data_path_valid mr be ebase bt txbase bout outbase bop opbase i j code.
Proof.
  intros He Ht Ho Hp HM (He0 & HeM & Ht0 & HtM & Ho0 & HoM & Hp0 & HpM & L1 & L2 & L3 & L4).
  unfold elements_null_data_path_valid. do 8 (split; [assumption|]).
  unfold elements_null_data_path_loads. repeat split; rewrite HM by congruence; assumption.
Qed.

(** Freshness of the selected environment blocks is a physical allocation
    condition. The wrapper must derive it from the real private allocation. *)
Definition elements_null_data_selected_private m bl bd dbase bw edge cur be ebase bt txbase bout outbase i j
    (parsed : list (txNullDatumF (list byte))) unused_hash : Prop :=
  forall d, nth_error parsed (Z.to_nat (Int64.unsigned j)) = Some d ->
  exists bop opbase,
    bl <> bop /\
    elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j
      (elements_datum_code (mapNullDatum byteStringHash d)) /\
    Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 260 b lo hi)
      (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j) /\
    (if elements_datum_push (mapNullDatum byteStringHash d) then
      uint32_array_at m bop (opbase + 36 * Int64.unsigned j)
        (hash256_reg (elements_datum_hash (mapNullDatum byteStringHash d) unused_hash)) /\
      out_sep bd dbase bw edge cur 260 bop (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32)
      else True).

Lemma elements_null_data_selected_read_preserved m mr bl bd dbase bw edge cur be ebase bt txbase bout outbase i j
    parsed unused_hash :
  bl <> be -> bl <> bt -> bl <> bout ->
  (forall chunk b ofs, b <> bl -> Mem.load chunk mr b ofs = Mem.load chunk m b ofs) ->
  elements_null_data_selected_private m bl bd dbase bw edge cur be ebase bt txbase bout outbase i j parsed unused_hash ->
  elements_null_data_index_selected mr bd dbase bw edge cur be ebase bt txbase bout outbase i j parsed unused_hash.
Proof.
  intros He Ht Ho HM Hsel d HD.
  destruct (Hsel d HD) as (bop & opbase & Hp & HPath & HSEP & HHash).
  exists bop, opbase. split.
  - eapply elements_null_data_path_read_preserved; eassumption.
  - split; [exact HSEP|].
    destruct (elements_datum_push (mapNullDatum byteStringHash d)); [|exact I].
    destruct HHash as [HA HS]. split; [|exact HS].
    intros k x HX. rewrite HM by congruence. exact (HA k x HX).
Qed.

Lemma elements_null_data_selected_private_fresh m ma bl bd dbase bw edge cur be ebase bt txbase bout outbase i j
    parsed unused_hash :
  Mem.alloc m 0 16 = (ma, bl) ->
  elements_null_data_index_selected m bd dbase bw edge cur be ebase bt txbase bout outbase i j parsed unused_hash ->
  elements_null_data_selected_private m bl bd dbase bw edge cur be ebase bt txbase bout outbase i j parsed unused_hash.
Proof.
  intros HA Hselected d HD.
  destruct (Hselected d HD) as (bop & opbase & HP & HS & HH).
  exists bop, opbase. split; [|exact (conj HP (conj HS HH))].
  pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HCode).
  intros Eq. subst bop. apply (Mem.fresh_block_alloc _ _ _ _ _ HA).
  eapply C.jet_bitmachine_rep.load_valid_block; exact HCode.
Qed.

Lemma elements_null_data_count_blocks_fresh m ma bl be ebase bt txbase bout outbase i count :
  Mem.alloc m 0 16 = (ma, bl) ->
  elements_null_data_count_path m be ebase bt txbase bout outbase i count ->
  bl <> be /\ bl <> bt /\ bl <> bout.
Proof.
  intros HA (_ & _ & _ & _ & _ & _ & L1 & L2 & L3).
  repeat split; intros Eq; subst; apply (Mem.fresh_block_alloc _ _ _ _ _ HA);
    eapply C.jet_bitmachine_rep.load_valid_block; eassumption.
Qed.

Definition elements_null_data_read_index_block : statement :=
  Ssequence (elements_read32_current_stmt _t'2 _j) elements_null_data_index_block.

Theorem exec_elements_null_data_read_index_block parsed unused_hash e le m bl bd dbase bw edge cur
    bi inedge rc (jw : Ty.tySem Word32) be ebase bt txbase bout outbase i :
  e!_simplicity_read32 = None -> e!_src = Some (bl, Tstruct _frameItem noattr) ->
  e!_writeBit = None -> e!_skipBits = None -> e!_writeHash = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) ->
  0 <= rc <= Int64.max_unsigned - 32 ->
  frame_fields_at m bl 0 bi inedge rc -> frame_input_word_at m bi inedge rc jw ->
  Mem.valid_access m Mint64 bl 8 Writable ->
  bl <> bi -> bl <> bd -> bl <> bw -> bl <> be -> bl <> bt -> bl <> bout ->
  Z.of_nat (length parsed) <= Int64.max_unsigned ->
  elements_null_data_count_path m be ebase bt txbase bout outbase i (Int64.repr (Z.of_nat (length parsed))) ->
  (forall r, Int64.unsigned r = @toZ (WordToZ 5) jw ->
    elements_null_data_selected_private m bl bd dbase bw edge cur be ebase bt txbase bout outbase i r parsed unused_hash) ->
  write_frame_at m bd dbase bw edge cur 260 ->
  exists le' mf r,
    Int64.unsigned r = @toZ (WordToZ 5) jw /\
    Clight2.exec_stmt elements_ge e le m elements_null_data_read_index_block E0 le' mf Out_normal /\
    write_effect_private bl m mf bd dbase bw edge cur 260
      (@encode (Ty.Sum Ty.Unit OpcodeTy) (elements_null_data_index_value parsed r unused_hash)) /\
    exists mr,
      (forall chunk b ofs, b <> bl -> Mem.load chunk mr b ofs = Mem.load chunk m b ofs) /\
      (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr b ofs kind p) /\
      (forall b, Mem.valid_block m b -> Mem.valid_block mr b) /\
      write_effect mr mf bd dbase bw edge cur 260
        (@encode (Ty.Sum Ty.Unit OpcodeTy) (elements_null_data_index_value parsed r unused_hash)).
Proof.
  intros HRd HSrc HW HS HH HD Henv Hi Hrc HFields HInput HAccess Hli Hld Hlw Hle Hlt Hlo Hlen HCount HSelected HFrame.
  destruct (exec_elements_read32_current _t'2 _j e le m bl bi inedge rc jw HRd HSrc Hrc HFields HInput HAccess Hli)
    as (mr & r & CR & HR & HFieldsR & HLoads & HPerm & HValid).
  set (next := PTree.set _j (Vlong r) (PTree.set _t'2 (Vlong r) le)).
  assert (HM : forall chunk b ofs, b <> bl -> Mem.load chunk mr b ofs = Mem.load chunk m b ofs).
  { intros chunk b ofs Hb. apply HLoads. left; exact Hb. }
  assert (HD' : next!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold next. rewrite !PTree.gso by discriminate. exact HD. }
  assert (Henv' : next!_env = Some (Vptr be (Ptrofs.repr ebase))).
  { unfold next. rewrite !PTree.gso by discriminate. exact Henv. }
  assert (Hi' : next!_i = Some (Vlong i)).
  { unfold next. rewrite !PTree.gso by discriminate. exact Hi. }
  assert (Hj' : next!_j = Some (Vlong r)).
  { unfold next. apply PTree.gss. }
  assert (HCountR : elements_null_data_count_path mr be ebase bt txbase bout outbase i (Int64.repr (Z.of_nat (length parsed)))).
  { eapply elements_null_data_count_path_read_preserved; eassumption. }
  assert (HSelectedR : elements_null_data_index_selected mr bd dbase bw edge cur be ebase bt txbase bout outbase i r parsed unused_hash).
  { eapply elements_null_data_selected_read_preserved; [exact Hle|exact Hlt|exact Hlo|exact HM|].
    apply HSelected; exact HR. }
  assert (HFrameR : write_frame_at mr bd dbase bw edge cur 260).
  { eapply write_frame_at_preserved with (m := m); [|exact HPerm|exact HFrame].
    intros chunk b ofs v Hb HL. rewrite HM; [exact HL|]. destruct Hb; subst; congruence. }
  destruct (exec_elements_null_data_index_block parsed unused_hash e next mr bd dbase bw edge cur
    be ebase bt txbase bout outbase i r Hlen HW HS HH HD' Henv' Hi' Hj' HCountR HSelectedR HFrameR)
    as (le' & mf & CI & EI).
  exists le', mf, r. split; [exact HR|]. split.
  - unfold elements_null_data_read_index_block.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact CR|exact CI].
  - split.
    + unfold write_effect_private. eapply write_effect_lift; eassumption.
    + exists mr. exact (conj HM (conj HPerm (conj HValid EI))).
Qed.

Fixpoint elements_find_index_read_arm (s : statement) : option statement :=
  match s with
  | Ssequence a b =>
      match a with
      | Ssequence (Scall (Some id) (Evar fn _) _) _ =>
          if Pos.eqb id _t'2 && Pos.eqb fn _simplicity_read32 then Some s else
            elements_stmt_first (elements_find_index_read_arm a) (elements_find_index_read_arm b)
      | _ => elements_stmt_first (elements_find_index_read_arm a) (elements_find_index_read_arm b)
      end
  | Sifthenelse _ a b | Sloop a b =>
      elements_stmt_first (elements_find_index_read_arm a) (elements_find_index_read_arm b)
  | _ => None
  end.

Lemma elements_null_data_read_index_source :
  elements_find_index_read_arm (fn_body f_simplicity_output_null_datum) = Some elements_null_data_read_index_block.
Proof. reflexivity. Qed.
