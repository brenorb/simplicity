(** Whole original Elements issuance_hash against the primitive-bearing program.
    The initial raw-field and SHA readiness relation is explicit. No payload
    execution or desired result is assumed at this public boundary. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_memcpy_model C.jet_bitmachine_rep C.jet_application_sep.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_frame_layout.
Require Import C.jet_input_layout C.jet_output_layout C.jet_output_layout_step C.jet_write_layout C.jet_encoding.
Require Import C.jet_constant_layout C.jet_wide C.jet_complement_wide_layout.
Require Import C.jet_read32s_layout C.jet_write32s_layout C.jet_uint32_array_init C.jet_sha256_iv_init.
Require Import C.jet_bitcoin_vh_hash_prep.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_transport C.jet_elements_field_eval.
Require Import C.jet_elements_indexed_exec C.jet_elements_index_eval C.jet_elements_wrapper C.jet_elements_call.
Require Import C.jet_elements_steps C.jet_elements_effects C.jet_elements_env_load C.jet_elements_sha_program.
Require Import C.jet_elements_prim C.jet_elements_asset_jets C.jet_elements_amount_jets C.jet_elements_input_hash_jets.
Require Import C.jet_elements_words_hash_program C.jet_elements_single_issuance_spec.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_block_local C.jet_elements_support_sha_ctx_abs.
Require Import C.jet_elements_support_sha_add_n_exec C.jet_elements_support_sha_compress_call.
Require Import C.jet_elements_support_sha_add_n_init C.jet_elements_support_sha_tapdata_prep C.jet_elements_support_sha_ctxi.
Require Import C.jet_elements_support_sha_add_n_calls.
Require Import C.jet_elements_support_sha_tagged_ctx C.jet_elements_support_sha_hash_io.
Require Import C.jet_elements_support_sha_hash_exec C.jet_elements_support_sha_finalize_exec.
Require Import C.jet_elements_make_tapleaf_exec C.jet_elements_input_utxo_prep C.jet_elements_input_utxo_payload.
Require Import C.jet_elements_single_input_prep C.jet_elements_single_input_payload.
Require Import C.jet_elements_single_input_chain C.jet_elements_single_input_optional.
Require Import C.jet_elements_indexed_ptr_jets C.jet_elements_hash_helpers C.jet_elements_env_tx_calls.
Require Import C.jet_readBit_layout.
Require Import C.jet_elements_single_issuance_spec C.jet_elements_single_issuance_prep.
Require Import C.jet_elements_single_issuance_rep C.jet_elements_single_issuance_dispatch.
Require Import C.jet_elements_indexed_flag.
Require Import C.jet_bitcoin_composite_hash.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64 sha_ge elements_ge.
Set Default Timeout 15.
Local Notation FR := (Tstruct _frameItem noattr).
Local Notation ENVT := (Tstruct _txEnv noattr).
Local Notation TXT := (Tstruct _elementsTransaction noattr).

Ltac nd6 :=
  repeat (apply NoDup_cons;
    [let HIn := fresh in intro HIn; cbn [In] in HIn;
     repeat (destruct HIn as [HIn|HIn]; [revert HIn; ne|]); exact HIn|]);
  apply NoDup_nil.

Definition elements_single_issuance_hash_rep (m : mem) (env : val) (e : Elements.env)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt txbase bin inbase nI,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
    0 <= txbase /\ txbase + 760 <= Ptrofs.max_unsigned /\
    0 <= inbase /\
    inbase + 544 * Z.of_nat (length (sigTxIn (Elements.envTx e))) <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) /\
    Mem.load Mptr m bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)) /\
    Mem.load Mint64 m bt (txbase + 696) = Some (Vlong nI) /\
    Int64.unsigned nI = Z.of_nat (length (sigTxIn (Elements.envTx e))) /\
    (forall j txi, nth_error (sigTxIn (Elements.envTx e)) j = Some txi ->
      eis_elem_rep m bin (inbase + 544 * Z.of_nat j + 256) txi) /\
    sha_globals_ok m /\
    fp = [(be, ebase, ebase + 8); (bt, txbase + 0, txbase + 8);
          (bin, inbase, inbase + 544 * Z.of_nat (length (sigTxIn (Elements.envTx e))));
          (GC, 0, 8); (GM, 0, 8)].

Theorem elements_single_issuance_hash_program_local_spec : memcpy_model ->
  application_jet_local_spec_sep f_simplicity_issuance_hash sha_ge Elements.env
    (Word 5) (Ty.Sum Ty.Unit (Word 8)) elements_single_issuance_hash_rep
    (fun a e => @elements_single_issuance_hash_spec elements_hash_alg a e).
Proof.
  intros Hmodel env0 env m bd dbase bs sbase bi bw edge outedge cursor rc a fp
    (be & ebase & bt & txbase & bin & inbase & nI & HEnvVal & He0 & He1 & Ht0 & Ht1 & Hi0 & Hi1 &
      HLtx & HLin & HLn & HnI & HLelem & [Hdisp HMaxC] & HFp)
    HSep HSbase HSAlign [HSE HSO] H0 Hmax Hin Hout.
  subst env fp.
  set (outs := sigTxIn (Elements.envTx env0)) in *.
  set (nn := Z.of_nat (length outs)) in *.
  change (Z.of_nat (bitSize (Ty.Sum Ty.Unit (Word 8)))) with 257 in *.
  change (Z.of_nat (bitSize (Word 5))) with 32 in Hmax.
  rewrite Forall_forall in HSep.
  assert (S1 : out_sep bd dbase bw outedge cursor 257 be ebase (ebase + 8))
    by exact (HSep (be, ebase, ebase + 8) ltac:(simpl; auto)).
  assert (S2 : out_sep bd dbase bw outedge cursor 257 bt (txbase + 0) (txbase + 8))
    by exact (HSep (bt, txbase + 0, txbase + 8) ltac:(simpl; auto)).
  assert (S3 : out_sep bd dbase bw outedge cursor 257 bin inbase (inbase + 544 * nn))
    by exact (HSep (bin, inbase, inbase + 544 * nn) ltac:(simpl; auto)).
  assert (S4 : out_sep bd dbase bw outedge cursor 257 GC 0 8)
    by exact (HSep (GC, 0, 8) ltac:(do 3 right; left; reflexivity)).
  assert (S5 : out_sep bd dbase bw outedge cursor 257 GM 0 8)
    by exact (HSep (GM, 0, 8) ltac:(do 4 right; left; reflexivity)).
  clear HSep.
  apply frame_input_word_at_encode in Hin.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  destruct (wide_input_first_load W32 m bi edge rc a Hin) as [w0i Hw0i].
  assert (Vi : Mem.valid_block m bi) by (eapply load_valid_block; exact Hw0i).
  assert (Vs : Mem.valid_block m bs) by (eapply load_valid_block; exact HSE).
  pose proof Hout as [HDbase [[HDE HDO] _]].
  assert (Vd : Mem.valid_block m bd) by (eapply load_valid_block; exact HDE).
  destruct (write_frame_at_head m bd dbase bw outedge cursor 257 ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  assert (Vw : Mem.valid_block m bw) by (eapply load_valid_block; exact HInitialWord).
  assert (VG : Mem.valid_block m GC) by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m GM) by (eapply load_valid_block; exact HMaxC).
  assert (Vbe : Mem.valid_block m be) by (eapply load_valid_block; exact HLtx).
  assert (Vbt : Mem.valid_block m bt) by (eapply load_valid_block; exact HLin).
  (* locals *)
  destruct (Mem.alloc m 0 16) as [ma1 bl] eqn:A1.
  destruct (Mem.alloc ma1 0 32) as [ma2 bm] eqn:A2.
  destruct (Mem.alloc ma2 0 88) as [ma3 bx] eqn:A3.
  destruct (Mem.alloc ma3 0 36) as [ma4 bA] eqn:A4.
  destruct (Mem.alloc ma4 0 36) as [ma5 bT] eqn:A5.
  destruct (Mem.alloc ma5 0 40) as [ma6 bZ] eqn:A6.
  destruct (Mem.alloc ma6 0 32) as [ma7 bB] eqn:A7.
  destruct (Mem.alloc ma7 0 88) as [m0 br] eqn:A8.
  assert (HAL : alloc_list m [16; 32; 88; 36; 36; 40; 32; 88] = (m0, [bl; bm; bx; bA; bT; bZ; bB; br])).
  { cbn [alloc_list]. rewrite A1, A2, A3, A4, A5, A6, A7, A8. reflexivity. }
  destruct (alloc_list_props _ _ _ _ HAL) as ((XV & XL & XP & XA) & FRh & ND & FA).
  inversion FA as [|? ? ? ? [PL0 VL0] FA1]; subst.
  inversion FA1 as [|? ? ? ? [PM0 VM0] FA2]; subst.
  inversion FA2 as [|? ? ? ? [PX0 VX0] FA3]; subst.
  inversion FA3 as [|? ? ? ? [PA0 VA0] FA4]; subst.
  inversion FA4 as [|? ? ? ? [PT0 VT0] FA5]; subst.
  inversion FA5 as [|? ? ? ? [PZ0 VZ0] FA6]; subst.
  inversion FA6 as [|? ? ? ? [PB0 VB0] FA7]; subst.
  inversion FA7 as [|? ? ? ? [PR0 VR0] FA8]; subst.
  clear FA FA1 FA2 FA3 FA4 FA5 FA6 FA7 FA8 HAL.
  apply NoDup_cons_iff in ND. destruct ND as [N1 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N2 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N3 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N4 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N5 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N6 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N7 _].
  pose proof (FRh bi Vi) as Nbi. pose proof (FRh bs Vs) as Nbs.
  pose proof (FRh bd Vd) as Nbd. pose proof (FRh bw Vw) as Nbw.
  pose proof (FRh GC VG) as NGC. pose proof (FRh GM VM) as NGM.
  set (e := eis_env bl bm bx bA bT bZ bB br).
  set (le := eis_temps (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase).
  (* the frame copy *)
  assert (HSE0 : Mem.load Mptr m0 bs sbase = Some (Vptr bi (Ptrofs.repr edge)))
    by (rewrite XL by exact Vs; exact HSE).
  assert (HSO0 : Mem.load Mint64 m0 bs (sbase + 8) = Some (Vlong (Int64.repr rc)))
    by (rewrite XL by exact Vs; exact HSO).
  destruct (frame_loadbytes_at m0 bs sbase _ _ HSE0 HSO0) as [bytes HB0].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB0) as Hbyteslen.
  assert (PLW : Mem.range_perm m0 bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hbyteslen. change (Mem.range_perm m0 bl 0 16 Cur Writable).
    intros ofs Hr. eapply Mem.perm_implies; [apply PL0; exact Hr|constructor]. }
  destruct (Mem.range_perm_storebytes m0 bl 0 bytes PLW) as [mc SC].
  destruct (frame_copy_fields_at m0 mc bs sbase bl bytes _ _ HB0 SC HSE0 HSO0) as [HLE HLO].
  assert (Kc : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch mc b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. pose proof (FRh b0 Hv) as Nb.
    erewrite Mem.load_storebytes_other; [|exact SC|left; ne]. apply XL. exact Hv. }
  assert (Pc : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm mc b0 ofs kd p).
  { intros b0 ofs kd p Hp. eapply Mem.perm_storebytes_1; eauto. }
  assert (Vc : forall b0, Mem.valid_block m0 b0 -> Mem.valid_block mc b0).
  { intros b0 Hv. eapply Mem.storebytes_valid_block_1; eauto. }
  assert (HCopy : Clight2.exec_stmt sha_ge e le m0 (Sassign (Evar _src FR) (Etempvar _src FR)) E0 le mc Out_normal).
  { apply (eis_copy e le m0 mc bl bs sbase bytes);
      [reflexivity|exact HSbase|exact HSAlign|ne|reflexivity|exact HB0|exact SC]. }
  (* read32 *)
  assert (HInputC : frame_input_word_at mc bi edge rc a).
  { eapply frame_input_bits_at_preserved; [|exact Hin].
    intros ofs w HL. rewrite Kc by exact Vi. exact HL. }
  assert (PLC : Mem.valid_access mc Mint64 bl (0 + 8) Writable).
  { split; [|exists 1; reflexivity]. intros ofs Hr. change (size_chunk Mint64) with 8 in Hr.
    eapply Mem.perm_implies; [apply Pc, PL0; lia|constructor]. }
  destruct (eval_read_wide_word_at W32 mc bl 0 bi edge rc a HLocalBase ltac:(change (wide_bits W32) with 32; lia)
    (conj HLE HLO) HInputC PLC ltac:(ne))
    as (mr & r & Hread & Hr & HRFields & HRMem & HRPerm & HRValid).
  assert (Hr5 : Int64.unsigned r = @toZ (WordToZ 5) a) by exact Hr.
  apply (elements_transport_call jets._simplicity_read32 jets.f_simplicity_read32
    ltac:(unfold elements_core_helpers; simpl; tauto)) in Hread.
  change (wide_reader W32) with jets.f_simplicity_read32 in Hread.
  assert (Kr : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch mr b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. pose proof (FRh b0 Hv) as Nb.
    rewrite HRMem by (left; ne). apply Kc. exact Hv. }
  assert (Pr : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm mr b0 ofs kd p).
  { intros b0 ofs kd p Hp. apply HRPerm, Pc, Hp. }
  assert (Vr : forall b0, Mem.valid_block m b0 -> Mem.valid_block mr b0).
  { intros b0 Hv. apply HRValid, Vc, XV, Hv. }
  (* writeBit *)
  assert (HFrameR : write_frame_at mr bd dbase bw outedge cursor 257).
  { eapply write_frame_at_preserved; [| |exact Hout].
    - intros ch b0 ofs v0 Hb HL. rewrite Kr; [exact HL|destruct Hb; subst; assumption].
    - intros b0 ofs kd p Hp. apply Pr, XP, Hp. }
  assert (HF1 : write_frame_at mr bd dbase bw outedge cursor 1).
  { eapply write_frame_at_shorter; [|exact HFrameR]. lia. }
  destruct (elements_writeBit_step mr bd dbase bw outedge cursor (Int64.ltu r nI) HF1) as (mb & Hwb1 & E1).
  assert (HFb : write_frame_at mb bd dbase bw outedge (cursor - 1) 256).
  { eapply write_frame_at_after_effect with (cells := [Some (Int64.ltu r nI)]);
      [reflexivity|lia|exact HFrameR|exact E1]. }
  assert (HLoadB : forall chunk b lo hi ofs, out_sep bd dbase bw outedge cursor 257 b lo hi ->
    lo <= ofs -> ofs + size_chunk chunk <= hi -> Mem.load chunk mb b ofs = Mem.load chunk mr b ofs).
  { intros chunk b lo hi ofs Hs Hlo Hhi.
    eapply write_effect_env_load with (bf := bd) (base := dbase) (bw := bw) (edge := outedge)
      (cursor := cursor) (cursor0 := cursor) (count0 := 257) (n := 1)
      (cells := [Some (Int64.ltu r nI)]) (lo := lo) (hi := hi);
      [lia|destruct HF1 as (_ & _ & _ & HC1 & _); lia|lia|lia|exact E1|exact Hs|exact Hlo|exact Hhi]. }
  destruct E1 as (O1 & P1 & F1 & L1 & Pm1 & V1) eqn:HE1.
  assert (E1' : write_effect mr mb bd dbase bw outedge cursor 1 [Some (Int64.ltu r nI)])
    by exact (conj O1 (conj P1 (conj F1 (conj L1 (conj Pm1 V1))))).
  clear HE1.
  assert (Hr0 : 0 <= Int64.unsigned r) by apply Int64.unsigned_range.
  assert (HE0 : Mem.load Mptr mr be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)))
    by (rewrite Kr by exact Vbe; exact HLtx).
  assert (HE2 : Mem.load Mint64 mr bt (txbase + 696) = Some (Vlong nI))
    by (rewrite Kr by exact Vbt; exact HLn).
  set (specv := @elements_single_issuance_hash_spec elements_hash_alg a env0).
  (* the two branches *)
  assert (HTotal : exists V le1 me,
    specv = Some V /\
    Clight2.exec_stmt sha_ge e le mc (elements_indexed_rest_flag _t'3 _t'9 _t'10 _numInputs eis_then eiu_else)
      E0 le1 me elements_returned_one /\
    frame_output_cells_at me bw outedge cursor (encode V) /\
    write_prefix_at mr me bw outedge cursor /\
    frame_fields_at me bd dbase bw outedge (cursor - 257) /\
    (forall ch b0 ofs, Mem.valid_block m b0 ->
      (b0 <> bd \/ ofs + size_chunk ch <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b0 <> bw \/ ofs + size_chunk ch <= outedge + 8 * ((cursor - 257) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load ch me b0 ofs = Mem.load ch mr b0 ofs) /\
    (forall b0 ofs kd p, Mem.perm mb b0 ofs kd p -> Mem.perm me b0 ofs kd p)).
  { destruct (Int64.ltu r nI) eqn:Hb.
    - (* in range *)
      assert (Hlt : Int64.unsigned r < nn).
      { unfold Int64.ltu in Hb.
        destruct (zlt (Int64.unsigned r) (Int64.unsigned nI)) as [Hl|Hnl]; [|discriminate].
        rewrite HnI in Hl. exact Hl. }
      destruct (nth_error outs (Z.to_nat (Int64.unsigned r))) as [o|] eqn:Hnth;
        [|apply nth_error_None in Hnth; unfold nn in Hlt; lia].
      set (ofs := inbase + 544 * Int64.unsigned r).
      set (iofs := ofs + 256).
      assert (Hm : 544 * Int64.unsigned r + 544 <= 544 * nn) by lia.
      pose proof (HLelem _ _ Hnth) as HInput.
      rewrite Z2Nat.id in HInput by lia. fold ofs in HInput. fold iofs in HInput.
      assert (Vbin : Mem.valid_block m bin) by (eapply eis_elem_rep_valid; exact HInput).
      pose proof (FRh bin Vbin) as Nbin. pose proof (FRh be Vbe) as Nbe. pose proof (FRh bt Vbt) as Nbt.
      set (RES := sha256_bytes_of (eis_message o)).
      assert (HSpec : specv = Some (inr (from_hash256 RES))).
      { unfold specv. rewrite elements_single_issuance_hash_sem.
        unfold elements_single_issuance_result. fold outs. rewrite <- Hr5, Hnth.
        unfold RES, eis_message, eis_proof_asset, eis_proof_token. reflexivity. }
      (* memory facts after writeBit *)
      assert (Kb : forall ch b0 lo hi o0, out_sep bd dbase bw outedge cursor 257 b0 lo hi ->
        Mem.valid_block m b0 -> lo <= o0 -> o0 + size_chunk ch <= hi ->
        Mem.load ch mb b0 o0 = Mem.load ch m b0 o0).
      { intros ch b0 lo hi o0 Hs Hv Hlo Hhi. rewrite (HLoadB ch b0 lo hi o0 Hs Hlo Hhi). apply Kr. exact Hv. }
      assert (Hmb0 : Mem.load Mptr mb be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase))).
      { rewrite (Kb Mptr be ebase (ebase + 8)); [exact HLtx|exact S1|exact Vbe|lia|change (size_chunk Mptr) with 8; lia]. }
      assert (Hmb1 : Mem.load Mptr mb bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase))).
      { rewrite (Kb Mptr bt (txbase + 0) (txbase + 8)); [exact HLin|exact S2|exact Vbt|lia|change (size_chunk Mptr) with 8; lia]. }
      assert (Pb : forall b0 ofs0 kd p, Mem.perm m0 b0 ofs0 kd p -> Mem.perm mb b0 ofs0 kd p).
      { intros b0 ofs0 kd p Hp. apply Pm1, Pr, Hp. }
      assert (Vb : forall b0, Mem.valid_block m b0 -> Mem.valid_block mb b0).
      { intros b0 Hv. apply V1, Vr, Hv. }
      (* the context *)
      destruct (ctxi_init bx bm ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) mb br
        ltac:(ne) ltac:(ne) (Vb _ VG) (Vb _ VM) ltac:(ne) ltac:(ne)
        ltac:(intros o0 Hr1; apply Pb, PR0, Hr1) ltac:(intros o0 Hr1; apply Pb, PX0, Hr1)
        ltac:(intros o0 Hr1; apply Pb, PM0, Hr1))
        as (mi & mx & ibytes & HInit & HLBi & HSBi & HAx & HLx & HPx & HVx).
      { unfold sha_dispatch_ok.
        rewrite (Kb Mptr GC 0 8); [exact Hdisp|exact S4|exact VG|lia|change (size_chunk Mptr) with 8; lia]. }
      { rewrite (Kb Mint64 GM 0 8); [exact HMaxC|exact S5|exact VM|lia|change (size_chunk Mint64) with 8; lia]. }
      assert (Kx : forall ch b0 o0, Mem.valid_block m b0 -> Mem.load ch mx b0 o0 = Mem.load ch mb b0 o0).
      { intros ch b0 o0 Hv. pose proof (FRh b0 Hv) as Nb. apply HLx; [apply Vb; exact Hv|ne|ne|ne]. }

      assert (HRepX : eis_elem_rep mx bin iofs o).
      { eapply eis_elem_rep_mono; [exact HInput|].
        intros ch off v Hlo Hhi HL. rewrite Kx by exact Vbin.
        rewrite (Kb ch bin inbase (inbase + 544 * nn));
          [exact HL|exact S3|exact Vbin|unfold iofs, ofs in *; lia|unfold iofs, ofs in *; lia]. }
      set (RPost := fun me : mem =>
        frame_output_cells_at me bw outedge cursor (encode (inr (from_hash256 RES) : Ty.tySem (Ty.Sum Ty.Unit (Word 8)))) /\
        write_prefix_at mr me bw outedge cursor /\
        frame_fields_at me bd dbase bw outedge (cursor - 257) /\
        (forall ch b0 ofs0, Mem.valid_block m b0 ->
          (b0 <> bd \/ ofs0 + size_chunk ch <= dbase + 8 \/ dbase + 16 <= ofs0) ->
          (b0 <> bw \/ ofs0 + size_chunk ch <= outedge + 8 * ((cursor - 257) / 64) \/
            write_word_address outedge cursor + 8 <= ofs0) ->
          Mem.load ch me b0 ofs0 = Mem.load ch mr b0 ofs0) /\
        (forall b0 ofs0 kd p, Mem.perm mb b0 ofs0 kd p -> Mem.perm me b0 ofs0 kd p)).
      exists (inr (from_hash256 RES)).
      destruct (exec_elements_indexed_rest_flag _t'3 _t'9 _t'10
        ltac:(repeat split; discriminate) ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
        e le _numInputs 696 eis_then eiu_else mc mr mb be ebase bt txbase bl bd dbase r nI RPost)
        as (le1 & me & HEx & HPost).
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + exact Hread.
      + exact He0.
      + lia.
      + exact Ht0.
      + lia.
      + lia.
      + exact elements_elementsTransaction_numInputs.
      + exact HE0.
      + exact HE2.
      + rewrite Hb. exact Hwb1.
      + intros le' Hi' Hd' He' _.
        set (le2 := PTree.set _t'7 (Vptr bt (Ptrofs.repr txbase)) le').
        set (le3 := PTree.set _t'8 (Vptr bin (Ptrofs.repr inbase)) le2).
        set (le4 := PTree.set _issuance (Vptr bin (Ptrofs.repr iofs)) le3).
        assert (Hd4 : le4!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
        { unfold le4, le3, le2. rewrite !PTree.gso by discriminate. exact Hd'. }
        assert (Ho4 : le4!_issuance = Some (Vptr bin (Ptrofs.repr iofs)))
          by (unfold le4; apply PTree.gss).
        destruct (exec_eis_dispatch_finalize Hmodel bx bm ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne)
          e le4 mx bin iofs bA bT bZ bB o HAx ltac:(nd6)
          ltac:(intros b HB; cbn [In] in HB; destruct HB as [E|[E|[E|[E|[]]]]]; subst b;
            repeat split; ne)
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
          Ho4 ltac:(unfold iofs, ofs; lia) ltac:(unfold iofs, ofs; lia) ltac:(ne) ltac:(ne) HRepX)
          as (mp & m9 & vr & HDisp9 & HFin9 & HReg9 & HL9 & HP9 & HV9).
        { intros off HO. apply HPx, Pb. eapply Mem.perm_implies; [apply PA0, HO|constructor]. }
        { intros off HO. apply HPx, Pb. eapply Mem.perm_implies; [apply PT0, HO|constructor]. }
        { intros off HO. apply HPx, Pb. eapply Mem.perm_implies; [apply PZ0, HO|constructor]. }
        { intros off HO. apply HPx, Pb. eapply Mem.perm_implies; [apply PB0, HO|constructor]. }
        fold RES in HReg9.
        assert (K9 : forall ch b0 o0, Mem.valid_block m b0 -> Mem.load ch m9 b0 o0 = Mem.load ch mb b0 o0).
        { intros ch b0 o0 Hv. pose proof (FRh b0 Hv) as Nb.
          rewrite HL9; [apply Kx; exact Hv|apply HVx, Vb; exact Hv|ne|ne|ne|ne|ne|ne]. }
        assert (P9 : forall b0 o0 kd p, Mem.perm mb b0 o0 kd p -> Mem.perm m9 b0 o0 kd p).
        { intros b0 o0 kd p Hp. apply HP9.
          - eapply Mem.perm_valid_block. apply HPx, Hp.
          - apply HPx, Hp. }
        (* writeHash *)
        assert (HOut9 : write_frame_at m9 bd dbase bw outedge (cursor - 1) 256).
        { eapply write_frame_at_preserved; [| |exact HFb].
          - intros ch b0 o0 v0 Hb0 HL. rewrite K9; [exact HL|destruct Hb0; subst; assumption].
          - exact P9. }
        assert (HArr9 : uint32_array_at m9 bm 0 (hash256_reg RES)).
        { apply u32_of_nth. intros j Hj. rewrite (hash256_len RES) in Hj. apply HReg9. exact Hj. }
        destruct (eval_sha_writeHash m9 bm 0 bd dbase bw outedge (cursor - 1) (hash256_reg RES)
          (hash256_len RES) ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
          ltac:(ne) ltac:(ne) HArr9 HOut9)
          as (m10 & HWr & HCells & HPrefix & HFldE & HLoadsE & HPermE & HValE).
        assert (E2 : write_effect m9 m10 bd dbase bw outedge (cursor - 1) 256 (uint32_word_cells (hash256_reg RES)))
          by exact (conj HCells (conj HPrefix (conj HFldE (conj HLoadsE (conj HPermE HValE))))).
        destruct (write_cells_seq mr mb m9 m10 bd dbase bw outedge cursor 1 256 [Some true]
          (uint32_word_cells (hash256_reg RES)) eq_refl ltac:(lia) HFrameR E1'
          ltac:(intros ch o0; apply K9; exact Vw) E2) as (HC & HPf & HFl).
  
        set (lef := eis_payload_le o le4 bin iofs bZ).
        assert (Hdf : lef!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
        { unfold lef. rewrite eis_payload_le_dst. exact Hd4. }
        exists lef, m10. split.
        {
          unfold eis_then.
          eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := mb).
          { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mb).
            - apply exec_Sset.
              eapply eval_elements_field_value with (sid := _txEnv) (delta := 0) (chunk := Mptr).
              + reflexivity.
              + exact eiu_env_tx.
              + reflexivity.
              + apply eval_elements_deref_struct. exact He'.
              + rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact Hmb0].
            - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := mb).
              + apply exec_Sset.
                eapply eval_elements_field_value with (sid := _elementsTransaction) (delta := 0) (chunk := Mptr).
                * reflexivity.
                * exact elements_elementsTransaction_input.
                * reflexivity.
                * apply eval_elements_deref_struct. unfold le2. apply PTree.gss.
                * rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact Hmb1].
              + apply exec_Sset.
                eapply eval_Eaddrof.
                unfold iofs. rewrite <- (elements_ptr_add_repr ofs 256) by (unfold ofs; lia).
                eapply eval_elements_field_lvalue; [reflexivity|exact elements_sigInput_issuance|].
                eapply eval_Elvalue.
                * apply eval_Ederef. apply (eih_input_ptr e le3 mb _t'8 _i bin inbase r).
                  -- unfold le3. apply PTree.gss.
                  -- unfold le3, le2. rewrite !PTree.gso by discriminate. exact Hi'.
                  -- exact Hi0.
                  -- unfold ofs in *; lia.
                * apply deref_loc_copy; reflexivity. }
          eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := mx).
          { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := mi).
            - change le4 with (set_opttemp None Vundef le4) at 2.
              eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_init) Ptrofs.zero)
                (vargs := [Vptr br Ptrofs.zero; Vptr bm Ptrofs.zero]) (f := Internal jets.f_sha256_init).
              + reflexivity.
              + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact tap_init_symbol]|].
                apply deref_loc_reference; reflexivity.
              + eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
                eapply eval_Econs; [apply el_eval_local_mid_s; reflexivity|reflexivity|apply eval_Enil].
              + exact tap_init_funct.
              + reflexivity.
              + exact HInit.
            - eapply (exec_ctx_struct_copy e le4 mi mx _ctx __res bx br ibytes);
                [reflexivity|reflexivity|ne|exact HLBi|exact HSBi]. }
  
          eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := lef) (m1 := mp).
          { exact HDisp9. }
          eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := lef) (m1 := m9).
          { eapply mt_call_finalize; [reflexivity|reflexivity|exact HFin9]. }
          change lef with (set_opttemp None Vundef lef) at 2.
          eapply exec_Scall with (vf := Vptr (sha_symbol_block _writeHash) Ptrofs.zero)
            (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bm Ptrofs.zero]) (f := Internal f_writeHash).
          - reflexivity.
          - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact hio_writeHash_symbol]|].
            apply deref_loc_reference; reflexivity.
          - eapply eval_Econs; [apply eval_Etempvar; exact Hdf|reflexivity|].
            eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
          - exact hio_writeHash_funct.
          - reflexivity.
          - exact HWr. }
        unfold RPost.
        split.
        { rewrite eiu_encode_some, <- uint32_cells_from_hash256. exact HC. }
        split; [exact HPf|]. split; [exact HFl|]. split.
        * intros ch b0 o0 Hv Hd Hw. pose proof (FRh b0 Hv) as Nb.
          rewrite HLoadsE.
          -- rewrite K9 by exact Hv. apply L1; [exact Hd|].
             destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw| |right; right; exact Hw].
             right; left.
             pose proof (Z.div_le_mono (cursor - 257) (cursor - 1) 64 ltac:(lia) ltac:(lia)). lia.
          -- exact Hd.
          -- destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw|right; left|right; right].
             ++ replace (cursor - 1 - 256) with (cursor - 257) by lia. exact Hw.
             ++ unfold write_word_address in *.
                pose proof (Z.div_le_mono (cursor - 1 - 1) (cursor - 1) 64 ltac:(lia) ltac:(lia)). lia.
        * intros b0 o0 kd p Hp. apply HPermE, P9, Hp.

      + intros le' _ _ _ Hbf. rewrite Hb in Hbf. discriminate Hbf.
      + exists le1, me. split; [exact HSpec|]. split; [exact HEx|exact HPost].
    - (* out of range *)
      assert (Hge : nn <= Int64.unsigned r).
      { unfold Int64.ltu in Hb.
        destruct (zlt (Int64.unsigned r) (Int64.unsigned nI)) as [Hl|Hnl]; [discriminate|].
        rewrite HnI in Hnl. lia. }
      assert (Hnth : nth_error outs (Z.to_nat (Int64.unsigned r)) = None).
      { apply nth_error_None. unfold nn in Hge. lia. }
      assert (HSpec : specv = Some (inl tt)).
      { unfold specv. rewrite elements_single_issuance_hash_sem.
        unfold elements_single_issuance_result. fold outs. rewrite <- Hr5, Hnth. reflexivity. }
      destruct (elements_skipBits_step mb bd dbase bw outedge (cursor - 1) 256 HFb) as (me & HCallS & E2).
      change (Z.of_nat 256) with 256 in HCallS, E2.
      pose proof (write_effect_seq mr mb me bd dbase bw outedge cursor 1 256 [Some false]
        (repeat None 256) eq_refl ltac:(lia) HFrameR E1' E2) as (HC & HPf & HFl & HLs & HPs & HVs).
      exists (inl tt).
      destruct (exec_elements_indexed_rest_flag _t'3 _t'9 _t'10
        ltac:(repeat split; discriminate) ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
        e le _numInputs 696 eis_then eiu_else mc mr mb be ebase bt txbase bl bd dbase r nI
        (fun me' => me' = me)) as (le1 & me' & HEx & HPost).
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + exact Hread.
      + exact He0.
      + lia.
      + exact Ht0.
      + lia.
      + lia.
      + exact elements_elementsTransaction_numInputs.
      + exact HE0.
      + exact HE2.
      + rewrite Hb. exact Hwb1.
      + intros le' _ _ _ Hbf. rewrite Hb in Hbf. discriminate Hbf.
      + intros le' Hi' Hd' He' _. exists le', me. split; [|reflexivity].
        unfold eiu_else.
        assert (Hargs : eval_exprlist sha_ge e le' mb
          [Etempvar _dst FRP; Econst_int (Int.repr 256) tint]
          (Tcons FRP (Tcons tulong Tnil))
          [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr 256)]).
        { eapply eval_Econs; [apply eval_Etempvar; exact Hd'|reflexivity|].
          eapply eval_Econs; [apply eval_Econst_int|apply eiu_cast256|apply eval_Enil]. }
        exact (exec_elements_helper_call e le' mb None _skipBits jets.f_skipBits
          _ _ _ _ _ _ me eiu_in_skipBits ltac:(reflexivity) Hargs ltac:(reflexivity) HCallS).
      + subst me'. exists le1, me. split; [exact HSpec|]. split; [exact HEx|].
        split; [rewrite eiu_encode_none; exact HC|].
        split; [exact HPf|]. split; [exact HFl|]. split.
        * intros ch b0 o0 Hv Hd Hw. apply HLs; assumption.
        * intros b0 o0 kd p Hp. destruct E2 as (_ & _ & _ & _ & Pm2 & _). apply Pm2, Hp. }
  destruct HTotal as (V & le1 & me & HSpec & HEx & HCells & HPrefix & HFields & HLoads & HPerm).
  (* freeing the locals *)
  destruct (free_list_blocks [(bx, 0, 88); (bl, 0, 16); (bm, 0, 32); (bZ, 0, 40); (bT, 0, 36); (bB, 0, 32); (bA, 0, 36); (br, 0, 88)] me)
    as (mf & HFL & HLf & _ & _).
  { intros b0 lo hi HIn ofs Hr1. apply HPerm, Pm1, Pr. cbn [In] in HIn.
    destruct HIn as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <- <-;
      [apply PX0|apply PL0|apply PM0|apply PZ0|apply PT0|apply PB0|apply PA0|apply PR0]; exact Hr1. }
  { clear -N1 N2 N3 N4 N5 N6 N7. cbn [map fst]. nd6. }
  cbn [map fst] in HLf.
  assert (HNl : forall b0, Mem.valid_block m b0 -> ~ In b0 [bx; bl; bm; bZ; bT; bB; bA; br]).
  { intros b0 Hb0 HIn. apply (FRh b0 Hb0). cbn [In] in HIn |- *. tauto. }
  exists mf, V. split; [exact HSpec|]. split; [|split; [|split; [|split]]].
  - eapply eval_funcall_internal with (e := e) (le1 := le) (m1 := m0) (le2 := le1) (m2 := me)
      (out := elements_returned_one).
    + eapply eis_entry; eassumption.
    + rewrite eis_body. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HCopy|exact HEx].
    + cbn. split; [discriminate|reflexivity].
    + unfold e. rewrite eis_blocks. exact HFL.
  - eapply frame_output_cells_preserved; [|exact HCells].
    intros ofs w HL. rewrite HLf by (apply HNl; exact Vw). exact HL.
  - eapply write_prefix_at_preserved; [| |exact HPrefix].
    + intros ofs w HL. rewrite Kr by exact Vw. exact HL.
    + intros ofs w HL. rewrite HLf by (apply HNl; exact Vw). exact HL.
  - destruct HFields as [HE1' HE2']. split; rewrite HLf by (apply HNl; exact Vd); assumption.
  - intros ch b0 ofs Hv Hd Hw. rewrite HLf by (apply HNl; exact Hv).
    rewrite HLoads by assumption. apply Kr; exact Hv.
Qed.
