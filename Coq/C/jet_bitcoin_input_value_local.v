(** Actual Bitcoin input_value jet against the literal canonical primitive
    InputValue.  The index is read from the source frame, the bounds test is
    written with writeBit, and the 64-bit amount or 64 padding cells follow;
    all environment loads are separated from the output by the footprint. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jet_frame_copy C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_input_layout.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec C.jet_exec.
Require C.jets.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_effects C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_read_step C.jet_bitcoin_steps.
Require Import C.jet_bitcoin_index_eval C.jet_bitcoin_indexed_exec C.jet_bitcoin_indexed_then.
Require Import C.jet_output_layout_step C.jet_bitcoin_env_load C.jet_bitcoin_input_value_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge ge0.
Set Default Timeout 60.

Definition bitcoin_input_value_elem : expr :=
  Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _sigInput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr).

Definition bitcoin_input_value_expr : expr :=
  Efield (Efield bitcoin_input_value_elem _txo (Tstruct _sigOutput noattr)) _value tulong.

Definition bitcoin_input_value_then : statement :=
  bitcoin_indexed_then _t'3 _t'4 _t'5 _input _sigInput bitcoin_input_value_expr _simplicity_write64.

Definition bitcoin_input_value_else : statement :=
  Scall None
    (Evar _skipBits (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 64) tint].

Definition bitcoin_input_value_rest : statement :=
  bitcoin_indexed_rest _t'6 _t'7 _numInputs bitcoin_input_value_then bitcoin_input_value_else.

Lemma bitcoin_input_value_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_input_value bitcoin_input_value_rest.
Proof.
  repeat split; try reflexivity.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Lemma eval_bitcoin_input_value_expr e le m r bin inbase v :
  le!_t'4 = Some (Vptr bin (Ptrofs.repr inbase)) -> le!_i = Some (Vlong r) ->
  0 <= inbase -> inbase + 160 * Int64.unsigned r + 112 <= Ptrofs.max_unsigned ->
  Mem.load Mint64 m bin (inbase + 160 * Int64.unsigned r + 104) = Some (Vlong v) ->
  eval_expr bitcoin_ge e le m bitcoin_input_value_expr (Vlong v).
Proof.
  intros H4 HI HB HM HL. unfold bitcoin_input_value_expr, bitcoin_input_value_elem.
  assert (HR : 0 <= Int64.unsigned r) by (apply Int64.unsigned_range).
  assert (HI' : le!_i = Some (Vlong (Int64.repr (Int64.unsigned r)))) by (rewrite Int64.repr_unsigned; exact HI).
  pose proof (eval_bitcoin_index e le m _t'4 _i _sigInput 160 bin inbase (Int64.unsigned r)
    bitcoin_sizeof_sigInput H4 HI' HB ltac:(lia) HR ltac:(lia)) as HElem.
  eapply eval_bitcoin_field_value with (sid := _sigOutput) (delta := 0) (chunk := Mint64).
  - reflexivity.
  - exact bitcoin_sigOutput_value.
  - reflexivity.
  - eapply eval_bitcoin_field_struct; [reflexivity|exact bitcoin_sigInput_txo|exact HElem].
  - rewrite bitcoin_ptr_add_repr by lia. rewrite bitcoin_ptr_add_repr by lia.
    apply bitcoin_loadv_repr; [lia|].
    replace (inbase + 160 * Int64.unsigned r + 104 + 0) with (inbase + 160 * Int64.unsigned r + 104) by lia.
    exact HL.
Qed.

Lemma bitcoin_input_value_mid environment m bd dbase bs sbase bi bw edge outedge cursor read_cursor
    (a : Ty.tySem Word32) be ebase bt txbase bin inbase nI bytes :
  0 <= ebase -> ebase + 56 <= Ptrofs.max_unsigned ->
  0 <= txbase -> txbase + 488 <= Ptrofs.max_unsigned ->
  0 <= inbase ->
  inbase + 160 * Z.of_nat (length (sigTxIn (Bitcoin.envTx environment))) <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mptr m bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)) ->
  Mem.load Mint64 m bt (txbase + 448) = Some (Vlong nI) ->
  Int64.unsigned nI = Z.of_nat (length (sigTxIn (Bitcoin.envTx environment))) ->
  (forall j txi, nth_error (sigTxIn (Bitcoin.envTx environment)) j = Some txi ->
    Mem.load Mint64 m bin (inbase + 160 * Z.of_nat j + 104) = Some (Vlong (sigTxiValue txi))) ->
  out_sep bd dbase bw outedge cursor 65 be ebase (ebase + 8) ->
  out_sep bd dbase bw outedge cursor 65 bt txbase (txbase + 8) ->
  out_sep bd dbase bw outedge cursor 65 bt (txbase + 448) (txbase + 456) ->
  out_sep bd dbase bw outedge cursor 65 bin inbase
    (inbase + 160 * Z.of_nat (length (sigTxIn (Bitcoin.envTx environment)))) ->
  frame_fields_at m bs sbase bi edge read_cursor ->
  0 <= read_cursor <= Int64.max_unsigned - 32 ->
  frame_input_word_at m bi edge read_cursor a ->
  write_frame_at m bd dbase bw outedge cursor 65 ->
  Mem.loadbytes m bs sbase 16 = Some bytes ->
  bitcoin_wrapper_mid f_simplicity_bitcoin_input_value bitcoin_input_value_rest
    (encode (bitcoin_input_value_result environment a)) (Vptr be (Ptrofs.repr ebase))
    m bd dbase bs sbase bw outedge cursor 65 bytes.
Proof.
  intros He0 He1 Ht0 Ht1 Hi0 Hi1 HLtx HLin HLn HnI HLelem S1 S2 S3 S4 HRF HRC HIn HFrame HBytes.
  unfold bitcoin_wrapper_mid. intros ma mc bl HAlloc HStore HLP HPP HFrameC.
  set (tx := Bitcoin.envTx environment) in *.
  set (nn := Z.of_nat (length (sigTxIn tx))) in *.
  assert (HVs : Mem.valid_block m bs).
  { eapply Mem.perm_valid_block. eapply (Mem.loadbytes_range_perm _ _ _ _ _ HBytes sbase); lia. }
  assert (HBa : Mem.loadbytes ma bs sbase 16 = Some bytes).
  { erewrite Mem.loadbytes_alloc_unchanged; eauto. }
  destruct (bitcoin_read_wide_step W32 m ma mc bl bs sbase bi edge read_cursor a bytes HRC HRF HIn
    HAlloc HBa HStore) as (mr & r & Hread & Hr & HRFields & HRMem & HRPerm & HRValid & HRLoads).
  pose proof HFrame as [HDB [[HDE HDO] [HEd [HN [HMx [HDW [PD HWords]]]]]]].
  destruct (write_frame_at_head m bd dbase bw outedge cursor 65 ltac:(lia) HFrame)
    as [_ [_ [_ [w0 Hw0]]]].
  assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
  assert (HFrameR : write_frame_at mr bd dbase bw outedge cursor 65).
  { eapply write_frame_at_preserved with (m := mc).
    - intros chunk b ofs v Hb HL. rewrite HRMem; [exact HL|].
      destruct Hb; subst; auto.
    - exact HRPerm.
    - exact HFrameC. }
  set (nn' := nn) in *.
  assert (HE0 : Mem.load Mptr mr be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase))) by (apply HRLoads; exact HLtx).
  assert (HE1 : Mem.load Mptr mr bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase))) by (apply HRLoads; exact HLin).
  assert (HE2 : Mem.load Mint64 mr bt (txbase + 448) = Some (Vlong nI)) by (apply HRLoads; exact HLn).
  assert (HF1 : write_frame_at mr bd dbase bw outedge cursor 1).
  { eapply write_frame_at_shorter; [|exact HFrameR]. lia. }
  destruct (bitcoin_writeBit_step mr bd dbase bw outedge cursor (Int64.ltu r nI) HF1)
    as (mb & Hwb & E1).
  assert (HF65 : write_frame_at mr bd dbase bw outedge cursor (1 + 64)) by exact HFrameR.
  assert (HFb : write_frame_at mb bd dbase bw outedge (cursor - 1) 64).
  { eapply write_frame_at_after_effect with (cells := [Some (Int64.ltu r nI)]);
      [reflexivity|lia|exact HF65|exact E1]. }
  assert (HLoadB : forall chunk b lo hi ofs, out_sep bd dbase bw outedge cursor 65 b lo hi ->
    lo <= ofs -> ofs + size_chunk chunk <= hi -> Mem.load chunk mb b ofs = Mem.load chunk mr b ofs).
  { intros chunk b lo hi ofs Hs Hlo Hhi.
    eapply write_effect_env_load with (bf := bd) (base := dbase) (bw := bw) (edge := outedge)
      (cursor := cursor) (cursor0 := cursor) (count0 := 65) (n := 1)
      (cells := [Some (Int64.ltu r nI)]) (lo := lo) (hi := hi);
      [lia|lia|lia|lia|exact E1|exact Hs|exact Hlo|exact Hhi]. }
  assert (Hidx : Int64.unsigned r = toZ a) by exact Hr.
  assert (Hr0 : 0 <= Int64.unsigned r) by apply Int64.unsigned_range.
  set (V := bitcoin_input_value_result environment a).
  assert (HTotal : exists le1 me,
    Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl)
      (bitcoin_wrapper_temps f_simplicity_bitcoin_input_value (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase)
      mc bitcoin_input_value_rest E0 le1 me bitcoin_returned_one /\
    write_effect mr me bd dbase bw outedge cursor 65 (encode V)).
  { eapply exec_bitcoin_indexed_rest with (e := bitcoin_version_locals bl) (tp := _t'6) (cp := _t'7)
      (countfield := _numInputs) (cdelta := 448) (mr := mr) (mb := mb) (be := be) (ebase := ebase)
      (bt := bt) (txbase := txbase) (bl := bl) (bd := bd) (dbase := dbase) (r := r) (nI := nI).
    - repeat split; discriminate.
    - repeat split; discriminate.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold bitcoin_wrapper_temps. apply PTree.gss.
    - unfold bitcoin_wrapper_temps. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate. apply PTree.gss.
    - exact Hread.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact bitcoin_bitcoinTransaction_numInputs.
    - exact HE0.
    - exact HE2.
    - exact Hwb.
    - (* success branch *)
      intros le' Hi Hd He Hb.
      assert (Hlt : Int64.unsigned r < nn).
      { unfold Int64.ltu in Hb.
        destruct (zlt (Int64.unsigned r) (Int64.unsigned nI)) as [Hl|Hnl]; [|discriminate].
        rewrite HnI in Hl. exact Hl. }
      destruct (nth_error (sigTxIn tx) (Z.to_nat (Int64.unsigned r))) as [txi|] eqn:Hnth;
        [|apply nth_error_None in Hnth; subst nn; lia].
      set (v := sigTxiValue txi).
      assert (HLv : Mem.load Mint64 mb bin (inbase + 160 * Int64.unsigned r + 104) = Some (Vlong v)).
      { rewrite (HLoadB Mint64 bin inbase (inbase + 160 * nn) (inbase + 160 * Int64.unsigned r + 104)
          S4 ltac:(lia) ltac:(change (size_chunk Mint64) with 8; lia)).
        apply HRLoads. pose proof (HLelem _ _ Hnth) as H.
        rewrite Z2Nat.id in H by lia. exact H. }
      assert (Hmb0 : Mem.load Mptr mb be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase))).
      { rewrite (HLoadB Mptr be ebase (ebase + 8) (ebase + 0) S1 ltac:(lia) ltac:(change (size_chunk Mptr) with 8; lia)).
        exact HE0. }
      assert (Hmb1 : Mem.load Mptr mb bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase))).
      { rewrite (HLoadB Mptr bt txbase (txbase + 8) (txbase + 0) S2 ltac:(lia) ltac:(change (size_chunk Mptr) with 8; lia)).
        exact HE1. }
      destruct (bitcoin_write_wide_step W64 mb bd dbase bw outedge (cursor - 1) v HFb)
        as (me & HCallW & E2).
      destruct (exec_bitcoin_indexed_then (bitcoin_version_locals bl) le' _t'3 _t'4 _t'5 _input 0 _sigInput
        bitcoin_input_value_expr _simplicity_write64 jets.f_simplicity_write64 mb me be ebase bt txbase bin inbase
        bd dbase r v ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(helper_in) ltac:(reflexivity) ltac:(reflexivity) He Hd Hi
        He0 ltac:(lia) Ht0 ltac:(lia) ltac:(lia) bitcoin_bitcoinTransaction_input Hmb0 Hmb1
        (fun le'' H4 HI' => eval_bitcoin_input_value_expr (bitcoin_version_locals bl) le'' mb r bin inbase v
          H4 HI' Hi0 ltac:(lia) HLv) HCallW) as [le'' HExec].
      exists le'', me. split; [exact HExec|].
      pose proof (write_effect_seq mr mb me bd dbase bw outedge cursor 1 64 [Some (Int64.ltu r nI)]
        (encode (decode_wide W64 (Int64.zero_ext (wide_bits W64) v))) eq_refl ltac:(lia) HF65 E1 E2) as Eseq.
      assert (Hcells : [Some (Int64.ltu r nI)] ++ encode (decode_wide W64 (Int64.zero_ext (wide_bits W64) v)) =
        encode V).
      { unfold V, bitcoin_input_value_result. rewrite <- Hidx. fold tx. rewrite Hnth. rewrite Hb.
        change (wide_bits W64) with 64. rewrite encode_sum_inr_word64.
        rewrite (decode_wide64_money v); [reflexivity|].
        pose proof (sigTxiValue_bound txi) as HB0. unfold MAX_MONEY in HB0. subst v. lia. }
      exact (eq_rect _ (fun c => write_effect mr me bd dbase bw outedge cursor (1 + 64) c) Eseq _ Hcells).
    - (* failure branch *)
      intros le' Hi Hd He Hb.
      assert (Hge : nn <= Int64.unsigned r).
      { unfold Int64.ltu in Hb.
        destruct (zlt (Int64.unsigned r) (Int64.unsigned nI)) as [Hl|Hnl]; [discriminate|].
        rewrite HnI in Hnl. lia. }
      assert (Hnth : nth_error (sigTxIn tx) (Z.to_nat (Int64.unsigned r)) = None).
      { apply nth_error_None. subst nn. lia. }
      assert (HFb' : write_frame_at mb bd dbase bw outedge (cursor - 1) (Z.of_nat 64)) by exact HFb.
      destruct (bitcoin_skipBits_step mb bd dbase bw outedge (cursor - 1) 64 HFb') as (me & HCallS & E2).
      exists le', me. split.
      + unfold bitcoin_input_value_else.
        assert (Hargs : eval_exprlist bitcoin_ge (bitcoin_version_locals bl) le' mb
          [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 64) tint]
          (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil))
          [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr 64)]).
        { eapply eval_Econs; [apply eval_Etempvar; exact Hd|reflexivity|].
          eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil]. }
        exact (exec_bitcoin_helper_call (bitcoin_version_locals bl) le' mb None _skipBits jets.f_skipBits
          _ _ _ _ _ _ me ltac:(helper_in) ltac:(reflexivity) Hargs ltac:(reflexivity) HCallS).
      + pose proof (write_effect_seq mr mb me bd dbase bw outedge cursor 1 64 [Some (Int64.ltu r nI)]
          (repeat None 64) eq_refl ltac:(lia) HF65 E1 E2) as Eseq.
        assert (Hcells : [Some (Int64.ltu r nI)] ++ repeat None 64 = encode V).
        { unfold V, bitcoin_input_value_result. rewrite <- Hidx. fold tx. rewrite Hnth. rewrite Hb.
          vm_compute. reflexivity. }
        exact (eq_rect _ (fun c => write_effect mr me bd dbase bw outedge cursor (1 + 64) c) Eseq _ Hcells). }
  destruct HTotal as (le1 & me & HEx & HEff).
  destruct (write_effect_lift mc mr me bl bd dbase bw outedge cursor 65 (encode V) HLd HLw
    HRMem HRPerm HRValid HEff) as (c & p & f & l & pm & vv).
  exists le1, me. refine (conj HEx (conj c (conj p (conj f (conj l (conj pm vv)))))).
Qed.

Definition bitcoin_input_value_env_rep (m : mem) (env : val) (environment : Bitcoin.env)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt txbase bin inbase nI,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    0 <= txbase /\ txbase + 488 <= Ptrofs.max_unsigned /\
    0 <= inbase /\
    inbase + 160 * Z.of_nat (length (sigTxIn (Bitcoin.envTx environment))) <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) /\
    Mem.load Mptr m bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)) /\
    Mem.load Mint64 m bt (txbase + 448) = Some (Vlong nI) /\
    Int64.unsigned nI = Z.of_nat (length (sigTxIn (Bitcoin.envTx environment))) /\
    (forall j txi, nth_error (sigTxIn (Bitcoin.envTx environment)) j = Some txi ->
      Mem.load Mint64 m bin (inbase + 160 * Z.of_nat j + 104) = Some (Vlong (sigTxiValue txi))) /\
    fp = [(be, ebase, ebase + 8); (bt, txbase, txbase + 8); (bt, txbase + 448, txbase + 456);
          (bin, inbase, inbase + 160 * Z.of_nat (length (sigTxIn (Bitcoin.envTx environment))))].

Theorem bitcoin_input_value_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_value bitcoin_ge Bitcoin.env
    Word32 (Ty.Sum Ty.Unit Word64) bitcoin_input_value_env_rep
    (fun a environment => @bitcoin_input_value_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor a fp
    (be & ebase & bt & txbase & bin & inbase & nI & HEnvVal & He0 & He1 & Ht0 & Ht1 & Hi0 & Hi1 &
      HLtx & HLin & HLn & HnI & HLelem & HFp)
    HSep HB HA [HSedge HSoff] HR0 HRmax Hin HFrame.
  subst env fp.
  assert (HC : Z.of_nat (bitSize (Ty.Sum Ty.Unit Word64)) = 65) by reflexivity.
  assert (HCA : Z.of_nat (bitSize Word32) = 32) by reflexivity.
  rewrite HC in HSep, HFrame. rewrite HCA in HRmax.
  rewrite Forall_forall in HSep.
  assert (S1 : out_sep bd dbase bw outedge cursor 65 be ebase (ebase + 8))
    by exact (HSep (be, ebase, ebase + 8) ltac:(simpl; auto)).
  assert (S2 : out_sep bd dbase bw outedge cursor 65 bt txbase (txbase + 8))
    by exact (HSep (bt, txbase, txbase + 8) ltac:(simpl; auto)).
  assert (S3 : out_sep bd dbase bw outedge cursor 65 bt (txbase + 448) (txbase + 456))
    by exact (HSep (bt, txbase + 448, txbase + 456) ltac:(simpl; auto)).
  assert (S4 : out_sep bd dbase bw outedge cursor 65 bin inbase
    (inbase + 160 * Z.of_nat (length (sigTxIn (Bitcoin.envTx environment)))))
    by exact (HSep (bin, inbase, inbase + 160 * Z.of_nat (length (sigTxIn (Bitcoin.envTx environment))))
      ltac:(simpl; auto)).
  apply frame_input_word_at_encode in Hin.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  destruct (bitcoin_wrapper_layout f_simplicity_bitcoin_input_value bitcoin_input_value_rest
    (encode (bitcoin_input_value_result environment a)) (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw
    outedge cursor 65 bytes bitcoin_input_value_shape HB HA HBytes ltac:(lia) HFrame
    (bitcoin_input_value_mid environment m bd dbase bs sbase bi bw edge outedge cursor read_cursor a
      be ebase bt txbase bin inbase nI bytes He0 He1 Ht0 Ht1 Hi0 Hi1 HLtx HLin HLn HnI HLelem
      S1 S2 S3 S4 (conj HSedge HSoff) ltac:(lia) Hin HFrame HBytes))
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (bitcoin_input_value_result environment a). split.
  - apply bitcoin_input_value_spec_sem.
  - split; [exact HCall|]. split; [exact HCells|]. split; [exact HPrefix|].
    rewrite HC. split; [exact HFields|]. exact HMem.
Qed.
