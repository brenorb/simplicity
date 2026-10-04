(** Actual Bitcoin input_annex_hash jet against the extended primitive
    InputAnnexHash.
    C: [i = simplicity_read32(&src);
        if (writeBit(dst, i < env->tx->numInputs)) {
          if (writeBit(dst, env->tx->input[i].hasAnnex)) writeHash(dst, &env->tx->input[i].annexHash);
          else skipBits(dst, 256);
        } else skipBits(dst, 257);
        return true;] *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jet_frame_copy C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_input_layout C.jet_output_layout_step.
Require Import C.jet_uint32_array_init C.jet_word_repr.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec C.jet_exec.
Require C.jets.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_effects C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_read_step C.jet_bitcoin_steps.
Require Import C.jet_bitcoin_index_eval C.jet_bitcoin_indexed_exec C.jet_bitcoin_indexed_ptr_then.
Require Import C.jet_bitcoin_env_load C.jet_bitcoin_indexed_scalar C.jet_bitcoin_indexed_ptr.
Require Import C.jet_bitcoin_current_exec.
Require Import C.jet_bitcoin_hash_write C.jet_bitcoin_hash_getters C.jet_bitcoin_script_cmr_local.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_ext_ptr_jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Import PrimitiveBitcoinExt.Primitive.Coercions.
Import PrimitiveBitcoinExt.Primitive.CanonicalStructures.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge ge0.
Set Default Timeout 120.

Definition bit_int (b : bool) : int := if b then Int.one else Int.zero.

Definition is_some {A} (o : option A) : bool := match o with Some _ => true | None => false end.

Lemma bitcoin_sigInput_annexHash : bitcoin_field_at _sigInput _annexHash 0.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_sigInput_hasAnnex : bitcoin_field_at _sigInput _hasAnnex 152.
Proof. vm_compute; reflexivity. Qed.

Definition annex_head : statement :=
  Ssequence
    (Scall (Some _t'1)
      (Evar _simplicity_read32 (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil) tulong cc_default))
      [Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))])
    (Sset _i (Etempvar _t'1 tulong)).

Definition writeBit_type : type :=
  Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default.

Definition annex_cond : statement :=
  Ssequence (Sset _t'9 bitcoin_env_tx_expr)
    (Ssequence
      (Sset _t'10 (Efield (Ederef (Etempvar _t'9 (tptr (Tstruct _bitcoinTransaction noattr)))
        (Tstruct _bitcoinTransaction noattr)) _numInputs tulong))
      (Scall (Some _t'3) (Evar _writeBit writeBit_type)
        [Etempvar _dst (tptr (Tstruct _frameItem noattr));
         Ebinop Olt (Etempvar _i tulong) (Etempvar _t'10 tulong) tint])).

Definition annex_elem (t : ident) : expr :=
  Ederef (Ebinop Oadd (Etempvar t (tptr (Tstruct _sigInput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr).

Definition annex_inner_cond : statement :=
  Ssequence (Sset _t'6 bitcoin_env_tx_expr)
    (Ssequence
      (Sset _t'7 (Efield (Ederef (Etempvar _t'6 (tptr (Tstruct _bitcoinTransaction noattr)))
        (Tstruct _bitcoinTransaction noattr)) _input (tptr (Tstruct _sigInput noattr))))
      (Ssequence
        (Sset _t'8 (Efield (annex_elem _t'7) _hasAnnex tbool))
        (Scall (Some _t'2) (Evar _writeBit writeBit_type)
          [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _t'8 tbool]))).

Definition annex_pexpr : expr :=
  Eaddrof (Efield (annex_elem _t'5) _annexHash (Tstruct _sha256_midstate noattr))
    (tptr (Tstruct _sha256_midstate noattr)).

Definition annex_then : statement :=
  Ssequence annex_inner_cond
    (Sifthenelse (Etempvar _t'2 tbool)
      (bitcoin_indexed_then_ptr _t'4 _t'5 _input _sigInput annex_pexpr _writeHash
        (Tstruct _sha256_midstate noattr))
      (bitcoin_skip_stmt 256)).

Definition annex_rest : statement :=
  Ssequence annex_head
    (Ssequence
      (Ssequence annex_cond (Sifthenelse (Etempvar _t'3 tbool) annex_then (bitcoin_skip_stmt 257)))
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))).

Lemma bitcoin_input_annex_hash_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_input_annex_hash annex_rest.
Proof.
  repeat split; try reflexivity.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Definition annex_elem_rep (m : mem) (b : block) (ofs : Z) (o : option hash256) : Prop :=
  Mem.load Mint8unsigned m b (ofs + 152) = Some (Vint (bit_int (is_some o))) /\
  forall h, o = Some h -> hash_elem_rep m b ofs h.

Definition annex_cells (annexes : list (option hash256)) (a : Ty.tySem Word32) : list Cell :=
  match nth_error annexes (Z.to_nat (toZ a)) with
  | None => Some false :: repeat None 257
  | Some None => Some true :: Some false :: repeat None 256
  | Some (Some h) => Some true :: Some true :: hash_cells (hash256_reg h)
  end.

Definition bitcoin_input_annex_hash_env_rep (m : mem) (env : val) (e : ext_environment)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt txbase bin inbase nI,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    0 <= txbase /\ txbase + 488 <= Ptrofs.max_unsigned /\
    0 <= inbase /\ inbase + 160 * Z.of_nat (length (extInAnnexHash e)) <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) /\
    Mem.load Mptr m bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)) /\
    Mem.load Mint64 m bt (txbase + 448) = Some (Vlong nI) /\
    Int64.unsigned nI = Z.of_nat (length (extInAnnexHash e)) /\
    (forall j o, nth_error (extInAnnexHash e) j = Some o ->
      annex_elem_rep m bin (inbase + 160 * Z.of_nat j) o) /\
    fp = [(be, ebase, ebase + 8); (bt, txbase + 0, txbase + 8);
          (bin, inbase, inbase + 160 * Z.of_nat (length (extInAnnexHash e)))].

Definition bitcoin_input_annex_hash_spec {alg : PrimitiveBitcoinExt.Primitive.Algebra} :
    alg Word32 (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256)) :=
  PrimitiveBitcoinExt.Primitive.Combinators.prim BitcoinExt.InputAnnexHash.

Definition bitcoin_annex_result (annexes : list (option hash256)) (a : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256)) :=
  match nth_error annexes (Z.to_nat (toZ a)) with
  | None => inl tt
  | Some None => inr (inl tt)
  | Some (Some h) => inr (inr (from_hash256 h))
  end.

Lemma bitcoin_input_annex_hash_sem environment a :
  @bitcoin_input_annex_hash_spec (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero)
    a environment = Some (bitcoin_annex_result (extInAnnexHash environment) a).
Proof. reflexivity. Qed.

Lemma encode_annex_result annexes a :
  encode (bitcoin_annex_result annexes a) = annex_cells annexes a.
Proof.
  unfold bitcoin_annex_result, annex_cells.
  destruct (nth_error annexes (Z.to_nat (toZ a))) as [ [h|] | ].
  - change (Some true :: Some true :: @encode Word256 (from_hash256 h) =
      Some true :: Some true :: hash_cells (hash256_reg h)).
    rewrite encode_from_hash256. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Lemma eval_annex_hasAnnex e le m t bin inbase r (v : int) :
  le!t = Some (Vptr bin (Ptrofs.repr inbase)) -> le!_i = Some (Vlong r) ->
  0 <= inbase -> inbase + 160 * Int64.unsigned r + 160 <= Ptrofs.max_unsigned ->
  Mem.load Mint8unsigned m bin (inbase + 160 * Int64.unsigned r + 152) = Some (Vint v) ->
  eval_expr bitcoin_ge e le m (Efield (annex_elem t) _hasAnnex tbool) (Vint v).
Proof.
  intros HT HI HB HM HL.
  assert (HR : 0 <= Int64.unsigned r) by (apply Int64.unsigned_range).
  assert (HI' : le!_i = Some (Vlong (Int64.repr (Int64.unsigned r))))
    by (rewrite Int64.repr_unsigned; exact HI).
  pose proof (eval_bitcoin_index e le m t _i _sigInput 160 bin inbase (Int64.unsigned r)
    bitcoin_sizeof_sigInput HT HI' HB ltac:(lia) HR ltac:(lia)) as HElem.
  eapply eval_bitcoin_field_value with (sid := _sigInput) (delta := 152) (chunk := Mint8unsigned).
  - reflexivity.
  - exact bitcoin_sigInput_hasAnnex.
  - reflexivity.
  - exact HElem.
  - rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact HL].
Qed.

Theorem bitcoin_input_annex_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_annex_hash bitcoin_ge ext_environment Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256)) bitcoin_input_annex_hash_env_rep
    (fun a environment => @bitcoin_input_annex_hash_spec
      (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor a fp
    (be & ebase & bt & txbase & bin & inbase & nI & HEnvVal & He0 & He1 & Ht0 & Ht1 & Hi0 & Hi1 &
      HLtx & HLin & HLn & HnI & HLelem & HFp)
    HSep HBf HA [HSedge HSoff] HR0 HRmax Hin HFrame.
  subst env fp.
  set (annexes := extInAnnexHash environment) in *.
  set (nn := Z.of_nat (length annexes)) in *.
  assert (HB : Z.of_nat (bitSize (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))) = 258) by reflexivity.
  rewrite HB in HSep, HFrame.
  change (Z.of_nat (bitSize Word32)) with 32 in HRmax.
  rewrite Forall_forall in HSep.
  assert (S1 : out_sep bd dbase bw outedge cursor 258 be ebase (ebase + 8))
    by exact (HSep (be, ebase, ebase + 8) ltac:(simpl; auto)).
  assert (S4 : out_sep bd dbase bw outedge cursor 258 bt (txbase + 0) (txbase + 8))
    by exact (HSep (bt, txbase + 0, txbase + 8) ltac:(simpl; auto)).
  assert (S5 : out_sep bd dbase bw outedge cursor 258 bin inbase (inbase + 160 * nn))
    by exact (HSep (bin, inbase, inbase + 160 * nn) ltac:(simpl; auto)).
  apply frame_input_word_at_encode in Hin.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  set (V := annex_cells annexes a).
  assert (HMid : bitcoin_wrapper_mid f_simplicity_bitcoin_input_annex_hash annex_rest V
    (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 258 bytes).
  { unfold bitcoin_wrapper_mid. intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    pose proof HFrame as [_ [_ [_ [HCnt0 _]]]].
    assert (HBa : Mem.loadbytes ma bs sbase 16 = Some bytes).
    { erewrite Mem.loadbytes_alloc_unchanged; eauto.
      eapply Mem.perm_valid_block. eapply (Mem.loadbytes_range_perm _ _ _ _ _ HBytes sbase); lia. }
    destruct (bitcoin_read_wide_step W32 m ma mc bl bs sbase bi edge read_cursor a bytes
      ltac:(change (wide_bits W32) with 32; lia) (conj HSedge HSoff) Hin HAlloc HBa HStore)
      as (mr & r & Hread & Hr & _ & HRMem & HRPerm & HRValid & HRLoads).
    assert (Hidx : Int64.unsigned r = toZ a) by exact Hr.
    assert (Hr0 : 0 <= Int64.unsigned r) by apply Int64.unsigned_range.
    assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto;
      destruct HFrame as [_ [[HDE _] _]]; exact HDE).
    assert (HLw : bl <> bw).
    { destruct (write_frame_at_head m bd dbase bw outedge cursor 258 ltac:(lia) HFrame)
        as [_ [_ [_ [w0 Hw0]]]]. eapply fresh_frame_not_loaded; eauto. }
    assert (HFrameR : write_frame_at mr bd dbase bw outedge cursor 258).
    { eapply write_frame_at_preserved with (m := mc).
      - intros chunk b0 ofs v Hb HL. rewrite HRMem; [exact HL|].
        destruct Hb; subst; auto.
      - exact HRPerm.
      - exact HFrameC. }
    assert (HE0 : Mem.load Mptr mr be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)))
      by (apply HRLoads; exact HLtx).
    assert (HE1 : Mem.load Mptr mr bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)))
      by (apply HRLoads; exact HLin).
    assert (HE2 : Mem.load Mint64 mr bt (txbase + 448) = Some (Vlong nI))
      by (apply HRLoads; exact HLn).
    set (b1 := Int64.ltu r nI).
    assert (HF1 : write_frame_at mr bd dbase bw outedge cursor 1).
    { eapply write_frame_at_shorter; [|exact HFrameR]. lia. }
    destruct (bitcoin_writeBit_step mr bd dbase bw outedge cursor b1 HF1) as (mb & Hwb1 & E1).
    assert (HFb : write_frame_at mb bd dbase bw outedge (cursor - 1) 257).
    { eapply write_frame_at_after_effect with (cells := [Some b1]);
        [reflexivity|lia|exact HFrameR|exact E1]. }
    assert (HLoadB : forall chunk b0 lo hi ofs, out_sep bd dbase bw outedge cursor 258 b0 lo hi ->
      lo <= ofs -> ofs + size_chunk chunk <= hi -> Mem.load chunk mb b0 ofs = Mem.load chunk mr b0 ofs).
    { intros chunk b0 lo hi ofs Hs Hlo Hhi.
      eapply write_effect_env_load with (bf := bd) (base := dbase) (bw := bw) (edge := outedge)
        (cursor := cursor) (cursor0 := cursor) (count0 := 258) (n := 1)
        (cells := [Some b1]) (lo := lo) (hi := hi);
        [lia|lia|lia|lia|exact E1|exact Hs|exact Hlo|exact Hhi]. }
    set (le0 := bitcoin_wrapper_temps f_simplicity_bitcoin_input_annex_hash (Vptr be (Ptrofs.repr ebase))
      bd dbase bs sbase).
    assert (HEnv0 : le0!_env = Some (Vptr be (Ptrofs.repr ebase)))
      by (unfold le0, bitcoin_wrapper_temps; apply PTree.gss).
    assert (HDst0 : le0!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
    { unfold le0, bitcoin_wrapper_temps. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. apply PTree.gss. }
    set (l1 := PTree.set _i (Vlong r) (PTree.set _t'1 (Vlong r) le0)).
    set (l2 := PTree.set _t'9 (Vptr bt (Ptrofs.repr txbase)) l1).
    set (l3 := PTree.set _t'10 (Vlong nI) l2).
    set (l4 := PTree.set _t'3 (Vint (bit_int b1)) l3).
    assert (Hi4 : l4!_i = Some (Vlong r)).
    { unfold l4, l3, l2, l1. repeat rewrite PTree.gso by discriminate. apply PTree.gss. }
    assert (Hd4 : l4!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
    { unfold l4, l3, l2, l1. repeat rewrite PTree.gso by discriminate. exact HDst0. }
    assert (He4 : l4!_env = Some (Vptr be (Ptrofs.repr ebase))).
    { unfold l4, l3, l2, l1. repeat rewrite PTree.gso by discriminate. exact HEnv0. }
    assert (HHead : Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl) le0 mc annex_head E0 l1 mr
      Out_normal).
    { unfold annex_head.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := PTree.set _t'1 (Vlong r) le0).
      - change (PTree.set _t'1 (Vlong r) le0) with (set_opttemp (Some _t'1) (Vlong r) le0).
        eapply exec_bitcoin_helper_call with (id := _simplicity_read32) (f := jets.f_simplicity_read32)
          (vargs := [Vptr bl Ptrofs.zero]) (vres := Vlong r).
        + unfold bitcoin_core_helpers. simpl. tauto.
        + reflexivity.
        + eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
        + reflexivity.
        + exact Hread.
      - apply exec_set. apply eval_Etempvar. apply PTree.gss. }
    assert (HCond : Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl) l1 mr annex_cond E0 l4 mb
      Out_normal).
    { unfold annex_cond.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l2).
      - apply exec_set. eapply eval_bitcoin_env_tx_expr; [|exact He0|lia|exact HE0].
        unfold l1. repeat rewrite PTree.gso by discriminate. exact HEnv0.
      - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l3).
        + apply exec_set.
          eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := 448) (chunk := Mint64).
          * reflexivity.
          * exact bitcoin_bitcoinTransaction_numInputs.
          * reflexivity.
          * apply eval_bitcoin_deref_struct. unfold l2. apply PTree.gss.
          * rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact HE2].
        + change l4 with (set_opttemp (Some _t'3) (Vint (bit_int b1)) l3).
          eapply exec_bitcoin_helper_call with (id := _writeBit) (f := jets.f_writeBit)
            (vargs := [Vptr bd (Ptrofs.repr dbase); Vint (bit_int b1)]) (vres := Vint (bit_int b1)).
          * unfold bitcoin_core_helpers. simpl. tauto.
          * reflexivity.
          * eapply eval_Econs.
            -- apply eval_Etempvar. unfold l3, l2, l1. repeat rewrite PTree.gso by discriminate. exact HDst0.
            -- reflexivity.
            -- eapply eval_Econs with (v1 := Val.of_bool b1).
               ++ eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vlong nI).
                  ** apply eval_Etempvar. unfold l3, l2. repeat rewrite PTree.gso by discriminate.
                     unfold l1. apply PTree.gss.
                  ** apply eval_Etempvar. unfold l3. apply PTree.gss.
                  ** apply bitcoin_ltu_cmp.
               ++ apply bitcoin_bool_cast.
               ++ apply eval_Enil.
          * reflexivity.
          * exact Hwb1. }
    assert (HBranch : exists le'' me,
      Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl) l4 mb
        (if b1 then annex_then else bitcoin_skip_stmt 257) E0 le'' me Out_normal /\
      write_effect mr me bd dbase bw outedge cursor 258 V).
    { destruct b1 eqn:Hb.
      - (* index in range *)
        assert (Hlt : Int64.unsigned r < nn).
        { unfold b1, Int64.ltu in Hb.
          destruct (zlt (Int64.unsigned r) (Int64.unsigned nI)) as [Hl|Hnl]; [|discriminate].
          rewrite HnI in Hl. exact Hl. }
        destruct (nth_error annexes (Z.to_nat (Int64.unsigned r))) as [o|] eqn:Hnth;
          [|apply nth_error_None in Hnth; subst nn; lia].
        set (eofs := inbase + 160 * Int64.unsigned r).
        assert (Hm : 160 * Int64.unsigned r + 160 <= 160 * nn) by lia.
        pose proof (HLelem _ _ Hnth) as HEl. rewrite Z2Nat.id in HEl by lia.
        destruct HEl as [Hflag Hhash].
        set (b2 := is_some o).
        assert (Hmb0 : Mem.load Mptr mb be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase))).
        { rewrite (HLoadB Mptr be ebase (ebase + 8) (ebase + 0) S1 ltac:(lia)
            ltac:(change (size_chunk Mptr) with 8; lia)). exact HE0. }
        assert (Hmb1 : Mem.load Mptr mb bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase))).
        { rewrite (HLoadB Mptr bt (txbase + 0) (txbase + 8) (txbase + 0) S4 ltac:(lia)
            ltac:(change (size_chunk Mptr) with 8; lia)). exact HE1. }
        assert (Hmbf : Mem.load Mint8unsigned mb bin (eofs + 152) = Some (Vint (bit_int b2))).
        { rewrite (HLoadB Mint8unsigned bin inbase (inbase + 160 * nn) (eofs + 152) S5
            ltac:(unfold eofs; lia) ltac:(change (size_chunk Mint8unsigned) with 1; unfold eofs; lia)).
          apply HRLoads. exact Hflag. }
        assert (HFb1 : write_frame_at mb bd dbase bw outedge (cursor - 1) 1).
        { eapply write_frame_at_shorter; [|exact HFb]. lia. }
        destruct (bitcoin_writeBit_step mb bd dbase bw outedge (cursor - 1) b2 HFb1) as (mb2 & Hwb2 & E2).
        assert (HFb2 : write_frame_at mb2 bd dbase bw outedge (cursor - 1 - 1) 256).
        { eapply write_frame_at_after_effect with (cells := [Some b2]);
            [reflexivity|lia|exact HFb|exact E2]. }
        assert (HLoadB2 : forall chunk b0 lo hi ofs, out_sep bd dbase bw outedge cursor 258 b0 lo hi ->
          lo <= ofs -> ofs + size_chunk chunk <= hi -> Mem.load chunk mb2 b0 ofs = Mem.load chunk mb b0 ofs).
        { intros chunk b0 lo hi ofs Hs Hlo Hhi.
          pose proof HFrameR as [_ [_ [_ [HCnt _]]]].
          eapply write_effect_env_load with (bf := bd) (base := dbase) (bw := bw) (edge := outedge)
            (cursor := cursor - 1) (cursor0 := cursor) (count0 := 258) (n := 1)
            (cells := [Some b2]) (lo := lo) (hi := hi);
            [lia|lia|lia|lia|exact E2|exact Hs|exact Hlo|exact Hhi]. }
        set (la := PTree.set _t'6 (Vptr bt (Ptrofs.repr txbase)) l4).
        set (lb := PTree.set _t'7 (Vptr bin (Ptrofs.repr inbase)) la).
        set (lc := PTree.set _t'8 (Vint (bit_int b2)) lb).
        set (ld := PTree.set _t'2 (Vint (bit_int b2)) lc).
        assert (Hid : ld!_i = Some (Vlong r)).
        { unfold ld, lc, lb, la. repeat rewrite PTree.gso by discriminate. exact Hi4. }
        assert (Hdd : ld!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
        { unfold ld, lc, lb, la. repeat rewrite PTree.gso by discriminate. exact Hd4. }
        assert (Hed : ld!_env = Some (Vptr be (Ptrofs.repr ebase))).
        { unfold ld, lc, lb, la. repeat rewrite PTree.gso by discriminate. exact He4. }
        assert (HInner : Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl) l4 mb annex_inner_cond
          E0 ld mb2 Out_normal).
        { unfold annex_inner_cond.
          eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := la).
          - apply exec_set. eapply eval_bitcoin_env_tx_expr; [exact He4|exact He0|lia|exact Hmb0].
          - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := lb).
            + apply exec_set.
              eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := 0) (chunk := Mptr).
              * reflexivity.
              * exact bitcoin_bitcoinTransaction_input.
              * reflexivity.
              * apply eval_bitcoin_deref_struct. unfold la. apply PTree.gss.
              * rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact Hmb1].
            + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := lc).
              * apply exec_set.
                eapply eval_annex_hasAnnex with (bin := bin) (inbase := inbase) (r := r).
                -- unfold lb. apply PTree.gss.
                -- unfold lb, la. repeat rewrite PTree.gso by discriminate. exact Hi4.
                -- exact Hi0.
                -- lia.
                -- exact Hmbf.
              * change ld with (set_opttemp (Some _t'2) (Vint (bit_int b2)) lc).
                eapply exec_bitcoin_helper_call with (id := _writeBit) (f := jets.f_writeBit)
                  (vargs := [Vptr bd (Ptrofs.repr dbase); Vint (bit_int b2)]) (vres := Vint (bit_int b2)).
                -- unfold bitcoin_core_helpers. simpl. tauto.
                -- reflexivity.
                -- eapply eval_Econs.
                   ++ apply eval_Etempvar. unfold lc, lb, la. repeat rewrite PTree.gso by discriminate.
                      exact Hd4.
                   ++ reflexivity.
                   ++ eapply eval_Econs with (v1 := Vint (bit_int b2)).
                      ** apply eval_Etempvar. unfold lc. apply PTree.gss.
                      ** destruct b2; reflexivity.
                      ** apply eval_Enil.
                -- reflexivity.
                -- exact Hwb2. }
        assert (HTail : exists le'' me,
          Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl) ld mb2
            (if b2 then bitcoin_indexed_then_ptr _t'4 _t'5 _input _sigInput annex_pexpr _writeHash
               (Tstruct _sha256_midstate noattr) else bitcoin_skip_stmt 256) E0 le'' me Out_normal /\
          write_effect mb me bd dbase bw outedge (cursor - 1) 257
            (match o with
             | Some h => Some true :: hash_cells (hash256_reg h)
             | None => Some false :: repeat None 256
             end)).
        { destruct o as [h|].
          - (* annex present *)
            change b2 with true in *.
            assert (Hrep : hash_elem_rep m bin eofs h) by (apply Hhash; reflexivity).
            assert (Hrep2 : hash_elem_rep mb2 bin eofs h).
            { eapply hash_elem_rep_mono; [exact Hrep|].
              intros chunk o0 v Hlo Hhi Hl.
              rewrite (HLoadB2 chunk bin inbase (inbase + 160 * nn) o0 S5 ltac:(unfold eofs in Hlo; lia)
                ltac:(unfold eofs in Hhi; lia)).
              rewrite (HLoadB chunk bin inbase (inbase + 160 * nn) o0 S5 ltac:(unfold eofs in Hlo; lia)
                ltac:(unfold eofs in Hhi; lia)).
              apply HRLoads. exact Hl. }
            assert (Hm20 : Mem.load Mptr mb2 be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase))).
            { rewrite (HLoadB2 Mptr be ebase (ebase + 8) (ebase + 0) S1 ltac:(lia)
                ltac:(change (size_chunk Mptr) with 8; lia)). exact Hmb0. }
            assert (Hm21 : Mem.load Mptr mb2 bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase))).
            { rewrite (HLoadB2 Mptr bt (txbase + 0) (txbase + 8) (txbase + 0) S4 ltac:(lia)
                ltac:(change (size_chunk Mptr) with 8; lia)). exact Hmb1. }
            assert (HSp : out_sep bd dbase bw outedge (cursor - 1 - 1) 256 bin eofs (eofs + 32)).
            { pose proof HFrameR as [_ [_ [_ [HCnt _]]]].
              eapply out_sep_range with (lo := inbase) (hi := inbase + 160 * nn);
                [|unfold eofs; lia|unfold eofs; lia].
              eapply out_sep_sub with (cursor := cursor) (count := 258); [lia|lia|lia|lia|exact S5]. }
            destruct (hash_elem_pay bd dbase bw outedge mb2 bin eofs h (cursor - 1 - 1) Hrep2
              ltac:(unfold eofs; lia) ltac:(unfold eofs; lia) HSp HFb2) as (me & HCallP & E3).
            destruct (exec_bitcoin_indexed_then_ptr (bitcoin_version_locals bl) ld _t'4 _t'5 _input 0
              _sigInput annex_pexpr _writeHash (Tstruct _sha256_midstate noattr) f_writeHash eofs
              mb2 me be ebase bt txbase bin inbase bd dbase r
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(reflexivity) ltac:(reflexivity) bitcoin_writeHash_symbol bitcoin_writeHash_funct
              ltac:(reflexivity) Hed Hdd Hid He0 ltac:(lia) Ht0 ltac:(lia) ltac:(lia)
              bitcoin_bitcoinTransaction_input Hm20 Hm21
              (fun le'' H4 HI' =>
                eq_rect _ (fun z => eval_expr bitcoin_ge (bitcoin_version_locals bl) le'' mb2 annex_pexpr
                    (Vptr bin (Ptrofs.repr z)))
                  (eval_bitcoin_elem_field_addr (bitcoin_version_locals bl) le'' mb2 _t'5 _i _sigInput 160
                    _annexHash 0 _sha256_midstate bin inbase r bitcoin_sizeof_sigInput
                    bitcoin_sigInput_annexHash H4 HI' Hi0 ltac:(split; lia) ltac:(lia) ltac:(lia) ltac:(lia))
                  eofs ltac:(unfold eofs; lia))
              HCallP) as [le'' HExec].
            exists le'', me. split; [exact HExec|].
            exact (write_effect_seq mb mb2 me bd dbase bw outedge (cursor - 1) 1 256 [Some true]
              (hash_cells (hash256_reg h)) eq_refl ltac:(lia) HFb E2 E3).
          - (* no annex *)
            change b2 with false in *.
            destruct (bitcoin_skipBits_step mb2 bd dbase bw outedge (cursor - 1 - 1) 256%nat HFb2)
              as (me & HCallS & E3).
            exists ld, me. split.
            + unfold bitcoin_skip_stmt.
              assert (Hargs : eval_exprlist bitcoin_ge (bitcoin_version_locals bl) ld mb2
                [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 256) tint]
                (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil))
                [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr (Z.of_nat 256))]).
              { eapply eval_Econs; [apply eval_Etempvar; exact Hdd|reflexivity|].
                eapply eval_Econs; [apply eval_Econst_int| |apply eval_Enil].
                apply bitcoin_cast_const'; lia. }
              exact (exec_bitcoin_helper_call (bitcoin_version_locals bl) ld mb2 None _skipBits jets.f_skipBits
                _ _ _ _ _ _ me ltac:(unfold bitcoin_core_helpers; simpl; tauto) ltac:(reflexivity) Hargs
                ltac:(reflexivity) HCallS).
            + exact (write_effect_seq mb mb2 me bd dbase bw outedge (cursor - 1) 1 256 [Some false]
                (repeat None 256) eq_refl ltac:(lia) HFb E2 E3). }
        destruct HTail as (lef & me & HT & EInner).
        exists lef, me. split.
        + unfold annex_then.
          eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb2) (le1 := ld); [exact HInner|].
          eapply exec_Sifthenelse with (v1 := Vint (bit_int b2)) (b := b2).
          * apply eval_Etempvar. unfold ld. apply PTree.gss.
          * destruct b2; reflexivity.
          * exact HT.
        + pose proof (write_effect_seq mr mb me bd dbase bw outedge cursor 1 257 [Some true] _
            eq_refl ltac:(lia) HFrameR E1 EInner) as Eseq.
          assert (Hcells : [Some true] ++
            (match o with
             | Some h => Some true :: hash_cells (hash256_reg h)
             | None => Some false :: repeat None 256
             end) = V).
          { unfold V, annex_cells. rewrite <- Hidx, Hnth. destruct o; reflexivity. }
          exact (eq_rect _ (fun c => write_effect mr me bd dbase bw outedge cursor 258 c) Eseq _ Hcells).
      - (* index out of range *)
        assert (Hge : nn <= Int64.unsigned r).
        { unfold b1, Int64.ltu in Hb.
          destruct (zlt (Int64.unsigned r) (Int64.unsigned nI)) as [Hl|Hnl]; [discriminate|].
          rewrite HnI in Hnl. lia. }
        assert (Hnth : nth_error annexes (Z.to_nat (Int64.unsigned r)) = None).
        { apply nth_error_None. subst nn. lia. }
        destruct (bitcoin_skipBits_step mb bd dbase bw outedge (cursor - 1) 257%nat HFb)
          as (me & HCallS & E2).
        exists l4, me. split.
        + unfold bitcoin_skip_stmt.
          assert (Hargs : eval_exprlist bitcoin_ge (bitcoin_version_locals bl) l4 mb
            [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 257) tint]
            (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil))
            [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr (Z.of_nat 257))]).
          { eapply eval_Econs; [apply eval_Etempvar; exact Hd4|reflexivity|].
            eapply eval_Econs; [apply eval_Econst_int| |apply eval_Enil].
            apply bitcoin_cast_const'; lia. }
          exact (exec_bitcoin_helper_call (bitcoin_version_locals bl) l4 mb None _skipBits jets.f_skipBits
            _ _ _ _ _ _ me ltac:(unfold bitcoin_core_helpers; simpl; tauto) ltac:(reflexivity) Hargs
            ltac:(reflexivity) HCallS).
        + pose proof (write_effect_seq mr mb me bd dbase bw outedge cursor 1 257 [Some false]
            (repeat None 257) eq_refl ltac:(lia) HFrameR E1 E2) as Eseq.
          assert (Hcells : [Some false] ++ repeat None 257 = V).
          { unfold V, annex_cells. rewrite <- Hidx, Hnth. reflexivity. }
          exact (eq_rect _ (fun c => write_effect mr me bd dbase bw outedge cursor 258 c) Eseq _ Hcells). }
    destruct HBranch as (lef & me & HBr & HEff).
    destruct (write_effect_lift mc mr me bl bd dbase bw outedge cursor 258 V HLd HLw
      HRMem HRPerm HRValid HEff) as (c & p & fl & l & pm & vv).
    exists lef, me. refine (conj _ (conj c (conj p (conj fl (conj l (conj pm vv)))))).
    unfold annex_rest.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l1); [exact HHead|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := lef);
      [|apply exec_Sreturn_some, eval_Econst_int].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := l4); [exact HCond|].
    eapply exec_Sifthenelse with (v1 := Vint (bit_int b1)) (b := b1).
    - apply eval_Etempvar. unfold l4. apply PTree.gss.
    - destruct b1; reflexivity.
    - exact HBr. }
  destruct (bitcoin_wrapper_layout f_simplicity_bitcoin_input_annex_hash annex_rest V
    (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 258 bytes
    bitcoin_input_annex_hash_shape HBf HA HBytes ltac:(lia) HFrame HMid)
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (bitcoin_annex_result annexes a). split; [apply bitcoin_input_annex_hash_sem|].
  split; [exact HCall|]. split; [rewrite encode_annex_result; exact HCells|].
  split; [exact HPrefix|]. rewrite HB. split; [exact HFields|]. exact HMem.
Qed.
