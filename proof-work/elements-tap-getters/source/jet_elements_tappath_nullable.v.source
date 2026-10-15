(** The Elements [tappath] jet under an environment relation that the real
    caller establishes for every path length: the path pointer is required
    only for a non-empty path ([simplicity_elements_mallocTapEnv] stores
    [path = NULL] otherwise, and the jet reads it only when the index is in
    range).  The relation of [C.jet_elements_tappath_local] implies this
    one; the proof is that module's proof with the pointer load taken
    inside the in-range branch. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option C.jet_elements_prim.
Require Import C.jet_application_sep C.jet_frame_copy C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_input_layout C.jet_output_layout_step.
Require Import C.jet_read8_input_word_total C.jet_uint32_array_init C.jet_word_repr.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_version_exec C.jet_exec.
Require C.jets.
Require Import C.jet_elements_field_eval C.jet_elements_effects C.jet_elements_wrapper.
Require Import C.jet_elements_transport C.jet_elements_call C.jet_elements_steps.
Require Import C.jet_elements_indexed_exec C.jet_elements_env_load C.jet_elements_indexed_scalar C.jet_elements_indexed_ptr.
Require Import C.jet_elements_hash_write C.jet_elements_hash_getters C.jet_elements_script_cmr_local.
Require Import C.jet_elements_hash_elem.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 120.
Require Import C.jet_elements_tappath_local.

Definition elements_tappath_env_rep_bounded (limit : nat) (m : mem) (env : val) (e : Elements.env)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt tbase bp pbase,
    env = Vptr be (Ptrofs.repr ebase) /\
    (length (tappath (Elements.envTap e)) <= limit)%nat /\
    0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
    0 <= tbase /\ tbase + 176 <= Ptrofs.max_unsigned /\
    0 <= pbase /\ pbase + 32 * Z.of_nat (length (tappath (Elements.envTap e))) <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)) /\
    (0 < Z.of_nat (length (tappath (Elements.envTap e))) ->
     Mem.load Mptr m bt (tbase + 0) = Some (Vptr bp (Ptrofs.repr pbase))) /\
    Mem.load Mint8unsigned m bt (tbase + 168) =
      Some (Vint (Int.repr (Z.of_nat (length (tappath (Elements.envTap e)))))) /\
    (forall j h, nth_error (tappath (Elements.envTap e)) j = Some h ->
      hash_elem_rep m bp (pbase + 32 * Z.of_nat j) h) /\
    fp = [(be, ebase + 8, ebase + 16); (bt, tbase + 0, tbase + 8);
          (bp, pbase, pbase + 32 * Z.of_nat (length (tappath (Elements.envTap e))))].

(** The original nullable-128 relation is definitionally preserved. *)
Definition elements_tappath_env_rep_nullable := elements_tappath_env_rep_bounded 128.
Definition elements_tappath_env_rep_u8 := elements_tappath_env_rep_bounded 255.

Lemma elements_tappath_nullable_128_unchanged m env e fp :
  elements_tappath_env_rep_nullable m env e fp <->
exists be ebase bt tbase bp pbase,
    env = Vptr be (Ptrofs.repr ebase) /\
    (length (tappath (Elements.envTap e)) <= 128)%nat /\
    0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
    0 <= tbase /\ tbase + 176 <= Ptrofs.max_unsigned /\
    0 <= pbase /\ pbase + 32 * Z.of_nat (length (tappath (Elements.envTap e))) <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)) /\
    (0 < Z.of_nat (length (tappath (Elements.envTap e))) ->
     Mem.load Mptr m bt (tbase + 0) = Some (Vptr bp (Ptrofs.repr pbase))) /\
    Mem.load Mint8unsigned m bt (tbase + 168) =
      Some (Vint (Int.repr (Z.of_nat (length (tappath (Elements.envTap e)))))) /\
    (forall j h, nth_error (tappath (Elements.envTap e)) j = Some h ->
      hash_elem_rep m bp (pbase + 32 * Z.of_nat j) h) /\
    fp = [(be, ebase + 8, ebase + 16); (bt, tbase + 0, tbase + 8);
          (bp, pbase, pbase + 32 * Z.of_nat (length (tappath (Elements.envTap e))))].
Proof. reflexivity. Qed.

Lemma elements_tappath_rep_bounded_mono small large :
  (small <= large)%nat -> forall m env e fp,
  elements_tappath_env_rep_bounded small m env e fp ->
  elements_tappath_env_rep_bounded large m env e fp.
Proof.
  intros Hbound m env e fp (be & ebase & bt & tbase & bp & pbase & HE & HL & Hrest).
  exists be, ebase, bt, tbase, bp, pbase. split; [exact HE|]. split; [lia|exact Hrest].
Qed.

Lemma elements_tappath_nullable_in_u8 m env e fp :
  elements_tappath_env_rep_nullable m env e fp -> elements_tappath_env_rep_u8 m env e fp.
Proof. apply elements_tappath_rep_bounded_mono. lia. Qed.

Lemma elements_tappath_env_rep_weaken m env e fp :
  elements_tappath_env_rep m env e fp -> elements_tappath_env_rep_nullable m env e fp.
Proof.
  intros (be & ebase & bt & tbase & bp & pbase & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
  exists be, ebase, bt, tbase, bp, pbase. repeat (split; [assumption|]). split; [intros _; exact H10|].
  repeat (split; [assumption|]). assumption.
Qed.

Theorem elements_tappath_bounded_local_spec (limit : nat) (Hlimit : (limit <= 255)%nat) :
  application_jet_local_spec_sep f_simplicity_tappath elements_ge Elements.env Word8
    (Ty.Sum Ty.Unit Word256) (elements_tappath_env_rep_bounded limit)
    (fun a environment => @elements_tappath_spec
      (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor a fp
    (be & ebase & bt & tbase & bp & pbase & HEnvVal & HPL0 & He0 & He1 & Ht0 & Ht1 & Hp0 & Hp1 &
      HLtap & HLpath & HLlen & HLelem & HFp)
    HSep HBf HA [HSedge HSoff] HR0 HRmax Hin HFrame.
  subst env fp.
  set (path := tappath (Elements.envTap environment)) in *.
  set (nn := Z.of_nat (length path)) in *.
  pose proof HPL0 as HPL. fold path in HPL.
  assert (Hnn : 0 <= nn <= 255) by (subst nn; lia).
  assert (HB : Z.of_nat (bitSize (Ty.Sum Ty.Unit Word256)) = 257) by reflexivity.
  rewrite HB in HSep, HFrame.
  change (Z.of_nat (bitSize Word8)) with 8 in HRmax.
  rewrite Forall_forall in HSep.
  assert (S1 : out_sep bd dbase bw outedge cursor 257 be (ebase + 8) (ebase + 16))
    by exact (HSep (be, ebase + 8, ebase + 16) ltac:(simpl; auto)).
  assert (S4 : out_sep bd dbase bw outedge cursor 257 bt (tbase + 0) (tbase + 8))
    by exact (HSep (bt, tbase + 0, tbase + 8) ltac:(simpl; auto)).
  assert (S5 : out_sep bd dbase bw outedge cursor 257 bp pbase (pbase + 32 * nn))
    by exact (HSep (bp, pbase, pbase + 32 * nn) ltac:(simpl; auto)).
  apply frame_input_word_at_encode in Hin.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  set (az := @toZ (WordToZ 3) a).
  assert (Haz : 0 <= az < 256) by (unfold az; exact (word_toZ_range 3 a)).
  set (iv := Int.repr az).
  set (b := az <? nn).
  set (V := tappath_cells path a).
  assert (HMid : elements_wrapper_mid f_simplicity_tappath tappath_rest V
    (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 257 bytes).
  { unfold elements_wrapper_mid. intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    assert (HBa : Mem.loadbytes ma bs sbase 16 = Some bytes).
    { erewrite Mem.loadbytes_alloc_unchanged; eauto.
      eapply Mem.perm_valid_block. eapply (Mem.loadbytes_range_perm _ _ _ _ _ HBytes sbase); lia. }
    destruct (elements_read8_step m ma mc bl bs sbase bi edge read_cursor a bytes ltac:(lia)
      (conj HSedge HSoff) Hin HAlloc HBa HStore)
      as (mr & Hread & HRMem & HRPerm & HRValid & HRLoads).
    fold az in Hread. fold iv in Hread.
    pose proof HFrame as [HDB [[HDE HDO] [HEd [HN [HMx [PD HWords]]]]]].
    destruct (write_frame_at_head m bd dbase bw outedge cursor 257 ltac:(lia) HFrame)
      as [_ [_ [_ [w0 Hw0]]]].
    assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
    assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
    assert (HFrameR : write_frame_at mr bd dbase bw outedge cursor 257).
    { eapply write_frame_at_preserved with (m := mc).
      - intros chunk b0 ofs v Hb HL. rewrite HRMem; [exact HL|].
        destruct Hb; subst; auto.
      - exact HRPerm.
      - exact HFrameC. }
    assert (HE0 : Mem.load Mptr mr be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)))
      by (apply HRLoads; exact HLtap).
    assert (HE1 : 0 < nn -> Mem.load Mptr mr bt (tbase + 0) = Some (Vptr bp (Ptrofs.repr pbase)))
      by (intros Hpos; apply HRLoads; exact (HLpath Hpos)).
    assert (HE2 : Mem.load Mint8unsigned mr bt (tbase + 168) = Some (Vint (Int.repr nn)))
      by (apply HRLoads; exact HLlen).
    assert (HF1 : write_frame_at mr bd dbase bw outedge cursor 1).
    { eapply write_frame_at_shorter; [|exact HFrameR]. lia. }
    destruct (elements_writeBit_step mr bd dbase bw outedge cursor b HF1) as (mb & Hwb1 & E1).
    assert (HFb : write_frame_at mb bd dbase bw outedge (cursor - 1) 256).
    { eapply write_frame_at_after_effect with (cells := [Some b]);
        [reflexivity|lia|exact HFrameR|exact E1]. }
    assert (HLoadB : forall chunk b0 lo hi ofs, out_sep bd dbase bw outedge cursor 257 b0 lo hi ->
      lo <= ofs -> ofs + size_chunk chunk <= hi -> Mem.load chunk mb b0 ofs = Mem.load chunk mr b0 ofs).
    { intros chunk b0 lo hi ofs Hs Hlo Hhi.
      eapply write_effect_env_load with (bf := bd) (base := dbase) (bw := bw) (edge := outedge)
        (cursor := cursor) (cursor0 := cursor) (count0 := 257) (n := 1)
        (cells := [Some b]) (lo := lo) (hi := hi);
        [lia|lia|lia|lia|exact E1|exact Hs|exact Hlo|exact Hhi]. }
    set (le0 := elements_wrapper_temps f_simplicity_tappath (Vptr be (Ptrofs.repr ebase))
      bd dbase bs sbase).
    assert (HEnv0 : le0!_env = Some (Vptr be (Ptrofs.repr ebase)))
      by (unfold le0, elements_wrapper_temps; apply PTree.gss).
    assert (HDst0 : le0!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
    { unfold le0, elements_wrapper_temps. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. apply PTree.gss. }
    set (l1 := PTree.set _i (Vint iv) (PTree.set _t'1 (Vint iv) le0)).
    set (l2 := PTree.set _t'5 (Vptr bt (Ptrofs.repr tbase)) l1).
    set (l3 := PTree.set _t'6 (Vint (Int.repr nn)) l2).
    set (l4 := PTree.set _t'2 (Vint (if b then Int.one else Int.zero)) l3).
    assert (Hi4 : l4!_i = Some (Vint iv)).
    { unfold l4, l3, l2, l1. repeat rewrite PTree.gso by discriminate. apply PTree.gss. }
    assert (Hd4 : l4!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
    { unfold l4, l3, l2, l1. repeat rewrite PTree.gso by discriminate. exact HDst0. }
    assert (He4 : l4!_env = Some (Vptr be (Ptrofs.repr ebase))).
    { unfold l4, l3, l2, l1. repeat rewrite PTree.gso by discriminate. exact HEnv0. }
    assert (HHead : Clight2.exec_stmt elements_ge (elements_version_locals bl) le0 mc tappath_head E0 l1 mr
      Out_normal).
    { unfold tappath_head.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := PTree.set _t'1 (Vint iv) le0).
      - change (PTree.set _t'1 (Vint iv) le0) with (set_opttemp (Some _t'1) (Vint iv) le0).
        eapply exec_elements_helper_call with (id := _simplicity_read8) (f := jets.f_simplicity_read8)
          (vargs := [Vptr bl Ptrofs.zero]) (vres := Vint iv).
        + unfold elements_core_helpers. simpl. tauto.
        + reflexivity.
        + eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
        + reflexivity.
        + exact Hread.
      - apply exec_set. eapply eval_Ecast; [apply eval_Etempvar; apply PTree.gss|].
        change (Some (Vint (Int.zero_ext 8 iv)) = Some (Vint iv)).
        unfold iv. rewrite zero_ext8_small by lia. reflexivity. }
    assert (Hcmp : Int.lt iv (Int.repr nn) = b).
    { unfold iv, b. apply tappath_lt_small; lia. }
    assert (HCond : Clight2.exec_stmt elements_ge (elements_version_locals bl) l1 mr tappath_cond E0 l4 mb
      Out_normal).
    { unfold tappath_cond.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l2).
      - apply exec_set. eapply eval_elements_env_taproot; [|exact He0|lia|exact HE0].
        unfold l1. repeat rewrite PTree.gso by discriminate. exact HEnv0.
      - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l3).
        + apply exec_set.
          eapply eval_elements_field_value with (sid := _elementsTapEnv) (delta := 168) (chunk := Mint8unsigned).
          * reflexivity.
          * exact elements_tapEnv_pathLen.
          * reflexivity.
          * apply eval_elements_deref_struct. unfold l2. apply PTree.gss.
          * rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HE2].
        + change l4 with (set_opttemp (Some _t'2) (Vint (if b then Int.one else Int.zero)) l3).
          eapply exec_elements_helper_call with (id := _writeBit) (f := jets.f_writeBit)
            (vargs := [Vptr bd (Ptrofs.repr dbase); Vint (if b then Int.one else Int.zero)])
            (vres := Vint (if b then Int.one else Int.zero)).
          * unfold elements_core_helpers. simpl. tauto.
          * reflexivity.
          * eapply eval_Econs.
            -- apply eval_Etempvar. unfold l3, l2, l1. repeat rewrite PTree.gso by discriminate. exact HDst0.
            -- reflexivity.
            -- eapply eval_Econs with (v1 := Val.of_bool b).
               ++ eapply eval_Ebinop with (v1 := Vint iv) (v2 := Vint (Int.repr nn)).
                  ** apply eval_Etempvar. unfold l3, l2. repeat rewrite PTree.gso by discriminate.
                     unfold l1. apply PTree.gss.
                  ** apply eval_Etempvar. unfold l3. apply PTree.gss.
                  ** change (Some (Val.of_bool (Int.lt iv (Int.repr nn))) = Some (Val.of_bool b)).
                     rewrite Hcmp. reflexivity.
               ++ apply elements_bool_cast.
               ++ apply eval_Enil.
          * reflexivity.
          * exact Hwb1. }
    assert (HBranch : exists le'' me,
      Clight2.exec_stmt elements_ge (elements_version_locals bl) l4 mb
        (if b then tappath_then else elements_skip_stmt 256) E0 le'' me Out_normal /\
      write_effect mr me bd dbase bw outedge cursor 257 V).
    { destruct b eqn:Hb.
      - (* in range *)
        assert (Hlt : az < nn) by (apply Z.ltb_lt; exact Hb).
        destruct (nth_error path (Z.to_nat az)) as [h|] eqn:Hnth;
          [|apply nth_error_None in Hnth; subst nn; lia].
        set (ofs := pbase + 32 * az).
        assert (Hrep : hash_elem_rep m bp ofs h).
        { pose proof (HLelem _ _ Hnth) as H. rewrite Z2Nat.id in H by lia. exact H. }
        assert (Hrepb : hash_elem_rep mb bp ofs h).
        { eapply hash_elem_rep_mono; [exact Hrep|].
          intros chunk o v Hlo Hhi Hl.
          rewrite (HLoadB chunk bp pbase (pbase + 32 * nn) o S5 ltac:(unfold ofs in Hlo; lia)
            ltac:(unfold ofs in Hhi; lia)).
          apply HRLoads. exact Hl. }
        assert (Hmb0 : Mem.load Mptr mb be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase))).
        { rewrite (HLoadB Mptr be (ebase + 8) (ebase + 16) (ebase + 8) S1 ltac:(lia)
            ltac:(change (size_chunk Mptr) with 8; lia)). exact HE0. }
        assert (Hmb1 : Mem.load Mptr mb bt (tbase + 0) = Some (Vptr bp (Ptrofs.repr pbase))).
        { rewrite (HLoadB Mptr bt (tbase + 0) (tbase + 8) (tbase + 0) S4 ltac:(lia)
            ltac:(change (size_chunk Mptr) with 8; lia)). exact (HE1 ltac:(lia)). }
        assert (HSp : out_sep bd dbase bw outedge (cursor - 1) 256 bp ofs (ofs + 32)).
        { eapply out_sep_range with (lo := pbase) (hi := pbase + 32 * nn);
            [|unfold ofs; lia|unfold ofs; lia].
          eapply out_sep_sub with (cursor := cursor) (count := 257); [lia|lia|lia|lia|exact S5]. }
        destruct (hash_elem_pay bd dbase bw outedge mb bp ofs h (cursor - 1) Hrepb
          ltac:(unfold ofs; lia) ltac:(unfold ofs; lia) HSp HFb) as (me & HCallP & E2).
        set (la := PTree.set _t'3 (Vptr bt (Ptrofs.repr tbase)) l4).
        set (lb := PTree.set _t'4 (Vptr bp (Ptrofs.repr pbase)) la).
        exists lb, me. split.
        + unfold tappath_then.
          eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := la).
          * apply exec_set. eapply eval_elements_env_taproot; [exact He4|exact He0|lia|exact Hmb0].
          * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := lb).
            -- apply exec_set.
               eapply eval_elements_field_value with (sid := _elementsTapEnv) (delta := 0) (chunk := Mptr).
               ++ reflexivity.
               ++ exact elements_tapEnv_path.
               ++ reflexivity.
               ++ apply eval_elements_deref_struct. unfold la. apply PTree.gss.
               ++ rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact Hmb1].
            -- eapply exec_Scall with (vf := Vptr (elements_symbol_block _writeHash) Ptrofs.zero)
                 (f := Internal f_writeHash)
                 (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bp (Ptrofs.repr ofs)]) (vres := Vundef).
               ++ reflexivity.
               ++ eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact elements_writeHash_symbol]|
                    apply deref_loc_reference; reflexivity].
               ++ eapply eval_Econs.
                  ** apply eval_Etempvar. unfold lb, la. repeat rewrite PTree.gso by discriminate. exact Hd4.
                  ** reflexivity.
                  ** eapply eval_Econs with (v1 := Vptr bp (Ptrofs.repr ofs)).
                     --- eapply eval_Ebinop with (v1 := Vptr bp (Ptrofs.repr pbase)) (v2 := Vint iv).
                         +++ apply eval_Etempvar. unfold lb. apply PTree.gss.
                         +++ apply eval_Etempvar. unfold lb, la. repeat rewrite PTree.gso by discriminate.
                             exact Hi4.
                         +++ unfold ofs, iv. rewrite <- (tappath_index_ptr pbase az Hp0 Haz ltac:(lia)).
                             cbn [typeof]. unfold sem_binary_operation.
                             exact (sem_add_ptr_uchar_sizeof (Clight.genv_cenv elements_ge)
                               (Tstruct _sha256_midstate noattr) (Int.repr az) (Ptrofs.repr pbase) bp 32 mb
                               elements_sizeof_midstate).
                     --- reflexivity.
                     --- apply eval_Enil.
               ++ exact elements_writeHash_funct.
               ++ reflexivity.
               ++ exact HCallP.
        + pose proof (write_effect_seq mr mb me bd dbase bw outedge cursor 1 256 [Some true]
            (hash_cells (hash256_reg h)) eq_refl ltac:(lia) HFrameR E1 E2) as Eseq.
          assert (Hcells : [Some true] ++ hash_cells (hash256_reg h) = V).
          { unfold V, tappath_cells. fold az. rewrite Hnth. reflexivity. }
          exact (eq_rect _ (fun c => write_effect mr me bd dbase bw outedge cursor 257 c) Eseq _ Hcells).
      - (* out of range *)
        assert (Hge : nn <= az) by (apply Z.ltb_ge; exact Hb).
        assert (Hnth : nth_error path (Z.to_nat az) = None).
        { apply nth_error_None. subst nn. lia. }
        destruct (elements_skipBits_step mb bd dbase bw outedge (cursor - 1) 256%nat HFb)
          as (me & HCallS & E2).
        exists l4, me. split.
        + unfold elements_skip_stmt.
          assert (Hargs : eval_exprlist elements_ge (elements_version_locals bl) l4 mb
            [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 256) tint]
            (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil))
            [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr (Z.of_nat 256))]).
          { eapply eval_Econs; [apply eval_Etempvar; exact Hd4|reflexivity|].
            eapply eval_Econs; [apply eval_Econst_int| |apply eval_Enil].
            apply elements_cast_const'; lia. }
          exact (exec_elements_helper_call (elements_version_locals bl) l4 mb None _skipBits jets.f_skipBits
            _ _ _ _ _ _ me ltac:(unfold elements_core_helpers; simpl; tauto) ltac:(reflexivity) Hargs
            ltac:(reflexivity) HCallS).
        + pose proof (write_effect_seq mr mb me bd dbase bw outedge cursor 1 256 [Some false]
            (repeat None 256) eq_refl ltac:(lia) HFrameR E1 E2) as Eseq.
          assert (Hcells : [Some false] ++ repeat None 256 = V).
          { unfold V, tappath_cells. fold az. rewrite Hnth. reflexivity. }
          exact (eq_rect _ (fun c => write_effect mr me bd dbase bw outedge cursor 257 c) Eseq _ Hcells). }
    destruct HBranch as (lef & me & HBr & HEff).
    destruct (write_effect_lift mc mr me bl bd dbase bw outedge cursor 257 V HLd HLw
      HRMem HRPerm HRValid HEff) as (c & p & fl & l & pm & vv).
    exists lef, me. refine (conj _ (conj c (conj p (conj fl (conj l (conj pm vv)))))).
    unfold tappath_rest.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l1); [exact HHead|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := lef);
      [|apply exec_Sreturn_some, eval_Econst_int].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := l4); [exact HCond|].
    eapply exec_Sifthenelse with (v1 := Vint (if b then Int.one else Int.zero)) (b := b).
    - apply eval_Etempvar. unfold l4. apply PTree.gss.
    - destruct b; reflexivity.
    - exact HBr. }
  destruct (elements_wrapper_layout f_simplicity_tappath tappath_rest V
    (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 257 bytes
    elements_tappath_shape HBf HA HBytes ltac:(lia) HFrame HMid)
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (elements_tappath_result path a). split; [apply elements_tappath_sem|].
  split; [exact HCall|]. split.
  - unfold V, tappath_cells in HCells. unfold elements_tappath_result.
    change (@toZ (WordToZ 3) a) with (toZ a) in HCells.
    destruct (nth_error path (Z.to_nat (toZ a))) as [h|].
    + rewrite encode_sum_inr_hash', encode_from_hash256. exact HCells.
    + exact HCells.
  - split; [exact HPrefix|]. rewrite HB. split; [exact HFields|]. exact HMem.
Qed.

Theorem elements_tappath_nullable_local_spec :
  application_jet_local_spec_sep f_simplicity_tappath elements_ge Elements.env Word8
    (Ty.Sum Ty.Unit Word256) elements_tappath_env_rep_nullable
    (fun a environment => @elements_tappath_spec
      (PrimitivePrimSem option_Monad_Zero) a environment).
Proof. apply (elements_tappath_bounded_local_spec 128). lia. Qed.

Theorem elements_tappath_u8_local_spec :
  application_jet_local_spec_sep f_simplicity_tappath elements_ge Elements.env Word8
    (Ty.Sum Ty.Unit Word256) elements_tappath_env_rep_u8
    (fun a environment => @elements_tappath_spec
      (PrimitivePrimSem option_Monad_Zero) a environment).
Proof. apply (elements_tappath_bounded_local_spec 255). lia. Qed.
