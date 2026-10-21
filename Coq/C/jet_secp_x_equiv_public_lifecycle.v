(** Actual public frame/field/point allocations, frame copy and frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Events Values.
Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_sx_mem C.jet_sx_state C.jet_sx_expr C.jet_sx_exec C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_public_copy C.jet_secp_public_body C.jet_secp_local_regions.
Require Import C.jet_secp_owned_public_lifecycle C.jet_secp_x_equiv_public_statements.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma x_equiv_public_blocks bl bq bp : blocks_of_env secp_ge (x_equiv_public_env bl bq bp) =
  [(bl,0,16);(bp,0,128);(bq,0,40)].
Proof. reflexivity. Qed.
Lemma x_equiv_free_public m bl bq bp : bp<>bl -> bq<>bl -> bp<>bq ->
  Mem.range_perm m bl 0 16 Cur Freeable -> Mem.range_perm m bp 0 128 Cur Freeable ->
  Mem.range_perm m bq 0 40 Cur Freeable ->
  exists mf, Mem.free_list m (blocks_of_env secp_ge (x_equiv_public_env bl bq bp)) = Some mf /\
    lframe (fun b _ => b<>bp /\ b<>bq /\ b<>bl) m mf.
Proof.
  intros HPL HQL HPQ HL HP HQ.
  destruct (free_list_exists [(bl,0,16);(bp,0,128);(bq,0,40)] m) as (mf & HF & HU).
  - cbn;repeat constructor;cbn;intuition congruence.
  - intros b lo hi [HE|[HE|[HE|HE]]];
      [inversion HE;subst;exact HL|inversion HE;subst;exact HP|inversion HE;subst;exact HQ|contradiction].
  - exists mf. split;[rewrite x_equiv_public_blocks;exact HF|].
    eapply lframe_implies;[apply lframe_unchanged;exact HU|].
    intros b pos (HNP & HNQ & HNL) HV;cbn;intuition congruence.
Qed.

Theorem x_equiv_prepare_public le m0 ma mb mc bl bq bp bd dbase bs sbase bw outedge cursor N bi edge rc :
  Mem.alloc m0 0 16 = (ma,bl) -> Mem.alloc ma 0 40 = (mb,bq) -> Mem.alloc mb 0 128 = (mc,bp) ->
  le!_src=Some (Vptr bs (Ptrofs.repr sbase)) ->
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  exists md,
    Clight2.exec_stmt secp_ge (x_equiv_public_env bl bq bp) le mc
      (Sassign (Evar _src secp_frame_type) (Etempvar _src secp_frame_type)) E0 le md Out_normal /\
    Mem.range_perm md bp 0 128 Cur Freeable /\ Mem.range_perm md bq 0 40 Cur Freeable /\
    Mem.range_perm md bl 0 16 Cur Freeable /\ frame_fields_at md bl 0 bi edge rc /\
    bp<>bl /\ bq<>bl /\ bp<>bq /\ xsep (extA m0 bd bw bi) [(bp,0);(bq,0);(bl,0)] /\
    finv m0 bd dbase bw outedge cursor N bi md false [] /\
    lframe (fun b _ => b<>bp /\ b<>bq /\ b<>bl) m0 md /\
    ~Mem.valid_block m0 bp /\ ~Mem.valid_block m0 bq /\ ~Mem.valid_block m0 bl.
Proof.
  intros AL AQ AP HTemp HO HBase HAlign HFields.
  destruct (owned_public_alloc_fresh 40 m0 ma bl bq mb AL AQ) as (NL & NQ & HQL).
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ AP) as NPi.
  assert (NP : ~Mem.valid_block m0 bp).
  { intro HV;apply NPi;eapply Mem.valid_block_alloc;[exact AQ|].
    eapply Mem.valid_block_alloc;eassumption. }
  assert (HPL : bp<>bl).
  { intro HE;apply NPi;rewrite HE;eapply Mem.valid_block_alloc;[exact AQ|].
    eapply Mem.valid_new_block;exact AL. }
  assert (HPQ : bp<>bq).
  { intro HE;apply NPi;rewrite HE;eapply Mem.valid_new_block;exact AQ. }
  destruct (owned_public_alloc_freeable 40 m0 ma bl bq mb AL AQ) as (FLb & FQb).
  assert (FL : Mem.range_perm mc bl 0 16 Cur Freeable).
  { intros pos HP;eapply Mem.perm_alloc_1;[exact AP|apply FLb;exact HP]. }
  assert (FQ : Mem.range_perm mc bq 0 40 Cur Freeable).
  { intros pos HP;eapply Mem.perm_alloc_1;[exact AP|apply FQb;exact HP]. }
  assert (FP : Mem.range_perm mc bp 0 128 Cur Freeable).
  { intros pos HP;eapply Mem.perm_alloc_2;eassumption. }
  assert (FA : lframe (fun _ _ => True) m0 mc).
  { eapply lframe_trans;[eapply owned_public_alloc_lframe;eassumption|].
    apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact AP. }
  assert (SourceC : frame_fields_at mc bs sbase bi edge rc).
  { destruct HFields as (HE & HC). pose proof (load_valid _ _ _ _ _ HE) as HV.
    split;rewrite (proj1 FA) by auto;assumption. }
  destruct SourceC as (HEdge & HCursor).
  destruct (frame_loadbytes_at mc bs sbase _ _ HEdge HCursor) as (bytes & HL).
  pose proof (Mem.loadbytes_length _ _ _ _ _ HL) as HLen.
  assert (HW : Mem.range_perm mc bl 0 (0+Z.of_nat (length bytes)) Cur Writable).
  { rewrite HLen;apply freeable_range_writable;exact FL. }
  destruct (Mem.range_perm_storebytes mc bl 0 bytes HW) as (md & HS).
  assert (HF : lframe (fun b _ => b<>bp /\ b<>bq /\ b<>bl) m0 md).
  { eapply lframe_trans;[eapply lframe_implies;[exact FA|intros;exact I]|].
    apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact HS|].
    intros pos HP (_ & _ & HNL);apply HNL;reflexivity. }
  assert (Ext : eqext m0 bd bw bi m0 md).
  { eapply lframe_implies;[exact HF|]. intros b pos [_ HV] _;repeat split;intro HE;subst b;contradiction. }
  assert (HU : Ptrofs.unsigned (Ptrofs.repr sbase)=sbase).
  { apply Ptrofs.unsigned_repr;unfold frame_base_valid in HBase;lia. }
  exists md. split.
  - eapply exec_Sassign_copy.
    + apply eval_Evar_local;reflexivity.
    + apply eval_Etempvar;exact HTemp.
    + reflexivity.
    + eapply assign_loc_copy with (b':=bs) (ofs':=Ptrofs.repr sbase) (bytes:=bytes).
      * reflexivity.
      * intros _;change (8 | Ptrofs.unsigned (Ptrofs.repr sbase));rewrite HU;exact HAlign.
      * intros _;change (8 | 0);exists 0;reflexivity.
      * left;intro HE;apply NL;subst bs;exact (load_valid _ _ _ _ _ (proj1 HFields)).
      * change (Mem.loadbytes mc bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16=Some bytes);rewrite HU;exact HL.
      * exact HS.
  - split;[intros pos HP;eapply Mem.perm_storebytes_1;[exact HS|apply FP;exact HP]|].
    split;[intros pos HP;eapply Mem.perm_storebytes_1;[exact HS|apply FQ;exact HP]|].
    split;[intros pos HP;eapply Mem.perm_storebytes_1;[exact HS|apply FL;exact HP]|].
    split;[exact (frame_copy_fields_at mc md bs sbase bl bytes _ _ HL HS HEdge HCursor)|].
    split;[exact HPL|]. split;[exact HQL|]. split;[exact HPQ|]. split.
    + intros [|[|[|r]]] HI;cbn [blk bas lay nth fst snd];unfold extA,fext;
        [intros [_ HV];contradiction|intros [_ HV];contradiction|intros [_ HV];contradiction|cbn in HI;lia].
    + split;[eapply finv_stable;[exact HO|apply finv_init;exact HO|exact Ext]|].
      split;[exact HF|]. repeat split;assumption.
Qed.
