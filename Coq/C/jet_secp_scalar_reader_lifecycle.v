(* Real read_scalar allocation and release around its unchanged checked body. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib AST Ctypes Clight Clightdefs ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_wrapper_run C.jet_secp_frame C.jet_secp_local_regions.
Require Import C.jet_output_layout C.jet_encoding C.jet_frame_bits C.jet_secp_fe_math C.jet_secp_input_bytes.
Require Import C.jet_secp_scalar_reader_run C.jet_secp_scalar_reader_set.
Require Import C.jet_secp_scalar_reader_body C.jet_secp_scalar_reader_value.
Require Import C.jet_secp_scalar_overflow_numeric C.jet_secp_canonical_scalar.
Require Import C.jet_secp_fe_nv C.jet_secp_symbolic_substitution C.jet_frame_layout.
Require Import C.jet_secp_scalar_set_b32_exec C.jet_secp_scalar_set_shape.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma scalar_reader_local_lookup id r ty :
  vlookup scalar_reader_venv id = Some (r, ty) ->
  id = jets_secp._buf /\ r = 2%nat /\ ty = tarray tuchar 32.
Proof.
  cbn [scalar_reader_venv vlookup].
  destruct (Pos.eqb jets_secp._buf id) eqn:HId; [|discriminate].
  apply Pos.eqb_eq in HId; intro H; inversion H; subst; repeat split; reflexivity.
Qed.
Local Opaque secp_ge.
Lemma free_scalar_reader_buffer rho layout bi edge e m :
  rep rho layout (sregs (scalar_reader_set_state bi edge)) m ->
  ematch layout scalar_reader_venv e ->
  exists mf,
    Mem.free_list m (blocks_of_env secp_ge e) = Some mf /\
    Mem.unchanged_on (fun b _ => b <> blk layout 2) m mf.
Proof.
  intros HRep HEnv.
  assert (HLength : length layout = 3%nat).
  { destruct HRep as [HLen _]; rewrite scalar_reader_set_regions in HLen; exact HLen. }
  destruct (rep_free_region rho layout (sregs (scalar_reader_set_state bi edge)) m 2 32 HRep)
    as [HBase HFree].
  { rewrite scalar_reader_set_regions; cbn [length]; lia. }
  { rewrite scalar_reader_set_regions; reflexivity. }
  destruct (callee_env_blocks secp_ge layout scalar_reader_venv e) as [HBlocks HNoRepeat].
  - intros id1 id2 r1 r2 ty1 ty2 H1 H2 HSame.
    destruct (scalar_reader_local_lookup id1 r1 ty1 H1) as [_ [-> _]].
    destruct (scalar_reader_local_lookup id2 r2 ty2 H2) as [_ [-> _]].
    reflexivity.
  - intro id; exact (proj1 (HEnv id)).
  - intros id r ty HLookup.
    destruct (scalar_reader_local_lookup id r ty HLookup) as [_ [-> _]].
    rewrite HLength; lia.
  - intros id1 id2 r ty1 ty2 H1 H2.
    destruct (scalar_reader_local_lookup id1 r ty1 H1) as [-> _].
    destruct (scalar_reader_local_lookup id2 r ty2 H2) as [-> _].
    reflexivity.
  - destruct (free_list_exists (blocks_of_env secp_ge e) m HNoRepeat) as [mf [HFreeList HUnchanged]].
    + intros b lo hi HIn.
      destruct (HBlocks b lo hi HIn) as (id & r & ty & HLookup & -> & -> & ->).
      destruct (scalar_reader_local_lookup id r ty HLookup) as [_ [-> ->]].
      change (Mem.range_perm m (blk layout 2) 0 32 Cur Freeable); exact HFree.
    + exists mf; split; [exact HFreeList|].
      eapply Mem.unchanged_on_implies; [exact HUnchanged|].
      intros b ofs HDiff HValid HIn.
      apply in_map_iff in HIn; destruct HIn as [[[b' lo] hi] [HEq HIn]].
      cbn in HEq; subst b'.
      destruct (HBlocks b lo hi HIn) as [id [r [ty [HLookup [HEq _]]]]].
      destruct (scalar_reader_local_lookup id r ty HLookup) as [_ [-> _]].
      exact (HDiff HEq).
Qed.

Lemma represented_layout_valid rho layout regs m b :
  rep rho layout regs m -> In b (map fst layout) -> Mem.valid_block m b.
Proof.
  intros [HLen [HSep HRegions]] HIn.
  apply in_map_iff in HIn; destruct HIn as [[b' base] [HEq HIn]]; cbn in HEq; subst b'.
  destruct (In_nth layout (b, base) (1%positive, 0) HIn) as [r [HIndex HNth]].
  assert (HIndexRegs : (r < length regs)%nat) by lia.
  destruct (nth_error regs r) as [reg|] eqn:HReg.
  - destruct (HRegions r reg HReg) as [_ [HValid _]].
    unfold blk, lay in HValid; rewrite HNth in HValid; exact HValid.
  - apply nth_error_None in HReg; lia.
Qed.

Definition scalar_reader_final_regs bi edge := firstn 2 (sregs (scalar_reader_set_state bi edge)).
Lemma scalar_reader_final_length bi edge : length (scalar_reader_final_regs bi edge) = 2%nat.
Proof. unfold scalar_reader_final_regs; rewrite scalar_reader_set_regions; reflexivity. Qed.

Lemma scalar_reader_foot_extended layout buffer base bi edge b ofs :
  length layout = 2%nat ->
  foot (layout ++ [(buffer, base)]) (map rshape (sregs (scalar_reader_initial bi edge))) b ofs ->
  foot layout (map rshape (scalar_reader_initial_regs bi edge)) b ofs \/ b = buffer.
Proof.
  intros HLength (r & sh & d & ch & HNth & HIn & HBlock & HRange).
  assert (HIndex : (r < 3)%nat).
  { assert (HLen : length (map rshape (sregs (scalar_reader_initial bi edge))) = 3%nat) by reflexivity.
    rewrite <- HLen; apply nth_error_Some; congruence. }
  destruct (lt_dec r 2) as [HSmall|HLarge].
  - left; exists r, sh, d, ch; split.
    + change (nth_error (map rshape (scalar_reader_initial_regs bi edge ++ [scalar_reader_buffer])) r = Some sh) in HNth.
      rewrite map_app, nth_error_app1 in HNth by (cbn [map scalar_reader_initial_regs length]; lia).
      exact HNth.
    + split; [exact HIn|]; split.
      * unfold blk in HBlock; rewrite lay_app_l in HBlock by lia; exact HBlock.
      * unfold bas in HRange; rewrite lay_app_l in HRange by lia; exact HRange.
  - assert (r = 2)%nat by lia; subst r; right.
    unfold blk, lay in HBlock; rewrite app_nth2 in HBlock by lia; rewrite HLength in HBlock.
    exact HBlock.
Qed.

Section READER_CALL.
Variables (m0 : mem) (bd : block) (dbase : Z) (bw : block)
  (outedge cursor N : Z) (bi : block) (edge rc : Z) (ibits : list bool)
  (outs0 : list Simplicity.BitMachine.Cell) (cap : Z).
Hypothesis HOutput : write_frame_at m0 bd dbase bw outedge cursor N.
Hypothesis HInput : frame_input_cells_at m0 bi edge rc (map Some ibits).
Hypothesis HCursor : 0 <= rc.
Hypothesis HCursorMax : rc + Z.of_nat (length ibits) <= Int64.max_unsigned.
Hypothesis HInputLength : length ibits = 256%nat.
Local Definition rd_rho := read_fe_rho ibits rc.
Local Definition rd_inv := invA m0 bd dbase bw outedge cursor N bi rc false outs0 cap.
Local Definition rd_ext := extA m0 bd bw bi.

Theorem eval_scalar_reader_owned m layout :
  rep rd_rho layout (scalar_reader_initial_regs bi (Ptrofs.repr edge)) m ->
  xsep rd_ext layout -> rd_inv rd_rho [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_read_scalar)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))] E0 mf Vundef /\
    rep rd_rho layout (scalar_reader_final_regs bi (Ptrofs.repr edge)) mf /\
    rd_inv rd_rho (scalar_reader_log bi (Ptrofs.repr edge)) mf /\
    lframe (frame rd_ext layout (scalar_reader_initial_regs bi (Ptrofs.repr edge)) m) m mf.
Proof.
  intros HRep HSep HInv.
  assert (HLength : length layout = 2%nat) by (exact (proj1 HRep)).
  destruct (xalloc_sound secp_ge rd_rho (std_cells (genv_cenv secp_ge))
    (fn_vars f_read_scalar) 2 [scalar_reader_buffer] scalar_reader_venv layout
    (scalar_reader_initial_regs bi (Ptrofs.repr edge)) m empty_env
    scalar_reader_allocation HRep HLength ltac:(cbn; constructor; [cbn; tauto|constructor]))
    as (e1 & m1 & betaN & HAlloc & HRep1 & HLenN & HEnv1 & HIdx & HInject & HFresh & HUnchanged1).
  cbn [length] in HLenN.
  destruct betaN as [|[buffer base] betaN]; [discriminate|].
  destruct betaN as [|p betaN]; [|discriminate].
  inversion HFresh as [|? ? HBufferFresh _]; subst.
  set (layout1 := layout ++ [(buffer, base)]) in *.
  assert (HLayout : forall r, (r < 2)%nat -> lay layout1 r = lay layout r).
  { intros r Hr; apply lay_app_l; lia. }
  assert (HBufferBlock : blk layout1 2 = buffer).
  { unfold blk, lay, layout1; rewrite app_nth2 by lia; rewrite HLength; reflexivity. }
  assert (HArgs : map (den rd_rho (lay layout1)) [XP 0 0; XP 1 0] =
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
     Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))]).
  { rewrite (map_den_ext rd_rho (lay layout) (lay layout1) 2 [XP 0 0; XP 1 0]
      HLayout eq_refl).
    cbn [map den]; fold (blk layout 0) (bas layout 0) (blk layout 1) (bas layout 1).
    rewrite !Z.add_0_r; reflexivity. }
  destruct (xbind_sound rd_rho layout1 (fn_params f_read_scalar) [XP 0 0; XP 1 0]
    (PTree.empty sx) scalar_reader_temps (create_undef_temps (fn_temps f_read_scalar))
    eq_refl ltac:(intros id x H; rewrite PTree.gempty in H; discriminate))
    as [le1 [HBind HTemps1]].
  rewrite HArgs in HBind.
  assert (HEnv : ematch layout1 scalar_reader_venv e1).
  { intro id; split.
    - rewrite HEnv1; destruct (vlookup scalar_reader_venv id) as [[r ty]|];
        [reflexivity|apply PTree.gempty].
    - intros r ty HLookup; exact (proj1 (proj2 (proj2 (HIdx id r ty HLookup)))). }
  assert (HSep1 : xsep rd_ext layout1).
  { intros r Hr HExt.
    destruct (lt_dec r 2) as [HSmall|HLarge].
    - apply (HSep r); [lia|]; unfold blk in *; rewrite HLayout in HExt by exact HSmall; exact HExt.
    - assert (r = 2)%nat by (unfold layout1 in Hr; rewrite app_length, HLength in Hr; cbn in Hr; lia).
      subst r; rewrite HBufferBlock in HExt.
      apply HBufferFresh; eapply invA_valid; [exact HInv|exact HExt]. }
  assert (HInv1 : rd_inv rd_rho [] m1).
  { eapply invA_stable; [exact HOutput|exact HInv|].
    apply lframe_unchanged; eapply Mem.unchanged_on_implies; [exact HUnchanged1|]; intros; exact I. }
  destruct (exec_scalar_reader_body m0 bd dbase bw outedge cursor N bi edge rc ibits outs0 cap
    HOutput HInput HCursor HCursorMax HInputLength m1 layout1 e1 le1
    HRep1 HTemps1 HEnv HSep1 HInv1)
    as [le2 [m2 [HBody [HRep2 [HTemps2 [HInv2 HFrame2]]]]]].
  destruct (free_scalar_reader_buffer rd_rho layout1 bi (Ptrofs.repr edge) e1 m2 HRep2 HEnv)
    as [mf [HFree HUnchangedFree]].
  assert (HCallerBeforeFree : rep rd_rho layout (scalar_reader_final_regs bi (Ptrofs.repr edge)) m2).
  { eapply rep_prefix with (βN := [(buffer, base)])
      (regsN := skipn 2 (sregs (scalar_reader_set_state bi (Ptrofs.repr edge)))).
    - unfold scalar_reader_final_regs; rewrite firstn_skipn; exact HRep2.
    - rewrite scalar_reader_final_length; exact HLength. }
  assert (HFinal : rep rd_rho layout (scalar_reader_final_regs bi (Ptrofs.repr edge)) mf).
  { eapply rep_mem; [|exact HCallerBeforeFree].
    eapply Mem.unchanged_on_implies; [exact HUnchangedFree|].
    intros b ofs HIn HValid; rewrite HBufferBlock; intro HEq; subst b.
    apply HBufferFresh; eapply represented_layout_valid; eassumption. }
  assert (HFinalInv : rd_inv rd_rho (scalar_reader_log bi (Ptrofs.repr edge)) mf).
  { eapply invA_stable; [exact HOutput|exact HInv2|].
    apply lframe_unchanged; eapply Mem.unchanged_on_implies; [exact HUnchangedFree|].
    intros b ofs HExt HValid; rewrite HBufferBlock; intro HEq; subst b.
    apply HBufferFresh; eapply invA_valid; [exact HInv|exact HExt]. }
  assert (HFinalFrame : lframe
    (frame rd_ext layout (scalar_reader_initial_regs bi (Ptrofs.repr edge)) m) m mf).
  { eapply lframe_trans.
    - apply lframe_unchanged; eapply Mem.unchanged_on_implies; [exact HUnchanged1|]; intros; exact I.
    - eapply lframe_trans.
      + eapply lframe_implies; [exact HFrame2|].
        intros b ofs [HValidOld [HOutside HNotExt]] HValid1.
        split; [exact HValid1|]; split; [|exact HNotExt].
        intro HFoot; destruct (scalar_reader_foot_extended layout buffer base bi (Ptrofs.repr edge)
          b ofs HLength HFoot) as [HOldFoot|HEq].
        * exact (HOutside HOldFoot).
        * subst b; exact (HBufferFresh HValidOld).
      + apply lframe_unchanged; eapply Mem.unchanged_on_implies; [exact HUnchangedFree|].
        intros b ofs [HValidOld HRest] HValid2; rewrite HBufferBlock; intro HEq; subst b.
        exact (HBufferFresh HValidOld). }
  exists mf; split.
  - eapply eval_funcall_internal with (e := e1) (le1 := le1) (le2 := le2)
      (m1 := m1) (m2 := m2) (out := Out_normal).
    + constructor.
      * cbn; constructor; [cbn; tauto|constructor].
      * cbn; repeat constructor; cbn; intuition discriminate.
      * cbn; intros x y HX HY; contradiction.
      * exact HAlloc.
      * exact HBind.
    + exact HBody.
    + reflexivity.
    + exact HFree.
  - split; [exact HFinal|]; split; assumption.
Qed.
End READER_CALL.

Lemma scalar_reader_final_loads rho layout bi edge m :
  rep rho layout (scalar_reader_final_regs bi edge) m ->
  forall i, (i < 4)%nat ->
    Mem.load Mint64 m (blk layout 0) (bas layout 0 + 8 * Z.of_nat i) =
      Some (Vlong (scalar_reader_limb rho (lay layout) i)).
Proof.
  intro HRep; unfold scalar_reader_final_regs in HRep; rewrite scalar_reader_set_regions in HRep.
  pose proof (rep_region rho layout _ m 0 _ HRep eq_refl) as HR.
  intros i HI; destruct i as [|[|[|[|i]]]]; try lia;
    unfold scalar_reader_limb; cbn [nth];
    match goal with |- Mem.load _ _ _ (_ + ?ofs) = Some (Vlong (il (den _ _ ?x))) =>
      pose proof (region_load rho layout m 0
        (mkreg (map (cell_subst scalar_reader_byte_shift) (cells0 scalar_set_state)) true (Some 32))
        ofs Mint64 x HR ltac:(cbn [rcells]; rewrite scalar_set_output_shape; cbn; auto)) as HL;
      rewrite (den_KL rho (lay layout) x eq_refl) in HL; exact HL
    end.
Qed.

Lemma scalar_reader_final_cursor bits rc layout bi edge m :
  rep (read_fe_rho bits rc) layout (scalar_reader_final_regs bi (Ptrofs.repr edge)) m ->
  frame_fields_at m (blk layout 1) (bas layout 1) bi edge (rc + 256).
Proof.
  intro HRep; unfold scalar_reader_final_regs in HRep; rewrite scalar_reader_set_regions in HRep.
  pose proof (rep_region (read_fe_rho bits rc) layout _ m 1 _ HRep eq_refl) as HR.
  unfold frame_fields_at; split.
  - pose proof (region_load (read_fe_rho bits rc) layout m 1 _ 0 Mint64
      (XA bi (Ptrofs.repr edge)) HR ltac:(left; reflexivity)) as HEdge.
    cbn [den] in HEdge; rewrite Z.add_0_r in HEdge; exact HEdge.
  - pose proof (region_load (read_fe_rho bits rc) layout m 1 _ 8 Mint64
      (XLb Badd (XLv 0) (XLc (Int64.repr 256))) HR
      ltac:(right; left; reflexivity)) as HCursor.
    cbn [den read_fe_rho il] in HCursor; rewrite i64_add_repr in HCursor; exact HCursor.
Qed.

Section READER_VALUE.
Variables (m0 : mem) (bd : block) (dbase : Z) (bw : block)
  (outedge cursor N : Z) (bi : block) (edge rc : Z) (ibits : list bool)
  (outs0 : list Simplicity.BitMachine.Cell) (cap : Z).
Hypothesis HOutput : write_frame_at m0 bd dbase bw outedge cursor N.
Hypothesis HInput : frame_input_cells_at m0 bi edge rc (map Some ibits).
Hypothesis HCursor : 0 <= rc.
Hypothesis HCursorMax : rc + Z.of_nat (length ibits) <= Int64.max_unsigned.
Hypothesis HInputLength : length ibits = 256%nat.
Local Definition value_rho := read_fe_rho ibits rc.
Local Definition value_inv := invA m0 bd dbase bw outedge cursor N bi rc false outs0 cap.
Local Definition value_ext := extA m0 bd bw bi.

Theorem eval_scalar_reader_numeric_owned m layout :
  rep value_rho layout (scalar_reader_initial_regs bi (Ptrofs.repr edge)) m ->
  xsep value_ext layout -> value_inv value_rho [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_read_scalar)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))] E0 mf Vundef /\
    (forall i, (i < 4)%nat ->
      Mem.load Mint64 mf (blk layout 0) (bas layout 0 + 8 * Z.of_nat i) =
        Some (Vlong (scalar_reader_limb value_rho (lay layout) i))) /\
    scalar_limb_value (scalar_reader_limb value_rho (lay layout)) =
      be_val (input_bytes 32 ibits) mod canonical_group_order /\
    frame_fields_at mf (blk layout 1) (bas layout 1) bi edge (rc + 256) /\
    rep value_rho layout (scalar_reader_final_regs bi (Ptrofs.repr edge)) mf /\
    value_inv value_rho (scalar_reader_log bi (Ptrofs.repr edge)) mf /\
    lframe (frame value_ext layout (scalar_reader_initial_regs bi (Ptrofs.repr edge)) m) m mf.
Proof.
  intros HRep HSep HInv.
  destruct (eval_scalar_reader_owned m0 bd dbase bw outedge cursor N bi edge rc ibits outs0 cap
    HOutput HInput HCursor HCursorMax HInputLength m layout HRep HSep HInv)
    as [mf [HCall [HFinal [HFinalInv HFrame]]]].
  exists mf; split; [exact HCall|]; split.
  - apply scalar_reader_final_loads with (bi := bi) (edge := Ptrofs.repr edge); exact HFinal.
  - split; [apply scalar_reader_value_mod_group; exact HInputLength|].
    split; [apply scalar_reader_final_cursor with (bits := ibits); exact HFinal|].
    split; [exact HFinal|]; split; assumption.
Qed.
End READER_VALUE.
