(** Shared field-call adapter: original optimized square from Z in an owned
    projective object, into a fresh possibly-uninitialized field temporary.
    Reuses the selected square arithmetic, not a new public jet registration. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_local_regions.
Require Import C.jet_secp_fe_b32.
Require Import C.jet_secp_multiply_run_run C.jet_secp_square_execution C.jet_secp_square_columns.
Require Import C.jet_secp_square_sx_equality C.jet_secp_square_source_list.
Require Import C.jet_secp_square_schedule.
Require Import C.jet_secp_square_separate_exec C.jet_secp_square_separate_caller.
Require Import C.jet_secp_square_separate_numeric C.jet_secp_square_numeric.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_point_mul_storage.
Require Import C.jet_secp_b32_exec C.jet_secp_multiply_finish_product C.jet_secp_multiply_checkpoint_columns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition point_square_z_input := mkreg (u64_cells 80 (vars5 0)) true (Some 128).
Definition point_square_z_regs := [free_region fe_undef 40;point_square_z_input].
Definition point_square_z_run := xfun (genv_cenv secp_ge) [] field_table 400
  f_secp256k1_fe_sqr [XP 0 0;XP 1 80] point_square_z_regs [] 5.
Definition point_square_z_state := match point_square_z_run with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition point_square_z_out := hd (mkreg [] false None) (sregs point_square_z_state).
Definition point_square_z_limbs := map field_cell_value (rcells point_square_z_out).

Lemma point_square_z_completes :
  match point_square_z_run with Some (RDone _ ONormal) => true | _ => false end = true.
Proof. vm_compute; reflexivity. Qed.
Lemma point_square_z_run_eq : point_square_z_run = Some (RDone point_square_z_state ONormal).
Proof.
  pose proof point_square_z_completes as H; unfold point_square_z_state.
  destruct point_square_z_run as [r|]; [|discriminate].
  destruct r; [destruct o;try discriminate;reflexivity|discriminate].
Qed.
Lemma point_square_z_return : (stemps point_square_z_state)!1%positive = None.
Proof. vm_compute; reflexivity. Qed.
Lemma point_square_z_tail : tl (sregs point_square_z_state) = [point_square_z_input].
Proof. vm_compute; reflexivity. Qed.
Lemma point_square_z_out_shape : rshape point_square_z_out =
  ([(0,Mint64);(8,Mint64);(16,Mint64);(24,Mint64);(32,Mint64)],true,Some 40).
Proof. vm_compute; reflexivity. Qed.
Lemma point_square_z_out_defined : field_cells_defined (rcells point_square_z_out) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma point_square_z_limb0 : nth 0 point_square_z_limbs (XLv 0) = sq_r0.
Proof. apply sx_same_sound; vm_compute; reflexivity. Qed.
Lemma point_square_z_limb1 : nth 1 point_square_z_limbs (XLv 0) = sq_r1.
Proof. apply sx_same_sound; vm_compute; reflexivity. Qed.
Lemma point_square_z_limb2 : nth 2 point_square_z_limbs (XLv 0) = sq_r2.
Proof. apply sx_same_sound; vm_compute; reflexivity. Qed.
Lemma point_square_z_limb3 : nth 3 point_square_z_limbs (XLv 0) = sq_r3.
Proof. apply sx_same_sound; vm_compute; reflexivity. Qed.
Lemma point_square_z_limb4 : nth 4 point_square_z_limbs (XLv 0) = sq_r4.
Proof. apply sx_same_sound; vm_compute; reflexivity. Qed.
Lemma point_square_z_limbs_equal : point_square_z_limbs = square_limbs.
Proof.
  rewrite original_square_symbolic_output.
  assert (HL : length point_square_z_limbs = 5%nat) by (vm_compute;reflexivity).
  apply nth_ext with (d:=XLv 0) (d':=XLv 0); [rewrite HL;reflexivity|].
  intros i HI; rewrite HL in HI. destruct i as [|[|[|[|[|i]]]]]; try lia;
    first [exact point_square_z_limb0|exact point_square_z_limb1|
      exact point_square_z_limb2|exact point_square_z_limb3|exact point_square_z_limb4].
Qed.
Lemma point_square_z_out_rebuild : point_square_z_out = mkreg (u64_cells 0 square_limbs) true (Some 40).
Proof.
  rewrite <- point_square_z_limbs_equal. unfold point_square_z_limbs.
  pose proof point_square_z_out_shape as HS. pose proof point_square_z_out_defined as HD.
  destruct point_square_z_out as [cs w f]; cbn [rshape rcells rw rfree] in HS.
  injection HS as HC HW HF; subst w f.
  assert (HN : length cs = 5%nat).
  { apply (f_equal (@length (Z * memory_chunk))) in HC; rewrite map_length in HC; exact HC. }
  f_equal; cbn [rcells]. apply field_cells_rebuild; [rewrite HN;exact HC|exact HD].
Qed.
Local Opaque point_square_z_state.
Lemma point_square_z_output : sregs point_square_z_state =
  [mkreg (u64_cells 0 square_limbs) true (Some 40);point_square_z_input].
Proof.
  pose proof point_square_z_tail as HT.
  assert (HNE : sregs point_square_z_state = point_square_z_out :: tl (sregs point_square_z_state)).
  { unfold point_square_z_out; destruct (sregs point_square_z_state) eqn:HE;
      [discriminate HT|reflexivity]. }
  rewrite HNE, point_square_z_tail, point_square_z_out_rebuild; reflexivity.
Qed.

Local Opaque secp_ge point_square_z_state square_limbs square_words.
Theorem eval_point_square_z_symbolic rho layout m : rep rho layout point_square_z_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 1) (Ptrofs.repr (bas layout 1+80))] E0 mf Vundef /\
    rep rho layout [mkreg (u64_cells 0 square_limbs) true (Some 40);point_square_z_input] mf /\
    lframe (fun b pos => ~ foot layout (map rshape point_square_z_regs) b pos) m mf.
Proof.
  intro HR.
  destruct (field_fun_sound 400 f_secp256k1_fe_sqr [XP 0 0;XP 1 80]
    point_square_z_regs 5 (RDone point_square_z_state ONormal) point_square_z_run_eq rho layout m HR)
    as (mf & result & HC & HP & HT & HS & HF).
  cbn [rsel fst] in HP, HT. rewrite point_square_z_return in HT; subst result.
  rewrite point_square_z_output in HP.
  change (map (den rho (lay layout)) [XP 0 0;XP 1 80]) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0+0));
     Vptr (blk layout 1) (Ptrofs.repr (bas layout 1+80))] in HC.
  rewrite Z.add_0_r in HC. exists mf; split; [exact HC|]. split; assumption.
Qed.

Lemma point_square_z_initial rho m bout bin :
  Mem.range_perm m bout 0 40 Cur Freeable -> fe_at m bin 80 (words5 rho) ->
  Mem.range_perm m bin 0 128 Cur Freeable -> bout<>bin ->
  rep rho [(bout,0);(bin,0)] point_square_z_regs m.
Proof.
  intros HO HI HF HNe. apply two_region_rep_separate; [reflexivity|exact HNe| |].
  - change (region_ok rho [(bout,0);(bin,0)] m 0 (free_region fe_undef 40)).
    apply region_with_freeable.
    + apply region_fe_undefined_from_storage; cbn [bas blk lay nth fst snd].
      * lia.
      * exists 0; reflexivity.
      * change (40<=18446744073709551615); lia.
      * apply freeable_range_writable; exact HO.
    + reflexivity.
    + reflexivity.
    + exact HO.
    + apply fe_undef_storage_size.
  - apply owned_field_slice_region; [reflexivity|lia|lia|exact HI|exact HF].
Qed.
Lemma point_square_z_fields rho m mf bout bin :
  square_input_bounds rho -> fe_at m bin 80 (words5 rho) ->
  rep rho [(bout,0);(bin,0)]
    [mkreg (u64_cells 0 square_limbs) true (Some 40);point_square_z_input] mf ->
  fe_at mf bout 0 (words5 (square_words rho)) /\ Mem.range_perm mf bout 0 40 Cur Freeable /\
  fe_at mf bin 80 (words5 rho) /\ Mem.range_perm mf bin 0 128 Cur Freeable.
Proof.
  intros HB HI HR.
  pose proof (rep_region _ _ _ mf 0 _ HR eq_refl) as H0.
  pose proof (rep_region _ _ _ mf 1 _ HR eq_refl) as H1.
  destruct (square_output_region_field rho [(bout,0);(bin,0)] mf 0 HB H0) as [HO HFO].
  pose proof H1 as (_ & _ & _ & _ & _ & _ & HFI & _).
  change (Mem.range_perm mf bin 0 128 Cur Freeable) in HFI.
  split; [exact HO|]. split; [exact HFO|]. split; [|exact HFI].
  destruct HI as (HOfs & HA & HM & _).
  split; [exact HOfs|]. split; [exact HA|]. split; [exact HM|]. split.
  - apply freeable_range_writable. intros pos HPos; apply HFI; lia.
  - intros i x HN.
    assert (HIdx : (i<5)%nat).
    { change (i<length (words5 rho))%nat. apply nth_error_Some; rewrite HN;discriminate. }
    assert (HVars : nth_error (vars5 0) i = Some (XLv i)).
    { destruct i as [|[|[|[|[|i]]]]]; try lia;reflexivity. }
    assert (HX : x=rho i).
    { unfold words5 in HN. destruct i as [|[|[|[|[|i]]]]]; try lia;inversion HN;reflexivity. }
    subst x.
    pose proof (region_load rho [(bout,0);(bin,0)] mf 1 _ _ Mint64 (XLv i) H1
      (u64_cells_nth (vars5 0) 80 i (XLv i) HVars)) as HL.
    change (Mem.load Mint64 mf bin (0+(80+8*Z.of_nat i))=Some (Vlong (rho i))) in HL.
    rewrite Z.add_0_l in HL;exact HL.
Qed.

Theorem eval_point_square_z_from_storage rho m bout bin :
  square_input_bounds rho -> Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin 80 (words5 rho) -> Mem.range_perm m bin 0 128 Cur Freeable -> bout<>bin ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
      [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr 80)] E0 mf Vundef /\
    fe_at mf bout 0 (words5 (square_words rho)) /\ Mem.range_perm mf bout 0 40 Cur Freeable /\
    fe_at mf bin 80 (words5 rho) /\ Mem.range_perm mf bin 0 128 Cur Freeable /\
    radix_value (square_words rho) mod field_prime = (radix_value rho * radix_value rho) mod field_prime /\
    square_input_bounds (square_words rho) /\
    lframe (fun b pos => ~ foot [(bout,0);(bin,0)] (map rshape point_square_z_regs) b pos) m mf.
Proof.
  intros HB HO HI HF HNe.
  destruct (eval_point_square_z_symbolic rho [(bout,0);(bin,0)] m
    (point_square_z_initial rho m bout bin HO HI HF HNe)) as (mf & HC & HR & HFrame).
  destruct (point_square_z_fields rho m mf bout bin HB HI HR) as (HO' & HFO & HI' & HFI).
  exists mf. split; [exact HC|]. split; [exact HO'|]. split; [exact HFO|].
  split; [exact HI'|]. split; [exact HFI|]. split; [apply square_output_numeric;exact HB|].
  split; [apply square_result_reusable;exact HB|exact HFrame].
Qed.
Print Assumptions eval_point_square_z_from_storage.

Lemma point_square_z_foot bout bin b pos :
  foot [(bout,0);(bin,0)] (map rshape point_square_z_regs) b pos ->
    (b=bout /\ 0<=pos<40) \/ (b=bin /\ 80<=pos<120).
Proof.
  intros (r & sh & d & ch & HN & HC & HB & HO).
  destruct r as [|[|r]].
  - left. split; [exact HB|].
    cbn [point_square_z_regs map nth_error rshape rcells rw rfree] in HN; injection HN as <-.
    cbn [fst map cshape cofs cchunk free_region fe_undef rcells] in HC.
    destruct HC as [HC|[HC|[HC|[HC|[HC|HC]]]]]; try contradiction;
      inversion HC; subst d ch; cbn [bas lay nth snd] in HO;
      change (size_chunk Mint64) with 8 in HO; lia.
  - right. split; [exact HB|].
    cbn [point_square_z_regs map nth_error rshape rcells rw rfree] in HN; injection HN as <-.
    cbn [point_square_z_input rcells u64_cells vars5 rshape map cshape cofs cchunk fst] in HC.
    destruct HC as [HC|[HC|[HC|[HC|[HC|HC]]]]]; try contradiction;
      inversion HC; subst d ch; cbn [bas lay nth snd] in HO;
      change (size_chunk Mint64) with 8 in HO; lia.
  - destruct r; discriminate HN.
Qed.
