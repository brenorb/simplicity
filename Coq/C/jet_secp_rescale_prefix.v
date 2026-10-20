(** The first two statements of the original gej_rescale body: execute the
    retained zero-check call and square into its distinct local zz.  This is
    a prefix theorem, not a complete gej_rescale jet contract. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix.
Require Import C.jet_secp_multiply_run_run C.jet_secp_multiply_checkpoint_prefix.
Require Import C.jet_secp_square_execution C.jet_secp_square_separate_layout C.jet_secp_square_separate_exec.
Require Import C.jet_secp_square_separate_caller C.jet_secp_square_separate_numeric.
Require Import C.jet_secp_square_numeric C.jet_secp_multiply_checkpoint_columns C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_square_source_list.
Require Import C.jet_secp_square_sx_equality.
Require Import C.jet_secp_square_schedule.
Require Import C.jet_secp_square_columns.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_fe_nv.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition rescale_point_storage := mkreg [] true (Some 128).
Definition rescale_prefix_regs :=
  [rescale_point_storage; separate_input true (Some 40);
   mkreg (map (fun ofs => mkcell ofs Mint64 None) [0;8;16;24;32]) true (Some 40)].
Definition rescale_prefix_temps :=
  PTree.set _s (XP 1 0) (PTree.set _r (XP 0 0) (PTree.empty sx)).
Definition rescale_allocated :=
  match xalloc (std_cells (genv_cenv secp_ge)) (genv_cenv secp_ge)
    (fn_vars f_secp256k1_gej_rescale) 2 with
  | Some p => p | None => ([],[]) end.
Definition rescale_spine := fst (split_statement_last (fn_body f_secp256k1_gej_rescale)).
Definition rescale_prefix := statement_sequence (firstn 2 rescale_spine) Sskip.
Definition rescale_rest := statement_sequence (skipn 2 rescale_spine)
  (snd (split_statement_last (fn_body f_secp256k1_gej_rescale))).
Lemma rescale_prefix_source :
  statement_sequence (firstn 2 rescale_spine) rescale_rest = fn_body f_secp256k1_gej_rescale.
Proof. reflexivity. Qed.

Definition rescale_prefix_initial := mkst rescale_prefix_temps rescale_prefix_regs [] 5.
Definition rescale_prefix_run := xstmt (genv_cenv secp_ge) [] field_table 400
  (snd rescale_allocated) rescale_prefix_initial rescale_prefix.
Lemma rescale_prefix_completes :
  match rescale_prefix_run with Some (RDone _ ONormal) => true | _ => false end = true.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Definition rescale_prefix_state := match rescale_prefix_run with
  | Some (RDone st _) => st | _ => rescale_prefix_initial end.
Lemma rescale_prefix_run_eq :
  rescale_prefix_run = Some (RDone rescale_prefix_state ONormal).
Proof.
  pose proof rescale_prefix_completes as H; unfold rescale_prefix_state.
  destruct rescale_prefix_run as [r|]; [|discriminate].
  destruct r; [destruct o; try discriminate; reflexivity|discriminate].
Qed.

Definition rescale_square_reg := nth 2 (sregs rescale_prefix_state) (mkreg [] false None).
Lemma rescale_prefix_regions : sregs rescale_prefix_state =
  [rescale_point_storage; separate_input true (Some 40); rescale_square_reg].
Proof.
  assert (HN : length (sregs rescale_prefix_state) = 3%nat).
  { Timeout 10 vm_compute; reflexivity. }
  assert (H0 : nth 0 (sregs rescale_prefix_state) (mkreg [] false None) = rescale_point_storage).
  { Timeout 10 vm_compute; reflexivity. }
  assert (H1 : nth 1 (sregs rescale_prefix_state) (mkreg [] false None) = separate_input true (Some 40)).
  { Timeout 10 vm_compute; reflexivity. }
  unfold rescale_square_reg.
  destruct (sregs rescale_prefix_state) as [|r0 [|r1 [|r2 rest]]];
    cbn [length] in HN; try discriminate.
  destruct rest; [|discriminate HN].
  cbn [nth] in H0, H1 |- *; subst r0 r1; reflexivity.
Qed.
Lemma rescale_square_shape : rshape rescale_square_reg =
  ([(0,Mint64);(8,Mint64);(16,Mint64);(24,Mint64);(32,Mint64)],true,Some 40).
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma rescale_square_defined : field_cells_defined (rcells rescale_square_reg) = true.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma rescale_square_r0 : nth 0 (map field_cell_value (rcells rescale_square_reg)) (XLv 0) = sq_r0.
Proof. apply sx_same_sound. Timeout 10 vm_compute; reflexivity. Qed.
Lemma rescale_square_r1 : nth 1 (map field_cell_value (rcells rescale_square_reg)) (XLv 0) = sq_r1.
Proof. apply sx_same_sound. Timeout 10 vm_compute; reflexivity. Qed.
Lemma rescale_square_r2 : nth 2 (map field_cell_value (rcells rescale_square_reg)) (XLv 0) = sq_r2.
Proof. apply sx_same_sound. Timeout 10 vm_compute; reflexivity. Qed.
Lemma rescale_square_r3 : nth 3 (map field_cell_value (rcells rescale_square_reg)) (XLv 0) = sq_r3.
Proof. apply sx_same_sound. Timeout 10 vm_compute; reflexivity. Qed.
Lemma rescale_square_r4 : nth 4 (map field_cell_value (rcells rescale_square_reg)) (XLv 0) = sq_r4.
Proof. apply sx_same_sound. Timeout 10 vm_compute; reflexivity. Qed.
Lemma rescale_square_values : map field_cell_value (rcells rescale_square_reg) = square_limbs.
Proof.
  rewrite original_square_symbolic_output.
  assert (HL : length (map field_cell_value (rcells rescale_square_reg)) = 5%nat).
  { Timeout 10 vm_compute; reflexivity. }
  apply nth_ext with (d := XLv 0) (d' := XLv 0).
  - rewrite HL; reflexivity.
  - intros i HI; rewrite HL in HI.
    destruct i as [|[|[|[|[|i]]]]]; try (exfalso; lia).
    + exact rescale_square_r0.
    + exact rescale_square_r1.
    + exact rescale_square_r2.
    + exact rescale_square_r3.
    + exact rescale_square_r4.
Qed.
Lemma rescale_square_rebuild : rescale_square_reg = mkreg (u64_cells 0 square_limbs) true (Some 40).
Proof.
  pose proof rescale_square_shape as HS; pose proof rescale_square_defined as HD.
  pose proof rescale_square_values as HV.
  destruct rescale_square_reg as [cs w f]; cbn [rshape rcells rw rfree] in HS, HD, HV.
  injection HS as HC HW HF; subst w f.
  assert (HN : length cs = 5%nat).
  { apply (f_equal (@length (Z * memory_chunk))) in HC; rewrite map_length in HC; exact HC. }
  f_equal; rewrite <- HV.
  apply field_cells_rebuild; [rewrite HN; exact HC|exact HD].
Qed.

Local Opaque xstmt rescale_prefix_state rescale_prefix rescale_allocated square_limbs square_words.
Theorem exec_rescale_through_square rho beta e le m :
  rep rho beta rescale_prefix_regs m ->
  tmatch rho beta rescale_prefix_temps le -> ematch beta (snd rescale_allocated) e ->
  exists le' mf,
    Clight2.exec_stmt secp_ge e le m rescale_prefix E0 le' mf Out_normal /\
    rep rho beta [rescale_point_storage; separate_input true (Some 40);
      mkreg (u64_cells 0 square_limbs) true (Some 40)] mf /\
    tmatch rho beta (stemps rescale_prefix_state) le' /\
    map rshape (sregs rescale_prefix_state) = map rshape rescale_prefix_regs /\
    lframe (fun b ofs => ~ foot beta (map rshape rescale_prefix_regs) b ofs) m mf.
Proof.
  intros HR HT HE.
  destruct (field_stmt_normal 400 (snd rescale_allocated) rescale_prefix_initial
    rescale_prefix rescale_prefix_state rescale_prefix_run_eq rho beta e le m HR HT HE)
    as (le' & mf & HX & HP & HT' & HS & HF).
  rewrite rescale_prefix_regions, rescale_square_rebuild in HP.
  exists le', mf; split; [exact HX|]; split; [exact HP|].
  split; [exact HT'|]; split; [exact HS|exact HF].
Qed.

Theorem exec_rescale_square_numeric rho beta e le m :
  square_input_bounds rho -> rep rho beta rescale_prefix_regs m ->
  tmatch rho beta rescale_prefix_temps le -> ematch beta (snd rescale_allocated) e ->
  exists le' mf,
    Clight2.exec_stmt secp_ge e le m rescale_prefix E0 le' mf Out_normal /\
    fe_at mf (blk beta 2) (bas beta 2) (words5 (square_words rho)) /\
    Mem.range_perm mf (blk beta 2) 0 40 Cur Freeable /\
    fe_at mf (blk beta 1) (bas beta 1) (words5 rho) /\
    Mem.range_perm mf (blk beta 1) 0 40 Cur Freeable /\
    Mem.range_perm mf (blk beta 0) 0 128 Cur Freeable /\
    radix_value (square_words rho) mod field_prime =
      (radix_value rho * radix_value rho) mod field_prime /\
    square_input_bounds (square_words rho) /\
    tmatch rho beta (stemps rescale_prefix_state) le' /\
    lframe (fun b ofs => ~ foot beta (map rshape rescale_prefix_regs) b ofs) m mf.
Proof.
  intros HB HR HT HE.
  destruct (exec_rescale_through_square rho beta e le m HR HT HE)
    as (le' & mf & HX & HP & HT' & HS & HF).
  destruct (square_output_region_field rho beta mf 2 HB
    (rep_region _ _ _ mf 2 _ HP eq_refl)) as [HO HOF].
  pose proof (rep_region _ _ _ mf 1 _ HP eq_refl) as HI.
  pose proof (separate_input_field rho beta mf 1 (Some 40) HI) as HIF.
  destruct HI as (_ & _ & _ & _ & _ & _ & HFreeI & _).
  pose proof (rep_region _ _ _ mf 0 _ HP eq_refl) as HPoint.
  destruct HPoint as (_ & _ & _ & _ & _ & _ & HFreeP & _).
  exists le', mf; split; [exact HX|]; split; [exact HO|]; split; [exact HOF|].
  split; [exact HIF|]; split; [exact HFreeI|]; split; [exact HFreeP|].
  split; [apply square_output_numeric; exact HB|].
  split; [apply square_result_reusable; exact HB|]; split; [exact HT'|exact HF].
Qed.
