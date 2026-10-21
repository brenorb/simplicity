(** Selected original C square on either field of a real affine allocation.
    The separate 40-byte output can be uninitialized. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_local_regions.
Require Import C.jet_secp_multiply_run_run C.jet_secp_square_execution C.jet_secp_square_schedule.
Require Import C.jet_secp_square_source_list C.jet_secp_square_sx_equality C.jet_secp_square_separate_exec.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_limbs.

Definition curve_square_offset (y : bool) : Z := if y then 40 else 0.
Definition curve_square_input k :=
  mkreg (u64_cells (curve_square_offset k) (vars5 0)) true (Some 88).
Definition curve_square_regs k :=
  [mkreg (map (fun ofs => mkcell ofs Mint64 None) [0;8;16;24;32]) true (Some 40);
   curve_square_input k].
Definition curve_square_args k := [XP 0 0; XP 1 (curve_square_offset k)].
Definition curve_square_run k := xfun (genv_cenv secp_ge) [] field_table 400
  f_secp256k1_fe_sqr (curve_square_args k) (curve_square_regs k) [] 5.
Definition curve_square_tree := curve_square_run.
Definition curve_square_state k := match curve_square_tree k with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Lemma curve_square_completes k : match curve_square_run k with
  | Some (RDone _ ONormal) => true | _ => false end = true.
Proof. destruct k; timeout 10 (vm_compute; reflexivity). Qed.
Lemma curve_square_run_eq k : curve_square_run k = Some (RDone (curve_square_state k) ONormal).
Proof.
  pose proof (curve_square_completes k) as H. unfold curve_square_state, curve_square_tree.
  destruct (curve_square_run k) as [r|]; [|discriminate].
  destruct r; [destruct o; try discriminate; reflexivity|discriminate].
Qed.
Lemma curve_square_return k : (stemps (curve_square_state k))!1%positive = None.
Proof. destruct k; timeout 10 (vm_compute; reflexivity). Qed.

Definition curve_square_out k := hd (mkreg [] false None) (sregs (curve_square_state k)).
Definition curve_square_limbs k := map field_cell_value (rcells (curve_square_out k)).
Lemma curve_square_tail k : tl (sregs (curve_square_state k)) = [curve_square_input k].
Proof. destruct k; timeout 10 (vm_compute; reflexivity). Qed.
Lemma curve_square_shape k : rshape (curve_square_out k) =
  ([(0,Mint64);(8,Mint64);(16,Mint64);(24,Mint64);(32,Mint64)],true,Some 40).
Proof. destruct k; timeout 10 (vm_compute; reflexivity). Qed.
Lemma curve_square_defined k : field_cells_defined (rcells (curve_square_out k)) = true.
Proof. destruct k; timeout 10 (vm_compute; reflexivity). Qed.
Lemma curve_square_rebuild k : curve_square_out k =
  mkreg (u64_cells 0 (curve_square_limbs k)) true (Some 40).
Proof.
  pose proof (curve_square_shape k) as HS; pose proof (curve_square_defined k) as HD.
  unfold curve_square_limbs.
  destruct (curve_square_out k) as [cs w f]; cbn [rshape rcells rw rfree] in HS.
  injection HS as HC HW HF; subst w f.
  assert (HN : length cs = 5%nat).
  { apply (f_equal (@length (Z * memory_chunk))) in HC; rewrite map_length in HC; exact HC. }
  f_equal; cbn [rcells]. apply field_cells_rebuild; [rewrite HN; exact HC|exact HD].
Qed.
Lemma curve_square_limbs_true : curve_square_limbs true = square_limbs.
Proof.
  rewrite original_square_symbolic_output.
  assert (HL : length (curve_square_limbs true) = 5%nat)
    by (timeout 10 (vm_compute; reflexivity)).
  apply nth_ext with (d := XLv 0) (d' := XLv 0).
  - rewrite HL; reflexivity.
  - intros i HI; rewrite HL in HI.
    destruct i as [|[|[|[|[|i]]]]]; try (exfalso; lia).
    + apply sx_same_sound; timeout 10 (vm_compute; reflexivity).
    + apply sx_same_sound; timeout 10 (vm_compute; reflexivity).
    + apply sx_same_sound; timeout 10 (vm_compute; reflexivity).
    + apply sx_same_sound; timeout 10 (vm_compute; reflexivity).
    + apply sx_same_sound; timeout 10 (vm_compute; reflexivity).
Qed.

Lemma curve_square_limbs_false : curve_square_limbs false = square_limbs.
Proof.
  rewrite original_square_symbolic_output.
  assert (HL : length (curve_square_limbs false) = 5%nat)
    by (timeout 10 (vm_compute; reflexivity)).
  apply nth_ext with (d := XLv 0) (d' := XLv 0).
  - rewrite HL; reflexivity.
  - intros i HI; rewrite HL in HI.
    destruct i as [|[|[|[|[|i]]]]]; try (exfalso; lia).
    + apply sx_same_sound; timeout 10 (vm_compute; reflexivity).
    + apply sx_same_sound; timeout 10 (vm_compute; reflexivity).
    + apply sx_same_sound; timeout 10 (vm_compute; reflexivity).
    + apply sx_same_sound; timeout 10 (vm_compute; reflexivity).
    + apply sx_same_sound; timeout 10 (vm_compute; reflexivity).
Qed.

Lemma curve_square_limbs_equal k : curve_square_limbs k = square_limbs.
Proof. destruct k; [exact curve_square_limbs_true|exact curve_square_limbs_false]. Qed.
Lemma curve_square_output k : sregs (curve_square_state k) =
  [mkreg (u64_cells 0 square_limbs) true (Some 40); curve_square_input k].
Proof.
  assert (HNE : sregs (curve_square_state k) = curve_square_out k :: tl (sregs (curve_square_state k))).
  { pose proof (curve_square_shape k) as HS. unfold curve_square_out in *.
    destruct (sregs (curve_square_state k)); [discriminate HS|reflexivity]. }
  rewrite HNE, curve_square_tail, curve_square_rebuild, curve_square_limbs_equal. reflexivity.
Qed.

Local Opaque curve_square_state.
Theorem eval_curve_square_symbolic k rho layout m : rep rho layout (curve_square_regs k) m ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
     Vptr (blk layout 1) (Ptrofs.repr (bas layout 1 + curve_square_offset k))] E0 mf Vundef /\
  rep rho layout [mkreg (u64_cells 0 square_limbs) true (Some 40); curve_square_input k] mf /\
  lframe (fun b ofs => ~ foot layout (map rshape (curve_square_regs k)) b ofs) m mf.
Proof.
  intro HR.
  destruct (field_fun_sound 400 f_secp256k1_fe_sqr (curve_square_args k) (curve_square_regs k) 5
    (RDone (curve_square_state k) ONormal) (curve_square_run_eq k) rho layout m HR)
    as (mf & result & HC & HF & HRet & HS & HL).
  cbn [rsel fst] in HF, HRet. rewrite curve_square_return in HRet. subst result.
  rewrite curve_square_output in HF.
  change (map (den rho (lay layout)) (curve_square_args k)) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0));
     Vptr (blk layout 1) (Ptrofs.repr (bas layout 1 + curve_square_offset k))] in HC.
  rewrite Z.add_0_r in HC. exists mf. split; [exact HC|]. split; assumption.
Qed.
