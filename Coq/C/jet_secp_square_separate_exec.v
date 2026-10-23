From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_multiply_run_run C.jet_secp_square_execution.
Require Import C.jet_secp_square_sx_equality C.jet_secp_square_separate_layout C.jet_secp_square_source_list.
Require Import C.jet_secp_square_schedule.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Fixpoint sx_list_same xs ys := match xs,ys with
  | [],[] => true
  | x::xs,y::ys => andb (sx_same x y) (sx_list_same xs ys)
  | _,_ => false
  end.
Lemma sx_list_same_sound xs : forall ys, sx_list_same xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; destruct ys as [|y ys]; cbn [sx_list_same]; try discriminate; intros H.
  - reflexivity.
  - apply Bool.andb_true_iff in H; destruct H as [H1 H2].
    f_equal; [apply sx_same_sound; exact H1|apply IH; exact H2].
Qed.
Definition separate_out writable freed := hd (mkreg [] false None) (sregs (separate_state writable freed)).
Definition separate_limbs writable freed := map field_cell_value (rcells (separate_out writable freed)).
Lemma separate_tail writable freed : tl (sregs (separate_state writable freed)) = [separate_input writable freed].
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma separate_out_shape writable freed : rshape (separate_out writable freed) =
  ([(0,Mint64);(8,Mint64);(16,Mint64);(24,Mint64);(32,Mint64)],true,Some 40).
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma separate_out_defined writable freed : field_cells_defined (rcells (separate_out writable freed)) = true.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma separate_out_rebuild writable freed : separate_out writable freed =
  mkreg (u64_cells 0 (separate_limbs writable freed)) true (Some 40).
Proof.
  pose proof (separate_out_shape writable freed) as HS; pose proof (separate_out_defined writable freed) as HD.
  unfold separate_limbs.
  destruct (separate_out writable freed) as [cs writable' freed']; cbn [rshape rcells rw rfree] in HS.
  injection HS as HC HW HF; subst writable' freed'.
  assert (HN : length cs = 5%nat).
  { apply (f_equal (@length (Z * memory_chunk))) in HC; rewrite map_length in HC; exact HC. }
  f_equal; cbn [rcells].
  apply field_cells_rebuild; [rewrite HN; exact HC|exact HD].
Qed.
(* Keep each checked conversion in its own proof. Closing all five computed
   certificates together needlessly repeats a large conversion at one Qed. *)
Local Lemma separate_r0_source writable freed :
  nth 0 (separate_limbs writable freed) (XLv 0) = sq_r0.
Proof. apply sx_same_sound. Timeout 10 vm_compute. reflexivity. Qed.
Local Lemma separate_r1_source writable freed :
  nth 1 (separate_limbs writable freed) (XLv 0) = sq_r1.
Proof. apply sx_same_sound. Timeout 10 vm_compute. reflexivity. Qed.
Local Lemma separate_r2_source writable freed :
  nth 2 (separate_limbs writable freed) (XLv 0) = sq_r2.
Proof. apply sx_same_sound. Timeout 10 vm_compute. reflexivity. Qed.
Local Lemma separate_r3_source writable freed :
  nth 3 (separate_limbs writable freed) (XLv 0) = sq_r3.
Proof. apply sx_same_sound. Timeout 10 vm_compute. reflexivity. Qed.
Local Lemma separate_r4_source writable freed :
  nth 4 (separate_limbs writable freed) (XLv 0) = sq_r4.
Proof. apply sx_same_sound. Timeout 10 vm_compute. reflexivity. Qed.

Lemma separate_limbs_equal writable freed : separate_limbs writable freed = square_limbs.
Proof.
  rewrite original_square_symbolic_output.
  assert (HL : length (separate_limbs writable freed) = 5%nat).
  { Timeout 10 vm_compute; reflexivity. }
  apply nth_ext with (d := XLv 0) (d' := XLv 0).
  - rewrite HL; reflexivity.
  - intros i HI; rewrite HL in HI.
    destruct i as [|[|[|[|[|i]]]]]; try (exfalso; lia).
    + exact (separate_r0_source writable freed).
    + exact (separate_r1_source writable freed).
    + exact (separate_r2_source writable freed).
    + exact (separate_r3_source writable freed).
    + exact (separate_r4_source writable freed).
Qed.
Lemma separate_output writable freed : sregs (separate_state writable freed) =
  [mkreg (u64_cells 0 square_limbs) true (Some 40); separate_input writable freed].
Proof.
  pose proof (separate_tail writable freed) as HT.
  assert (HNE : sregs (separate_state writable freed) =
    separate_out writable freed :: tl (sregs (separate_state writable freed))).
  { unfold separate_out; destruct (sregs (separate_state writable freed)); [discriminate|reflexivity]. }
  rewrite HNE, separate_tail, separate_out_rebuild, separate_limbs_equal; reflexivity.
Qed.

Local Opaque secp_ge separate_state square_limbs.
Theorem eval_original_square_separate rho layout m writable freed :
  rep rho layout (separate_regs writable freed) m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))] E0 mf Vundef /\
    rep rho layout [mkreg (u64_cells 0 square_limbs) true (Some 40); separate_input writable freed] mf /\
    lframe (fun b ofs => ~ foot layout (map rshape (separate_regs writable freed)) b ofs) m mf.
Proof.
  intro HR.
  destruct (field_fun_sound 400 f_secp256k1_fe_sqr [XP 0 0;XP 1 0]
    (separate_regs writable freed) 5 (RDone (separate_state writable freed) ONormal)
    (separate_run_eq writable freed) rho layout m HR)
    as (mf & vres & HC & HP & HReturn & HShape & HF).
  cbn [rsel fst] in HP, HReturn.
  rewrite separate_return in HReturn; subst vres; rewrite separate_output in HP.
  change (map (den rho (lay layout)) [XP 0 0;XP 1 0]) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0));
     Vptr (blk layout 1) (Ptrofs.repr (bas layout 1 + 0))] in HC.
  rewrite !Z.add_0_r in HC.
  exists mf; split; [exact HC|]; split; assumption.
Qed.
