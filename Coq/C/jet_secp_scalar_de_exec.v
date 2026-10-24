(** Actual scalar-order coefficient-update call, including allocation/freeing and
    exact output words. The modular-value and range bridge remains separate;
    this execution theorem is not a new registered public jet. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_modinv_fg_iteration_prefix C.jet_secp_modinfo_scalar_global C.jet_secp_modinv_de_exec.
Require Import C.jet_sx_known.
Require Import C.jet_secp_multiply_run_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition scalar_de62_regs :=
 [mkreg (u64_cells 0 [XLv 0;XLv 1;XLv 2;XLv 3;XLv 4]) true (Some 40);
  mkreg (u64_cells 0 [XLv 5;XLv 6;XLv 7;XLv 8;XLv 9]) true (Some 40);
  mkreg (u64_cells 0 [XLv 10;XLv 11;XLv 12;XLv 13]) true (Some 32);
  mkreg (u64_cells 0 (map XLc modinfo_scalar_words)) false None].
Definition scalar_de62_run := known_fun (genv_cenv secp_ge) [] fg_fast_table 400
 f_secp256k1_modinv64_update_de_62 de62_args scalar_de62_regs [] 14.
Definition scalar_de62_run_ok := match scalar_de62_run with Some (RDone _ ONormal)=>true | _=>false end.
Lemma scalar_de62_run_ok_true : scalar_de62_run_ok=true.
Proof. vm_compute;reflexivity. Qed.

Definition scalar_de62_state := match scalar_de62_run with
 | Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end.
Lemma scalar_de62_run_eq : scalar_de62_run=Some (RDone scalar_de62_state ONormal).
Proof.
 pose proof scalar_de62_run_ok_true as Run;unfold scalar_de62_run_ok,scalar_de62_state in *.
 destruct scalar_de62_run as [r|];[|discriminate].
 destruct r;[destruct o;try discriminate;reflexivity|discriminate].
Qed.
Lemma scalar_de62_return : (stemps scalar_de62_state)!1%positive=None.
Proof. vm_compute;reflexivity. Qed.

Definition scalar_de62_out_region (high : bool) := nth (if high then 1 else 0) (sregs scalar_de62_state) (mkreg [] false None).
Definition scalar_de62_limbs (high : bool) := map field_cell_value (rcells (scalar_de62_out_region high)).
Lemma scalar_de62_limbs_properties high : length (scalar_de62_limbs high)=5%nat /\
 forallb (isk KL) (scalar_de62_limbs high)=true /\ forallb (xp_lt 0) (scalar_de62_limbs high)=true.
Proof. destruct high;vm_compute;repeat split;reflexivity. Qed.
Lemma scalar_de62_out_shape high : rshape (scalar_de62_out_region high)=(field_u64_shapes 0 5,true,Some 40).
Proof. destruct high;vm_compute;reflexivity. Qed.
Lemma scalar_de62_out_defined high : field_cells_defined (rcells (scalar_de62_out_region high))=true.
Proof. destruct high;vm_compute;reflexivity. Qed.
Lemma scalar_de62_tail : skipn 2 (sregs scalar_de62_state)=skipn 2 scalar_de62_regs.
Proof. vm_compute;reflexivity. Qed.
Lemma scalar_de62_out_rebuild high : scalar_de62_out_region high=mkreg (u64_cells 0 (scalar_de62_limbs high)) true (Some 40).
Proof.
 pose proof (scalar_de62_out_shape high) as Shape;pose proof (scalar_de62_out_defined high) as Defined.
 unfold scalar_de62_limbs;destruct (scalar_de62_out_region high) as [cells write owned];cbn [rshape rcells rw rfree] in *.
 injection Shape as Cells Write Owned;subst write owned.
 assert (Count : length cells=5%nat).
 { apply (f_equal (@length (Z*memory_chunk))) in Cells;rewrite map_length in Cells;exact Cells. }
 f_equal;apply field_cells_rebuild;[rewrite Count;exact Cells|exact Defined].
Qed.
Lemma scalar_de62_two_heads : sregs scalar_de62_state=scalar_de62_out_region false::scalar_de62_out_region true::skipn 2 (sregs scalar_de62_state).
Proof.
 pose proof scalar_de62_tail as Tail;unfold scalar_de62_out_region;destruct (sregs scalar_de62_state) as [|a [|b rest]];
 [discriminate Tail|discriminate Tail|reflexivity].
Qed.
Lemma scalar_de62_output_regs : sregs scalar_de62_state=
 [mkreg (u64_cells 0 (scalar_de62_limbs false)) true (Some 40);
  mkreg (u64_cells 0 (scalar_de62_limbs true)) true (Some 40);
  nth 2 scalar_de62_regs (mkreg [] false None);nth 3 scalar_de62_regs (mkreg [] false None)].
Proof. rewrite scalar_de62_two_heads,scalar_de62_tail,!scalar_de62_out_rebuild;reflexivity. Qed.

Theorem scalar_eval_de_symbolic rho beta m : rep rho beta scalar_de62_regs m -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_update_de_62)
  (map (den rho (lay beta)) de62_args) E0 mf Vundef /\
 rep rho beta (sregs scalar_de62_state) mf /\
 lframe (fun b ofs=>~foot beta (map rshape scalar_de62_regs) b ofs) m mf.
Proof.
 intro Rep.
 destruct (known_fun_sound secp_ge fg_fast_table fg_fast_table_correct 400
  f_secp256k1_modinv64_update_de_62 de62_args scalar_de62_regs 14 _ scalar_de62_run_eq rho beta m Rep)
  as (mf & vres & Call & Out & Return & Shape & Frame).
 cbn [rsel fst] in Out,Return;rewrite scalar_de62_return in Return;subst vres.
 exists mf;split;[exact Call|];split;[exact Out|exact Frame].
Qed.

Definition scalar_de62_word rho high i := il (den rho (fun _=>(1%positive,0)) (nth i (scalar_de62_limbs high) (XLc Int64.zero))).
Lemma scalar_de62_word_den rho beta high i : (i<5)%nat ->
 den rho beta (nth i (scalar_de62_limbs high) (XLc Int64.zero))=Vlong (scalar_de62_word rho high i).
Proof.
 intro I;destruct (scalar_de62_limbs_properties high) as (Len & Kind & Closed).
 assert (Member : In (nth i (scalar_de62_limbs high) (XLc Int64.zero)) (scalar_de62_limbs high))
  by (apply nth_In;rewrite Len;exact I).
 rewrite forallb_forall in Kind,Closed.
 rewrite (den_ext rho _ (fun _=>(1%positive,0)) beta 0 ltac:(intros;lia) (Closed _ Member)).
 apply den_KL;apply Kind;exact Member.
Qed.
Lemma scalar_de62_output_load rho beta m : rep rho beta (sregs scalar_de62_state) m ->
 forall (high : bool) i,(i<5)%nat ->
 Mem.load Mint64 m (blk beta (if high then 1 else 0))
  (bas beta (if high then 1 else 0)+8*Z.of_nat i)=Some (Vlong (scalar_de62_word rho high i)).
Proof.
 intros Rep high i I;rewrite scalar_de62_output_regs in Rep.
 pose proof (rep_region rho beta _ m (if high then 1%nat else 0%nat)
  (mkreg (u64_cells 0 (scalar_de62_limbs high)) true (Some 40)) Rep ltac:(destruct high;reflexivity)) as Region.
 assert (Nth : nth_error (scalar_de62_limbs high) i=Some (nth i (scalar_de62_limbs high) (XLc Int64.zero))).
 { apply nth_error_nth';rewrite (proj1 (scalar_de62_limbs_properties high));exact I. }
 pose proof (region_load rho beta m _ _ (8*Z.of_nat i) Mint64 _ Region
  ltac:(replace (8*Z.of_nat i) with (0+8*Z.of_nat i) by lia;apply u64_cells_nth;exact Nth)) as Load.
 rewrite scalar_de62_word_den in Load by exact I;exact Load.
Qed.

Theorem scalar_eval_de_words rho beta m : rep rho beta scalar_de62_regs m -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_update_de_62)
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
   Vptr (blk beta 2) (Ptrofs.repr (bas beta 2));Vptr (blk beta 3) (Ptrofs.repr (bas beta 3))] E0 mf Vundef /\
 (forall (high : bool) i,(i<5)%nat -> Mem.load Mint64 mf (blk beta (if high then 1 else 0))
  (bas beta (if high then 1 else 0)+8*Z.of_nat i)=Some (Vlong (scalar_de62_word rho high i))) /\
 rep rho beta (sregs scalar_de62_state) mf /\
 lframe (fun b ofs=>~foot beta (map rshape scalar_de62_regs) b ofs) m mf.
Proof.
 intro Rep;destruct (scalar_eval_de_symbolic rho beta m Rep) as (mf & Call & Out & Frame).
 change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_update_de_62)
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0));
   Vptr (blk beta 2) (Ptrofs.repr (bas beta 2+0));Vptr (blk beta 3) (Ptrofs.repr (bas beta 3+0))] E0 mf Vundef) in Call.
 rewrite !Z.add_0_r in Call.
 exists mf;split;[exact Call|];split;[exact (scalar_de62_output_load rho beta mf Out)|];split;assumption.
Qed.
