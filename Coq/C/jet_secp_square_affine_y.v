(** Original optimized square into Y of an owned affine point. This retains
    the actual offset 40 and 88-byte allocation, not a substituted helper. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_local_regions
 C.jet_secp_multiply_run_run C.jet_secp_square_execution C.jet_secp_square_source_list
 C.jet_secp_square_sx_equality C.jet_secp_square_separate_exec.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_limbs.

Definition affine_y_square_input := mkreg (u64_cells 0 (vars5 0)) true (Some 40).
Definition affine_y_square_regs :=
 [mkreg (map (fun ofs=>mkcell ofs Mint64 None) [40;48;56;64;72]) true (Some 88);
  affine_y_square_input].
Definition affine_y_square_args := [XP 0 40;XP 1 0].
Definition affine_y_square_run := xfun (genv_cenv secp_ge) [] field_table 400
 f_secp256k1_fe_sqr affine_y_square_args affine_y_square_regs [] 5.
Definition affine_y_square_state := match affine_y_square_run with
 | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Lemma affine_y_square_completes :
 match affine_y_square_run with Some (RDone _ ONormal) => true | _ => false end=true.
Proof. vm_compute;reflexivity. Qed.
Lemma affine_y_square_run_eq : affine_y_square_run=Some (RDone affine_y_square_state ONormal).
Proof.
 pose proof affine_y_square_completes as Done;unfold affine_y_square_state.
 destruct affine_y_square_run as [r|];[|discriminate].
 destruct r;[destruct o;try discriminate;reflexivity|discriminate].
Qed.
Lemma affine_y_square_return : (stemps affine_y_square_state)!1%positive=None.
Proof. vm_compute;reflexivity. Qed.
Definition affine_y_square_out := hd (mkreg [] false None) (sregs affine_y_square_state).
Definition affine_y_square_limbs := map field_cell_value (rcells affine_y_square_out).
Lemma affine_y_square_tail : tl (sregs affine_y_square_state)=[affine_y_square_input].
Proof. vm_compute;reflexivity. Qed.
Lemma affine_y_square_shape : rshape affine_y_square_out=
 ([(40,Mint64);(48,Mint64);(56,Mint64);(64,Mint64);(72,Mint64)],true,Some 88).
Proof. vm_compute;reflexivity. Qed.
Lemma affine_y_square_defined : field_cells_defined (rcells affine_y_square_out)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma affine_y_square_rebuild : affine_y_square_out=
 mkreg (u64_cells 40 affine_y_square_limbs) true (Some 88).
Proof.
 pose proof affine_y_square_shape as Shape;pose proof affine_y_square_defined as Defined.
 unfold affine_y_square_limbs.
 destruct affine_y_square_out as [cs writable freed];cbn [rshape rcells rw rfree] in Shape.
 injection Shape as Cells W F;subst writable freed.
 assert (Length : length cs=5%nat).
 { apply (f_equal (@length (Z*memory_chunk))) in Cells;rewrite map_length in Cells;exact Cells. }
 f_equal;cbn [rcells];apply field_cells_rebuild;[rewrite Length;exact Cells|exact Defined].
Qed.
Lemma affine_y_square_limb0 : nth 0 affine_y_square_limbs (XLv 0)=nth 0 square_limbs (XLv 0).
Proof. rewrite original_square_symbolic_output;apply sx_same_sound;vm_compute;reflexivity. Qed.
Lemma affine_y_square_limb1 : nth 1 affine_y_square_limbs (XLv 0)=nth 1 square_limbs (XLv 0).
Proof. rewrite original_square_symbolic_output;apply sx_same_sound;vm_compute;reflexivity. Qed.
Lemma affine_y_square_limb2 : nth 2 affine_y_square_limbs (XLv 0)=nth 2 square_limbs (XLv 0).
Proof. rewrite original_square_symbolic_output;apply sx_same_sound;vm_compute;reflexivity. Qed.
Lemma affine_y_square_limb3 : nth 3 affine_y_square_limbs (XLv 0)=nth 3 square_limbs (XLv 0).
Proof. rewrite original_square_symbolic_output;apply sx_same_sound;vm_compute;reflexivity. Qed.
Lemma affine_y_square_limb4 : nth 4 affine_y_square_limbs (XLv 0)=nth 4 square_limbs (XLv 0).
Proof. rewrite original_square_symbolic_output;apply sx_same_sound;vm_compute;reflexivity. Qed.
Lemma affine_y_square_limbs_equal : affine_y_square_limbs=square_limbs.
Proof.
 assert (Length : length affine_y_square_limbs=5%nat) by (vm_compute;reflexivity).
 apply nth_ext with (d:=XLv 0) (d':=XLv 0).
 - rewrite Length;reflexivity.
 - intros i Bound;rewrite Length in Bound.
   destruct i as [|[|[|[|[|i]]]]];try (exfalso;lia).
   + exact affine_y_square_limb0.
   + exact affine_y_square_limb1.
   + exact affine_y_square_limb2.
   + exact affine_y_square_limb3.
   + exact affine_y_square_limb4.
Qed.
Local Opaque affine_y_square_state.
Lemma affine_y_square_output : sregs affine_y_square_state=
 [mkreg (u64_cells 40 square_limbs) true (Some 88);affine_y_square_input].
Proof.
 assert (Nonempty : sregs affine_y_square_state=
   affine_y_square_out::tl (sregs affine_y_square_state)).
 { pose proof affine_y_square_tail as Tail.
   unfold affine_y_square_out;destruct (sregs affine_y_square_state);[discriminate Tail|reflexivity]. }
 rewrite Nonempty,affine_y_square_tail,affine_y_square_rebuild,affine_y_square_limbs_equal;reflexivity.
Qed.

Local Opaque affine_y_square_state.
Theorem eval_square_affine_y_symbolic rho layout m :
 rep rho layout affine_y_square_regs m -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
  [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0+40));
   Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))] E0 mf Vundef /\
 rep rho layout [mkreg (u64_cells 40 square_limbs) true (Some 88);affine_y_square_input] mf /\
 lframe (fun b ofs=>~foot layout (map rshape affine_y_square_regs) b ofs) m mf.
Proof.
 intro Rep.
 destruct (field_fun_sound 400 f_secp256k1_fe_sqr affine_y_square_args affine_y_square_regs 5
  (RDone affine_y_square_state ONormal) affine_y_square_run_eq rho layout m Rep)
  as (mf & result & Call & Final & Return & Shape & Frame).
 cbn [rsel fst] in Final,Return;rewrite affine_y_square_return in Return;subst result.
 rewrite affine_y_square_output in Final.
 change (map (den rho (lay layout)) affine_y_square_args) with
  [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0+40));
   Vptr (blk layout 1) (Ptrofs.repr (bas layout 1+0))] in Call.
 rewrite Z.add_0_r in Call.
 exists mf;split;[exact Call|];split;assumption.
Qed.
