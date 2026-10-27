(** Original three-slice fe_mul with a borrowed, read-only right operand.
    The same actual C body and proved u128 event log are retained. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep
 C.jet_sx_revalue_cells C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_fe_b32 C.jet_secp_b32_exec C.jet_secp_field_add_initial
 C.jet_secp_point_mul_run C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric
 C.jet_secp_u128_word_oracle C.jet_secp_field_mul_word_model C.jet_secp_curve_mul
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_slice_permissions C.jet_clight_internal_permissions.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Require Import C.jet_borrowed_region C.jet_secp_field_slice_product.

Definition field_slice_borrowed_regs := borrow_at 2 field_slice_product_regs.
Definition field_slice_borrowed_args := [XP 0 0;XP 1 0;XP 2 0].
Definition field_slice_borrowed_run := xfun (genv_cenv secp_ge) [] point_mul_table 400
 f_secp256k1_fe_mul field_slice_borrowed_args field_slice_borrowed_regs [] 10.
Definition field_slice_borrowed_tree := Eval vm_compute in field_slice_borrowed_run.
Definition field_slice_borrowed_state := match field_slice_borrowed_tree with
 | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition field_slice_borrowed_out := borrow_at 2 field_slice_product_out.
Lemma field_slice_borrowed_run_eq : field_slice_borrowed_run=Some (RDone field_slice_borrowed_state ONormal).
Proof. reflexivity. Qed.
Lemma field_slice_borrowed_log : slog field_slice_borrowed_state=fe_mul_log.
Proof. reflexivity. Qed.
Lemma field_slice_borrowed_output : sregs field_slice_borrowed_state=field_slice_borrowed_out.
Proof. reflexivity. Qed.
Lemma field_slice_borrowed_return : (stemps field_slice_borrowed_state)!1%positive=None.
Proof. reflexivity. Qed.
Local Opaque field_slice_borrowed_state.

Theorem eval_field_slice_borrowed_symbolic rho beta m :
 rep rho beta field_slice_borrowed_regs m -> Forall (u128_evok rho) fe_mul_log -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
   Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef /\
 rep rho beta field_slice_borrowed_out mf /\
 lframe (fun b pos=>~foot beta (map rshape field_slice_borrowed_regs) b pos) m mf.
Proof.
 intros Initial Solves.
 destruct (xfun_top_sound secp_ge [] point_mul_table u128_evok u128_inv u128_ext
   ltac:(intros;exact I) ltac:(intros;contradiction) point_mul_table_ok 400 f_secp256k1_fe_mul
   field_slice_borrowed_args field_slice_borrowed_regs [] 10
   (RDone field_slice_borrowed_state ONormal) field_slice_borrowed_run_eq rho beta m Initial)
  as (mf & result & Call & Rep & Ret & Shape & _ & Frame).
 - split;intros;discriminate.
 - intros r _ Eq;exact Eq.
 - exact I.
 - cbn [rsel fst];rewrite field_slice_borrowed_log;exact Solves.
 - cbn [rsel fst] in Rep,Ret;rewrite field_slice_borrowed_return in Ret;subst result.
   rewrite field_slice_borrowed_output in Rep.
   change (map (den rho (lay beta)) field_slice_borrowed_args) with
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0));
     Vptr (blk beta 2) (Ptrofs.repr (bas beta 2+0))] in Call.
   rewrite !Z.add_0_r in Call;exists mf;split;[exact Call|];split;[exact Rep|].
   eapply lframe_implies;[exact Frame|].
   intros b pos Outside Valid;split;[exact Valid|];split;[exact Outside|intros Eq;exact Eq].
Qed.


