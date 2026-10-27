(** Original scalar_add into a distinct uninitialized scalar. The execution
    reuses the same carry/reduction expressions as the in-place proof, while
    retaining both input objects. This is the call shape in split_lambda. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_frame C.jet_secp_shift64_executor
 C.jet_secp_scalar_add_run C.jet_secp_scalar_add_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_add_separate_cells := map (fun c=>mkcell (cofs c) (cchunk c) None)
 (u64_cells 0 [XLv 0;XLv 1;XLv 2;XLv 3]).
Definition scalar_add_separate_initial :=
 mkreg scalar_add_separate_cells true (Some 32) :: scalar_add_initial_regs.
Definition scalar_add_separate_run :=
 xfun (genv_cenv secp_ge) [] secp_shift64_table 1200 f_secp256k1_scalar_add
 [XP 0 0;XP 1 0;XP 2 0] scalar_add_separate_initial [] 8.
Definition scalar_add_separate_tree := Eval vm_compute in scalar_add_separate_run.
Definition scalar_add_separate_state : sstate := match scalar_add_separate_tree with
 | Some (RIf _ (RDone st _) _) => st
 | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition scalar_add_separate_result := RIf scalar_add_condition
 (RDone scalar_add_separate_state ONormal) (RDone scalar_add_separate_state ONormal).

Lemma scalar_add_separate_run_eq : scalar_add_separate_run=Some scalar_add_separate_result.
Proof. reflexivity. Qed.
Lemma scalar_add_separate_output : sregs scalar_add_separate_state=
 mkreg (u64_cells 0 scalar_add_limbs) true (Some 32) :: scalar_add_initial_regs.
Proof. reflexivity. Qed.
Lemma scalar_add_separate_return : (stemps scalar_add_separate_state)!1%positive=Some scalar_add_return_sx.
Proof. reflexivity. Qed.
Lemma scalar_add_separate_selected rho beta :
 rsel rho beta scalar_add_separate_result=(scalar_add_separate_state,ONormal).
Proof.
 change ((if truth rho beta scalar_add_condition then (scalar_add_separate_state,ONormal)
  else (scalar_add_separate_state,ONormal))=(scalar_add_separate_state,ONormal)).
 destruct (truth rho beta scalar_add_condition);reflexivity.
Qed.

Local Opaque secp_ge.
Theorem eval_scalar_add_separate_regions rho beta m :
 rep rho beta scalar_add_separate_initial m ->
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_add)
 [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
  Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
  Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf
 (Vint (ii (den rho (lay beta) scalar_add_return_sx))) /\
 rep rho beta (sregs scalar_add_separate_state) mf /\
 lframe (fun b ofs=>~foot beta (map rshape scalar_add_separate_initial) b ofs) m mf.
Proof.
 intro Rep.
 destruct (xfun_shift64_sound 1200 f_secp256k1_scalar_add [XP 0 0;XP 1 0;XP 2 0]
  scalar_add_separate_initial 8 _ scalar_add_separate_run_eq rho beta m Rep)
  as (mf & vres & Call & Final & Return & Shape & Frame).
 rewrite scalar_add_separate_selected in Final,Return,Shape;cbn [fst] in Final,Return,Shape.
 rewrite scalar_add_separate_return in Return;subst vres.
 rewrite (den_KI rho (lay beta) scalar_add_return_sx scalar_add_return_int) in Call.
 change (map (den rho (lay beta)) [XP 0 0;XP 1 0;XP 2 0]) with
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0));
   Vptr (blk beta 2) (Ptrofs.repr (bas beta 2+0))] in Call.
 rewrite !Z.add_0_r in Call.
 exists mf;split;[exact Call|];split;assumption.
Qed.
