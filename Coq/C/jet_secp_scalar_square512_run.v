(** Actual scalar_mul_512 with both arguments pointing at one input region.
    The product buffer is fresh and uninitialized. No duplicated ownership. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values
  Maps Memory Events Globalenvs.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec
  C.jet_sx_rep C.jet_sx_mem C.jet_sx_pure C.jet_sx_compact.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_scalar_mul512_run
  C.jet_secp_scalar_mul512_fresh C.jet_secp_symbolic_substitution.
Require Import C.jet_sx_rename.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition square512_rename (n : nat) := (n mod 4)%nat.
Definition scalar_square512_regs : list region :=
  [hd (mkreg [] false None) scalar_mul512_fresh_regs;
   mkreg (u64_cells 0 [XLv 0; XLv 1; XLv 2; XLv 3]) true (Some 32)].
Definition scalar_square512_run :=
  compact_fun (genv_cenv secp_ge) [] (int_table scalar_mul512_functions) 200
    f_secp256k1_scalar_mul_512 [XP 0 0; XP 1 0; XP 1 0]
    scalar_square512_regs [] 16.
Lemma scalar_square512_completes :
  match scalar_square512_run with Some (RDone _ ONormal) => true | _ => false end = true.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Definition scalar_square512_state :=
  match scalar_square512_run with Some (RDone st _) => st
  | _ => mkst (PTree.empty sx) [] [] 0 end.
Lemma scalar_square512_run_eq :
  scalar_square512_run = Some (RDone scalar_square512_state ONormal).
Proof.
  pose proof scalar_square512_completes as H.
  unfold scalar_square512_state; destruct scalar_square512_run as [r|]; [|discriminate].
  destruct r; [destruct o; try discriminate; reflexivity|discriminate].
Qed.
Lemma scalar_square512_return : (stemps scalar_square512_state)!1%positive = None.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma scalar_square512_log_nil : slog scalar_square512_state = [].
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Definition scalar_square512_limbs := map (sx_rename square512_rename) scalar_mul512_limbs.
Definition scalar_square512_output_regs : list region :=
  [mkreg (u64_cells 0 scalar_square512_limbs) true (Some 64);
   mkreg (u64_cells 0 [XLv 0; XLv 1; XLv 2; XLv 3]) true (Some 32)].
Lemma scalar_square512_output : sregs scalar_square512_state = scalar_square512_output_regs.
Proof. Timeout 10 reflexivity. Qed.

Local Opaque scalar_square512_state scalar_mul512_state.
Theorem eval_scalar_square512_fresh rho beta m :
  rep rho beta scalar_square512_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul_512)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
    rep rho beta scalar_square512_output_regs mf /\
    lframe (fun b ofs => ~ foot beta (map rshape scalar_square512_regs) b ofs) m mf.
Proof.
  intro HR.
  destruct (compact_fun_pure secp_ge scalar_mul512_functions scalar_mul512_functions_ok
    200 f_secp256k1_scalar_mul_512 [XP 0 0; XP 1 0; XP 1 0] scalar_square512_regs
    16 (RDone scalar_square512_state ONormal) scalar_square512_run_eq
    ltac:(cbn [leaves_log_nil]; rewrite scalar_square512_log_nil; reflexivity) rho beta m HR)
    as (mf & vres & HC & Hrep & Hreturn & Hshape & Hframe).
  cbn [rsel fst] in Hrep,Hreturn.
  rewrite scalar_square512_return in Hreturn; subst vres.
  rewrite scalar_square512_output in Hrep.
  change (map (den rho (lay beta)) [XP 0 0; XP 1 0; XP 1 0]) with
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0 + 0));
     Vptr (blk beta 1) (Ptrofs.repr (bas beta 1 + 0));
     Vptr (blk beta 1) (Ptrofs.repr (bas beta 1 + 0))] in HC.
  rewrite !Z.add_0_r in HC.
  exists mf; exact (conj HC (conj Hrep Hframe)).
Qed.
