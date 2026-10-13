(** Exact execution tree of the unchanged original in-place scalar addition.
    The two owned scalar regions match the public caller's distinct locals.
    This is helper execution, not yet the public implementation-to-spec proof. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Integers Values Maps.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_frame.
Require Import C.jet_secp_shift64_executor.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_add_initial_regs : list region :=
  [mkreg (u64_cells 0 [XLv 0; XLv 1; XLv 2; XLv 3]) true (Some 32);
   mkreg (u64_cells 0 [XLv 4; XLv 5; XLv 6; XLv 7]) true (Some 32)].
Definition scalar_add_run : option res :=
  xfun (genv_cenv secp_ge) [] secp_shift64_table 1200 f_secp256k1_scalar_add
    [XP 0 0; XP 0 0; XP 1 0] scalar_add_initial_regs [] 8.
Definition scalar_add_tree := Eval vm_compute in scalar_add_run.
Definition scalar_add_state : sstate :=
  match scalar_add_tree with Some (RDone state _) => state
  | Some (RIf _ (RDone state _) _) => state
  | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition scalar_add_condition : sx :=
  match scalar_add_tree with Some (RIf c _ _) => c | _ => XIc Int.zero end.
Definition scalar_add_result : res :=
  RIf scalar_add_condition (RDone scalar_add_state ONormal) (RDone scalar_add_state ONormal).
Definition scalar_add_return_sx : sx :=
  match (stemps scalar_add_state)!1%positive with Some x => x | None => XV Vundef end.

Lemma scalar_add_run_eq : scalar_add_run = Some scalar_add_result.
Proof. reflexivity. Qed.
Lemma scalar_add_selected rho beta :
  rsel rho beta scalar_add_result = (scalar_add_state, ONormal).
Proof.
  change ((if truth rho beta scalar_add_condition then (scalar_add_state, ONormal)
    else (scalar_add_state, ONormal)) = (scalar_add_state, ONormal)).
  destruct (truth rho beta scalar_add_condition); reflexivity.
Qed.
Lemma scalar_add_return : (stemps scalar_add_state)!1%positive = Some scalar_add_return_sx.
Proof. reflexivity. Qed.
Lemma scalar_add_output_shape :
  exists limbs, length limbs = 4%nat /\
    sregs scalar_add_state =
      [mkreg (u64_cells 0 limbs) true (Some 32);
       mkreg (u64_cells 0 [XLv 4; XLv 5; XLv 6; XLv 7]) true (Some 32)].
Proof.
  exists (map cell_sx (rcells (hd (mkreg [] false None) (sregs scalar_add_state))));
    split; reflexivity.
Qed.
Lemma scalar_add_caller_owned :
  length (sregs scalar_add_state) = 2%nat /\
  rfree (nth 0 (sregs scalar_add_state) (mkreg [] false None)) = Some 32 /\
  rfree (nth 1 (sregs scalar_add_state) (mkreg [] false None)) = Some 32.
Proof. repeat split; reflexivity. Qed.
