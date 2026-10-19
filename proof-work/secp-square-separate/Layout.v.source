(** The original optimized square into a distinct output region.
    Input ownership is parameterized; the actual input cells are preserved. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_multiply_run_run C.jet_secp_square_execution.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition separate_input writable freed :=
  mkreg (u64_cells 0 [XLv 0;XLv 1;XLv 2;XLv 3;XLv 4]) writable freed.
Definition separate_regs writable freed : list region :=
  [mkreg (map (fun ofs => mkcell ofs Mint64 None) [0;8;16;24;32]) true (Some 40);
   separate_input writable freed].
Definition separate_run writable freed :=
  xfun (genv_cenv secp_ge) [] field_table 400 f_secp256k1_fe_sqr
    [XP 0 0;XP 1 0] (separate_regs writable freed) [] 5.
Lemma separate_completes writable freed :
  match separate_run writable freed with Some (RDone _ ONormal) => true | _ => false end = true.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Definition separate_state writable freed := match separate_run writable freed with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Lemma separate_run_eq writable freed :
  separate_run writable freed = Some (RDone (separate_state writable freed) ONormal).
Proof.
  pose proof (separate_completes writable freed) as H; unfold separate_state.
  destruct (separate_run writable freed) as [r|]; [|discriminate].
  destruct r; [destruct o; try discriminate; reflexivity|discriminate].
Qed.
Lemma separate_return writable freed : (stemps (separate_state writable freed))!1%positive = None.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
