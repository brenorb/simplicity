(** Actual third-fold slice, through c, with typed p0..p4 checkpoint inputs. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight Maps Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_sx_rep.
Require Import C.jet_secp_frame.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix C.jet_secp_shift64_executor.
Require Import C.jet_sx_compact C.jet_secp_scalar_reduce512_run
  C.jet_secp_reduce512_first_run C.jet_secp_reduce512_second_run
  C.jet_secp_reduce512_typed_stage.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition reduce512_third_count := (reduce512_second_count +
  spine_cut_after _c (skipn reduce512_second_count reduce512_spine))%nat.
Definition reduce512_third_spine := firstn reduce512_third_count reduce512_spine.
Definition reduce512_third_prefix := statement_sequence reduce512_third_spine Sskip.
Definition reduce512_third_stage_spine := firstn
  (reduce512_third_count - reduce512_second_count) (skipn reduce512_second_count reduce512_spine).
Definition reduce512_third_stage := statement_sequence reduce512_third_stage_spine Sskip.
Lemma reduce512_third_source :
  statement_sequence reduce512_second_spine reduce512_third_stage = reduce512_third_prefix.
Proof. Timeout 10 reflexivity. Qed.
Lemma reduce512_third_boundary :
  statement_ends_set _c (last reduce512_third_spine Sskip) = true /\
  (reduce512_second_count < reduce512_third_count < length reduce512_spine)%nat.
Proof. Timeout 10 (vm_compute; split; [reflexivity|lia]). Qed.
Section TYPED.
Variable digits : nat -> int64.
Variable p4 : int.
Definition reduce512_third_temps :=
  PTree.set _p4 (XI p4)
  (PTree.set _p3 (XL (digits 3%nat)) (PTree.set _p2 (XL (digits 2%nat))
  (PTree.set _p1 (XL (digits 1%nat)) (PTree.set _p0 (XL (digits 0%nat))
  (PTree.set _l (XP 1 0) (PTree.set _r (XP 0 0) (PTree.empty sx))))))).
Definition reduce512_third_initial := mkst reduce512_third_temps
  (scalar_reduce512_initial_regs ++ fst reduce512_allocated) [] 12.
Definition reduce512_third_run := compact_stmt (genv_cenv secp_ge) [] secp_shift64_table 300
  (snd reduce512_allocated) reduce512_third_initial reduce512_third_stage.
Lemma reduce512_third_completes :
  match reduce512_third_run with Some (RDone _ ONormal) => true | _ => false end = true.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Definition reduce512_third_state :=
  match reduce512_third_run with Some (RDone st _) => st | _ => reduce512_third_initial end.
Lemma reduce512_third_run_eq :
  reduce512_third_run = Some (RDone reduce512_third_state ONormal).
Proof.
  pose proof reduce512_third_completes as H.
  unfold reduce512_third_state; destruct reduce512_third_run as [r|]; [|discriminate].
  destruct r; [destruct o; try discriminate; reflexivity|discriminate].
Qed.
Definition reduce512_third_limbs :=
  map cell_sx (rcells (hd (mkreg [] false None) (sregs reduce512_third_state))).
Definition reduce512_third_c :=
  match (stemps reduce512_third_state)!_c with Some x => x | None => XV Vundef end.
Lemma reduce512_third_log : slog reduce512_third_state = repeat (mkev 0 12 0 []) 3.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma reduce512_third_limb_kinds : forallb (isk KL) reduce512_third_limbs = true.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
End TYPED.
