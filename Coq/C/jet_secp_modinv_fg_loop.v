(** Induction over the actual original inverse transition loop. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_modinv_fg_prefix.
Require Import C.jet_secp_modinv_fg_iteration C.jet_secp_modinv_fg_iteration_prefix C.jet_secp_modinv_fg_index.
Require Import C.jet_secp_modinv_fg_revalue C.jet_secp_multiply_second_temps.
Require Import C.jet_secp_modinv_fg_iteration_numeric.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fg_fixed_bindings :=
 [(_M62,fg_iter_mask);(_r,XLv 13);(_q,XLv 12);(_v,XLv 11);(_u,XLv 10);
  (_len,XL2I (XLv 14));(_t,XP 2 0);(_g,XP 1 0);(_f,XP 0 0)].
Lemma fg_fixed_initial k : fg_iter_temps k=
 PTree.set _i (XIc (Int.repr (Z.of_nat k))) (temps_of fg_fixed_bindings).
Proof. reflexivity. Qed.
Lemma fg_fixed_final k : (0<k<5)%nat ->
 Forall (fun p=>(stemps (fg_iter_final_state k))!(fst p)=Some (snd p)) fg_fixed_bindings.
Proof. destruct k as [|[|[|[|[|k]]]]];intro K;try lia;vm_compute;repeat constructor. Qed.
Lemma fg_final_index k : (0<k<5)%nat ->
 (stemps (fg_iter_final_state k))!_i=Some (XIc (Int.repr (Z.of_nat k))).
Proof. destruct k as [|[|[|[|[|k]]]]];intro K;try lia;vm_compute;reflexivity. Qed.
Lemma fg_fixed_den rho beta k :
 binding_values (fg_next_rho rho k) beta fg_fixed_bindings=binding_values rho beta fg_fixed_bindings.
Proof. reflexivity. Qed.

Lemma fg_iteration_next_temps rho beta le k : (0<k<5)%nat ->
 tmatch rho beta (stemps (fg_iter_final_state k)) le ->
 tmatch (fg_next_rho rho k) beta (fg_iter_temps (S k))
  (PTree.set _i (Vint (Int.repr (Z.of_nat (S k)))) le).
Proof.
 intros K Match;rewrite fg_fixed_initial;apply tmatch_set;apply tmatch_bindings.
 assert (Fixed : Forall (binding_actual rho beta le) fg_fixed_bindings).
 { eapply Forall_impl;[|exact (fg_fixed_final k K)].
   intros [id x] Entry;exact (Match id x Entry). }
 unfold binding_values in *.
 assert (Values : Forall (fun p=>le!(fst p)=Some (snd p))
   (binding_values rho beta fg_fixed_bindings)).
 { unfold binding_values;rewrite Forall_map;exact Fixed. }
 rewrite <-(fg_fixed_den rho beta k) in Values.
 unfold binding_values in Values;rewrite Forall_map in Values;exact Values.
Qed.

Lemma fg_initial_index k : (fg_iter_temps k)!_i=Some (XIc (Int.repr (Z.of_nat k))).
Proof. reflexivity. Qed.
Lemma fg_initial_length k : (fg_iter_temps k)!_len=Some (XL2I (XLv 14)).
Proof. reflexivity. Qed.

Theorem exec_fg_iteration_advance k rho beta e le m : (0<k<5)%nat ->
 rep rho beta fg_iter_regs m -> tmatch rho beta (fg_iter_temps k) le ->
 ematch beta (snd fg_alloc) e -> exists lb lef mf,
 Clight2.exec_stmt secp_ge e le m fg_work E0 lb mf Out_normal /\
 Clight2.exec_stmt secp_ge e lb mf fg_step E0 lef mf Out_normal /\
 rep (fg_next_rho rho k) beta fg_iter_regs mf /\
 tmatch (fg_next_rho rho k) beta (fg_iter_temps (S k)) lef /\
 lframe (fun b ofs=>~foot beta (map rshape fg_iter_regs) b ofs) m mf.
Proof.
 intros K Rep Temps Env.
 destruct (exec_fg_iteration k rho beta e le m K Rep Temps Env)
  as (lb & mf & Body & Out & Match & Frame).
 exists lb,(PTree.set _i (Vint (Int.repr (Z.of_nat (S k)))) lb),mf.
 split;[exact Body|];split.
 - replace (Z.of_nat (S k)) with (Z.of_nat k+1) by lia.
   apply exec_fg_step;[lia|exact (Match _ _ (fg_final_index k K))].
 - split;[exact (fg_iteration_revalue rho beta k mf K Out)|];split;
    [exact (fg_iteration_next_temps rho beta lb k K Match)|exact Frame].
Qed.

Fixpoint fg_loop_rho count rho k := match count with
 | O=>rho | S n=>fg_loop_rho n (fg_next_rho rho k) (S k) end.

Theorem exec_fg_loop_from_body count : forall k rho beta e le m,
 (1<=k)%nat -> (k+count<=5)%nat ->
 Int64.loword (rho 14%nat)=Int.repr (Z.of_nat (k+count)) ->
 rep rho beta fg_iter_regs m -> tmatch rho beta (fg_iter_temps k) le ->
 ematch beta (snd fg_alloc) e -> exists lef mf,
 Clight2.exec_stmt secp_ge e le m fg_loop E0 lef mf Out_normal /\
 rep (fg_loop_rho count rho k) beta fg_iter_regs mf /\
 tmatch (fg_loop_rho count rho k) beta (fg_iter_temps (k+count)) lef /\
 lframe (fun b ofs=>~foot beta (map rshape fg_iter_regs) b ofs) m mf.
Proof.
 induction count as [|count IH];intros k rho beta e le m Start End Len Rep Temps Env.
 - rewrite Nat.add_0_r in Len |- *;cbn [fg_loop_rho].
   exists le,m;split.
   + apply (exec_fg_loop_exit e le m (Z.of_nat k));[lia|exact (Temps _ _ (fg_initial_index k))|].
     rewrite <-Len;exact (Temps _ _ (fg_initial_length k)).
   + split;[exact Rep|];split;[exact Temps|apply lframe_refl].
 - assert (K : (0<k<5)%nat) by lia.
   pose proof (Temps _ _ (fg_initial_index k)) as Index.
   pose proof (Temps _ _ (fg_initial_length k)) as Length.
   change (le!_len=Some (Vint (Int64.loword (rho 14%nat)))) in Length;rewrite Len in Length.
   destruct (exec_fg_iteration_advance k rho beta e le m K Rep Temps Env)
    as (lb & ls & ms & Body & Step & Out & Match & Frame).
   assert (Len' : Int64.loword (fg_next_rho rho k 14%nat)=Int.repr (Z.of_nat (S k+count))).
   { change (Int64.loword (rho 14%nat)=Int.repr (Z.of_nat (S k+count))).
     replace (S k+count)%nat with (k+S count)%nat by lia;exact Len. }
   destruct (IH (S k) (fg_next_rho rho k) beta e ls ms ltac:(lia) ltac:(lia) Len' Out Match Env)
    as (lef & mf & Loop & Final & TFinal & FFinal).
   exists lef,mf;split.
   + rewrite fg_loop_source.
     eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0)
      (le1:=lb) (m1:=ms) (le2:=ls) (m2:=ms) (out1:=Out_normal).
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m);[|exact Body].
       eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
       -- pose proof (eval_fg_guard e le m (Z.of_nat k) (Z.of_nat (k+S count))
           ltac:(lia) ltac:(lia) Index Length) as Guard.
          rewrite (proj2 (Z.ltb_lt (Z.of_nat k) (Z.of_nat (k+S count))) ltac:(lia)) in Guard;exact Guard.
       -- reflexivity.
       -- constructor.
     * constructor.
     * exact Step.
     * exact Loop.
   + split;[exact Final|];split.
     * replace (k+S count)%nat with (S k+count)%nat by lia;exact TFinal.
     * eapply lframe_trans;[exact Frame|exact FFinal].
Qed.
