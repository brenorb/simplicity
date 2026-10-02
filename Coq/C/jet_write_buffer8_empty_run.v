(** Compose the actual empty-buffer loop from its actual writeBit/skipBits
    calls. The subsequent layout consumer must derive those calls initially. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_write_buffer8_empty_exec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition buffer8_empty_index (xs : list Z) := match xs with [] => 0 | j :: _ => j end.
Fixpoint buffer8_empty_chain (xs : list Z) : Prop := match xs with
  | [] => True
  | j :: xs => 0 < j <= Int64.max_unsigned /\ j / 2 = buffer8_empty_index xs /\ buffer8_empty_chain xs
  end.
Fixpoint buffer8_empty_calls bf base (xs : list Z) m mf : Prop := match xs with
  | [] => m = mf
  | j :: xs => exists mb mi,
    Clight2.eval_funcall ge0 m (Internal f_writeBit) [Vptr bf (Ptrofs.repr base); Vint Int.zero] E0 mb (Vint Int.zero) /\
    Clight2.eval_funcall ge0 mb (Internal f_skipBits) [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr (8 * j))] E0 mi Vundef /\
    buffer8_empty_calls bf base xs mi mf
  end.
Definition buffer63_empty_counts : list Z := [32;16;8;4;2;1].

Lemma buffer63_empty_counts_chain : buffer8_empty_chain buffer63_empty_counts.
Proof. vm_compute; repeat split; congruence. Qed.

Lemma empty_loop_from_normal_sequence e le m s1 s2 lenext mn lef mf :
  Clight2.exec_stmt ge0 e le m (Ssequence s1 s2) E0 lenext mn Out_normal ->
  Clight2.exec_stmt ge0 e lenext mn (Sloop s1 s2) E0 lef mf Out_normal ->
  Clight2.exec_stmt ge0 e le m (Sloop s1 s2) E0 lef mf Out_normal.
Proof.
  intros Hstep Hrest. inversion Hstep; subst; [|contradiction].
  match goal with H : _ ** _ = E0 |- _ => apply Eapp_E0_inv in H; destruct H; subst end.
  eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0) (out1 := Out_normal);
    [eassumption|constructor|eassumption|exact Hrest].
Qed.

Theorem exec_buffer8_empty_calls xs le m mf bf base :
  buffer8_empty_chain xs -> le!_dst = Some (Vptr bf (Ptrofs.repr base)) ->
  le!_len = Some (Vlong Int64.zero) -> le!_i = Some (Vlong (Int64.repr (buffer8_empty_index xs))) ->
  buffer8_empty_calls bf base xs m mf ->
  exists lef, Clight2.exec_stmt ge0 empty_env le m buffer8_actual_loop E0 lef mf Out_normal.
Proof.
  revert le m. induction xs as [|j xs IH]; intros le m Hchain HD HL HI Hcalls.
  - change (m = mf) in Hcalls. subst mf. exists le. apply exec_buffer8_empty_stop; exact HI.
  - destruct Hchain as [HJ [Hhalf Hchain]]. destruct Hcalls as (mb & mi & HB & HS & Hcalls).
    set (next := PTree.set _i (Vlong (Int64.repr (j / 2))) (PTree.set _t'2 (Vint Int.zero) le)).
    pose proof (exec_buffer8_empty_iteration empty_env le m mb mi bf base j ltac:(reflexivity)
      ltac:(reflexivity) HD HL HI HJ HB HS) as Hstep.
    assert (HDnext : next!_dst = Some (Vptr bf (Ptrofs.repr base))).
    { unfold next. repeat rewrite PTree.gso by discriminate; exact HD. }
    assert (HLnext : next!_len = Some (Vlong Int64.zero)).
    { unfold next. repeat rewrite PTree.gso by discriminate; exact HL. }
    assert (HInext : next!_i = Some (Vlong (Int64.repr (buffer8_empty_index xs)))).
    { unfold next. rewrite PTree.gss, Hhalf; reflexivity. }
    destruct (IH next mi Hchain HDnext HLnext HInext Hcalls) as (lef & Hloop).
    exists lef. unfold buffer8_loop_body, buffer8_loop_update in Hstep.
    rewrite buffer8_actual_loop_shape in Hstep, Hloop |- *.
    eapply empty_loop_from_normal_sequence; [exact Hstep|exact Hloop].
Qed.
