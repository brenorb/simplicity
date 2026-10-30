(** Transport initialized modulus data across private owned argument blocks.
    Readonly state also requires backward maximum-permission preservation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_modinfo_fe_global C.jet_secp_modinfo_fe_caller.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque modinfo_fe_block.
Lemma modinfo_fe_owned_distinct m b hi:
 modinfo_fe_state m ->0<hi ->Mem.range_perm m b 0 hi Cur Freeable ->b<>modinfo_fe_block.
Proof.
 intros [_ Readonly] Positive Free Same;subst b;apply (Readonly 0).
 apply Mem.perm_cur_max;eapply Mem.perm_implies;[apply Free;lia|constructor].
Qed.
Theorem modinfo_fe_global_owned_frame m mf (slots:list (block*Z)):
 modinfo_fe_state m ->
 (forall b hi,In (b,hi) slots ->0<hi /\Mem.range_perm m b 0 hi Cur Freeable) ->
 lframe (fun b _=>~In b (map fst slots)) m mf ->modinfo_fe_global_rep mf.
Proof.
 intros Ready Owned Frame;eapply modinfo_fe_global_lframe;[exact (proj1 Ready)|exact Frame|].
 intros pos Member;apply in_map_iff in Member as ([b hi] & Same & Slot);cbn in Same;subst b.
 destruct (Owned modinfo_fe_block hi Slot) as [Positive Free].
 exact (modinfo_fe_owned_distinct m modinfo_fe_block hi Ready Positive Free eq_refl).
Qed.
Theorem modinfo_fe_state_unchanged m mf:
 modinfo_fe_state m ->Mem.unchanged_on (fun b _=>b=modinfo_fe_block) m mf ->modinfo_fe_state mf.
Proof.
 intros [Global Readonly] Unchanged;split.
 - apply (modinfo_fe_global_unchanged m mf Unchanged Global).
 - intros ofs WritePerm;apply (Readonly ofs).
   eapply Mem.perm_unchanged_on_2;[exact Unchanged|reflexivity|exact (proj1 Global)|exact WritePerm].
Qed.
Require Import C.jet_clight_forward.
Theorem modinfo_fe_state_framed_forward m mf P:
 modinfo_fe_state m ->mem_forward m mf ->lframe P m mf ->
 (forall ofs,P modinfo_fe_block ofs) ->modinfo_fe_state mf.
Proof.
 intros [Global Readonly] Forward Frame Outside;split.
 - eapply modinfo_fe_global_lframe;[exact Global|exact Frame|exact Outside].
 - intros ofs WritePerm;apply (Readonly ofs).
   exact (proj2 (Forward modinfo_fe_block (proj1 Global)) ofs Writable WritePerm).
Qed.
Theorem modinfo_fe_state_owned_frame m mf (slots:list (block*Z)):
 modinfo_fe_state m ->mem_forward m mf ->
 (forall b hi,In (b,hi) slots ->0<hi /\Mem.range_perm m b 0 hi Cur Freeable) ->
 lframe (fun b _=>~In b (map fst slots)) m mf ->modinfo_fe_state mf.
Proof.
 intros Ready Forward Owned Frame;eapply modinfo_fe_state_framed_forward;
 [exact Ready|exact Forward|exact Frame|].
 intros pos Member;apply in_map_iff in Member as ([b hi] & Same & Slot);cbn in Same;subst b.
 destruct (Owned modinfo_fe_block hi Slot) as [Positive Free].
 exact (modinfo_fe_owned_distinct m modinfo_fe_block hi Ready Positive Free eq_refl).
Qed.
