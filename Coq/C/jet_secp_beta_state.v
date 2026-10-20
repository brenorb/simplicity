(** Non-vacuous initialized beta state survives proved old-readonly preservation. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_clight_readonly_frame.
Require Import C.jet_clight_internal_frame C.jet_secp_beta_global C.jet_clight_internal_preserve C.jet_secp_beta_graph.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque beta_block secp_ge.

Theorem beta_initialized_preserved m mf :
  beta_initialized m -> readonly_preserved m mf -> beta_initialized mf.
Proof.
  intros [[HV [HP HL]] HB] [HForward HU].
  assert (HG : Mem.unchanged_on (fun b _ => b = beta_block) m mf).
  { eapply Mem.unchanged_on_implies; [exact HU|].
    intros b ofs -> HValid; split; [exact HV|].
    intro HW; destruct (proj1 (HB ofs Max Writable) HW) as [_ HO]; inversion HO. }
  pose proof (lframe_unchanged _ _ _ HG) as [HLoads [HPerms HValid]].
  split; [|].
  - split; [exact (HValid beta_block HV)|]; split.
    + intros ofs HOfs; eapply HPerms; [exact HV|reflexivity|apply HP; exact HOfs].
    + intros i w HNth; rewrite HLoads; [exact (HL i w HNth)|exact HV|intros; reflexivity].
  - intros ofs k p; split.
    + intro HF; apply (proj1 (HB ofs k p)).
      eapply Mem.perm_unchanged_on_2; [exact HG|reflexivity|exact HV|exact HF].
    + intro HI; eapply Mem.perm_unchanged_on; [exact HG|reflexivity|apply (proj2 (HB ofs k p)); exact HI].
Qed.

Theorem beta_graph_keeps_state m f args t mf result :
  allowed_call beta_internal_table f -> beta_initialized m ->
  Clight2.eval_funcall secp_ge m f args t mf result -> beta_initialized mf.
Proof.
  intros HA HG HC; eapply beta_initialized_preserved; [exact HG|].
  exact (beta_graph_call_preserves _ _ _ _ _ _ HA HC).
Qed.
