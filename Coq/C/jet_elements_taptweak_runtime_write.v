(** Preserve linked startup through arbitrary valid 256-bit frame writes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Memory Values Integers.
Require Import C.jet_sx_mem C.jet_clight_internal_preserve C.jet_bitcoin_effects
 C.jet_output_layout C.jet_write_layout C.jet_secp_taptweak_writer_state C.jet_elements_taptweak_globals
 C.jet_elements_taptweak_tag_state_at.
Require Import C.jet_elements_taptweak_runtime_ready.
Local Open Scope Z_scope.
Set Default Timeout 10.
Theorem elements_taptweak_runtime_ready_after_write m mf bd base bw edge cursor cells:
 elements_taptweak_runtime_ready m ->write_frame_at m bd base bw edge cursor 256 ->
 readonly_preserved m mf ->write_effect m mf bd base bw edge cursor 256 cells ->
 elements_taptweak_runtime_ready mf.
Proof.
 intros(Curve & SHA & Tag & ValidD & BoundsD)Frame Read Effect.
 pose proof(write_effect_lframe m mf bd base bw edge cursor 256 cells Effect)as Changes.
 assert(SeparateD:bd<>elements_taptweak_sha_dispatch_block /\bw<>elements_taptweak_sha_dispatch_block).
 { eapply small_block_output_separate with(hi:=8);[lia|exact BoundsD|exact Frame]. }
 split;[eapply elements_taptweak_curve_state_readonly;[exact Curve|exact Read]|].
 split.
 - eapply elements_taptweak_sha_startup_preserved;[exact SHA|exact Read|exact Changes|].
   intros pos;destruct SeparateD as[Dst Word];split;congruence.
 - split.
   + eapply elements_taptweak_tag_after_write_at;[exact Tag|exact Frame|exact Read|exact Effect].
   + split;[exact(proj1(proj1 Read _ ValidD))|].
     eapply block_extent_forward;[exact ValidD|exact BoundsD|exact(proj1 Read)].
Qed.
Theorem elements_taptweak_runtime_ready_entry m mf:
 elements_taptweak_runtime_ready m ->readonly_preserved m mf ->lframe(fun _ _=>True)m mf ->
 elements_taptweak_runtime_ready mf.
Proof.
 intros Ready Read Frame;eapply elements_taptweak_runtime_ready_owned with(slots:=nil);
 [exact Ready|exact Read|intros b hi Impossible;contradiction|].
 eapply lframe_implies;[exact Frame|intros;exact I].
Qed.
