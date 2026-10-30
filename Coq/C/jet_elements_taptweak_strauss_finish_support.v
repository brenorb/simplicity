(** Linked readonly exceptions and final private-storage layout. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jets_secp C.jet_sx_mem C.jet_secp_linkage C.jet_secp_generator_entry
 C.jet_secp_strauss_scale_function C.jet_secp_generator_function C.jet_secp_generator_globalz_call
 C.jet_secp_generator_preprocess C.jet_secp_strauss_beta_prepare C.jet_secp_strauss_first_loop
 C.jet_elements_taptweak_pure C.jet_elements_taptweak_beta C.jet_elements_taptweak_split_constants
 C.jet_clight_readonly_frame C.jet_clight_internal_preserve.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition elements_taptweak_strauss_readonly_blocks : list block :=
 [elements_taptweak_multiplier_block true;elements_taptweak_multiplier_block false;
  elements_taptweak_basis_block true;elements_taptweak_basis_block false;elements_taptweak_lambda_block;elements_taptweak_beta_block].
Lemma elements_taptweak_strauss_readonly_blocks_not_writable m :
 elements_taptweak_split_ready m -> elements_taptweak_beta_initialized m ->
 forall b,In b elements_taptweak_strauss_readonly_blocks -> forall pos,~Mem.perm m b pos Max Writable.
Proof.
 intros [Multipliers [Basis Lambda]] Beta b Inside pos.
 cbn [elements_taptweak_strauss_readonly_blocks In] in Inside.
 destruct Inside as [At|[At|[At|[At|[At|[At|At]]]]]];try contradiction;subst b.
 - exact (proj2 (Multipliers true) pos).
 - exact (proj2 (Multipliers false) pos).
 - exact (proj2 (Basis true) pos).
 - exact (proj2 (Basis false) pos).
 - exact (proj2 Lambda pos).
 - apply (readonly_bounds_not_writable _ _ _ _ (proj2 Beta)).
Qed.

Lemma elements_taptweak_strauss_prepare_reassociate e le m lef mf :
 Clight2.exec_stmt elements_taptweak_ge e le m strauss_point_prepare E0 lef mf Out_normal ->
 Clight2.exec_stmt elements_taptweak_ge e le m generator_no_points_phase E0 lef mf Out_normal.
Proof.
 intro Run;unfold strauss_point_prepare,strauss_preprocess_finite_statement in Run.
 inversion Run;subst;clear Run;try contradiction.
 match goal with Inner:exec_stmt function_entry2 _ _ _ _ (Ssequence generator_preprocess_statement generator_globalz_statement) _ _ _ Out_normal |- _ =>
  inversion Inner;subst;clear Inner end;try contradiction.
 all:repeat match goal with
 | H : ?t1 ** ?t2 = E0 |- _ => let Parts:=fresh "Parts" in
  pose proof (Eapp_E0_inv t1 t2 H) as Parts;clear H;destruct Parts as [LeftTrace RightTrace];subst
 | H : E0 = ?t1 ** ?t2 |- _ => let Parts:=fresh "Parts" in
  pose proof (Eapp_E0_inv t1 t2 (eq_sym H)) as Parts;clear H;destruct Parts as [LeftTrace RightTrace];subst
 end.
 rewrite generator_no_points_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[eassumption|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[eassumption|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[eassumption|constructor].
Qed.
Lemma elements_taptweak_generator_local_blocks bt bz b0 b128 bw0 bw128 bj bn bl:
 blocks_of_env elements_taptweak_ge(generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl)=
 [(bw128,0,516);(bw0,0,516);(bt,0,88);(bj,0,128);(bz,0,40);(b128,0,32);(b0,0,32);(bn,0,32);(bl,0,32)].
Proof. vm_compute;reflexivity. Qed.
