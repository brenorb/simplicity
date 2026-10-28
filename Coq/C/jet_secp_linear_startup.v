(** Actual readonly constants used by the general linear-combination caller. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Integers Ctypes Clight ClightBigstep Memory Values Globalenvs.
Require Import C.jets_secp C.jet_secp_linkage C.jet_sx_mem C.jet_clight_forward
 C.jet_clight_internal_preserve C.jet_clight_readonly_frame
 C.jet_secp_scale_startup C.jet_secp_strauss_scale_function
 C.jet_secp_split_constants C.jet_secp_split_multipliers C.jet_secp_scalar_lambda_global
 C.jet_secp_beta_global C.jet_secp_beta_state C.jet_secp_generator_globals C.jet_secp_generator_pair_general.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition linear_startup m :=
 split_constants_ready m /\ beta_initialized m /\ (forall h,generator_table_state h m).
Definition linear_startup_blocks :=
 strauss_readonly_blocks++[generator_table_block Datatypes.false;generator_table_block Datatypes.true].
Lemma linear_startup_initializes m : Genv.init_mem jets_secp.prog=Some m -> linear_startup m.
Proof.
 intro Init;split;[apply split_constants_initializes;exact Init|];split.
 - apply beta_initialized_from_init;exact Init.
 - intro h;apply generator_table_initializes;exact Init.
Qed.
Lemma linear_startup_exists : exists m,Genv.init_mem jets_secp.prog=Some m /\ linear_startup m.
Proof.
 destruct generator_tables_initialized_memory_exists as (m & Init & Tables).
 exists m;split;[exact Init|apply linear_startup_initializes;exact Init].
Qed.
Lemma linear_startup_readonly m mf : linear_startup m -> readonly_preserved m mf -> linear_startup mf.
Proof.
 intros (Split & Beta & Tables) Read;split;[eapply split_constants_readonly;eassumption|];split.
 - eapply beta_initialized_preserved;eassumption.
 - eapply generator_tables_readonly;eassumption.
Qed.
Lemma linear_startup_not_writable m : linear_startup m -> forall b,In b linear_startup_blocks ->
 forall pos,~Mem.perm m b pos Max Writable.
Proof.
 intros (Split & Beta & Tables) b Member pos;apply in_app_iff in Member;destruct Member as [RO|Table].
 - exact (strauss_readonly_blocks_not_writable m Split Beta b RO pos).
 - destruct Table as [Same|[Same|[]]];subst b;
   apply (readonly_bounds_not_writable _ _ _ _ (proj2 (Tables _))).
Qed.
Lemma linear_startup_lframe P m mf : linear_startup m -> mem_forward m mf -> lframe P m mf ->
 (forall b,In b linear_startup_blocks -> forall pos,P b pos) -> linear_startup mf.
Proof.
 intros ([Multipliers [Basis Lambda]] & Beta & Tables) Forward Frame Cover.
 assert (CoverRO:forall b,In b strauss_readonly_blocks -> forall pos,P b pos).
 { intros b Slot;apply Cover;apply in_or_app;left;exact Slot. }
 split.
 - split.
   + intro first;eapply scale_scalar_constant_lframe;[apply Multipliers|exact Forward|exact Frame|].
     apply CoverRO;destruct first;cbn [strauss_readonly_blocks In];tauto.
   + split.
     * intro first;eapply scale_scalar_constant_lframe;[apply Basis|exact Forward|exact Frame|].
       apply CoverRO;destruct first;cbn [strauss_readonly_blocks In];tauto.
     * eapply scale_scalar_constant_lframe;[exact Lambda|exact Forward|exact Frame|].
       apply CoverRO;cbn [strauss_readonly_blocks In];tauto.
 - split.
   + eapply scale_beta_lframe;[exact Beta|exact Forward|exact Frame|].
     apply CoverRO;cbn [strauss_readonly_blocks In];tauto.
   + intro h;pose proof (Tables h) as [Table Bounds];pose proof Table as [Valid _].
     assert (Outside:forall pos,P (generator_table_block h) pos).
     { apply Cover;apply in_or_app;right;destruct h;cbn [In];tauto. }
     pose proof (generator_table_rep_lframe h m mf P Table Frame Outside) as Rep.
     split;[exact Rep|];eapply readonly_bounds_transport;
      [exact Valid|exact Bounds|exact Forward|exact (proj1 (proj2 Rep))].
Qed.
Lemma linear_startup_owned_separate m b : linear_startup m -> Mem.perm m b 0 Cur Freeable ->
 forall bg,In bg linear_startup_blocks -> b<>bg.
Proof.
 intros Ready Owned bg Global Same;subst b;apply (linear_startup_not_writable m Ready bg Global 0).
 apply Mem.perm_cur_max;eapply Mem.perm_implies;[exact Owned|constructor].
Qed.
Theorem linear_startup_ecmult_call m mf f args trace result br bk ba bg :
 linear_startup m ->
 (forall b hi,In (b,hi) [(br,128);(bk,32);(ba,128);(bg,32)] -> Mem.range_perm m b 0 hi Cur Freeable) ->
 ClightBigstep.Clight2.eval_funcall secp_ge m f args trace mf result ->
 lframe (fun b _=>~In b [br;bk;ba;bg]) m mf -> linear_startup mf.
Proof.
 intros Ready Owned Call Frame;eapply linear_startup_lframe;[exact Ready| |exact Frame|].
 - exact (proj2 (clight_exec_forward secp_ge) _ _ _ _ _ _ Call).
 - intros global Global pos Member;cbn [In] in Member.
   destruct Member as [Same|[Same|[Same|[Same|[]]]]];
    first [apply (linear_startup_owned_separate m br Ready (Owned br 128 ltac:(cbn [In];tauto) 0 ltac:(lia)) global Global);exact Same|
     apply (linear_startup_owned_separate m bk Ready (Owned bk 32 ltac:(cbn [In];tauto) 0 ltac:(lia)) global Global);exact Same|
     apply (linear_startup_owned_separate m ba Ready (Owned ba 128 ltac:(cbn [In];tauto) 0 ltac:(lia)) global Global);exact Same|
     apply (linear_startup_owned_separate m bg Ready (Owned bg 32 ltac:(cbn [In];tauto) 0 ltac:(lia)) global Global);exact Same].
Qed.
