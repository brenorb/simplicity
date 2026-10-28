(** Initialized readonly state for the literal scale caller, established
    from the original program and preserved by actual readers/calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Integers Ctypes Clight ClightBigstep Memory Values Globalenvs.
Require Import C.jets_secp C.jet_sx_mem C.jet_secp_linkage C.jet_clight_forward
 C.jet_clight_internal_preserve C.jet_clight_readonly_frame
 C.jet_secp_strauss_zero_generator C.jet_secp_strauss_scale_main C.jet_secp_strauss_scale_function
 C.jet_secp_scalar_constant C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_add_reader_support
 C.jet_secp_split_constants C.jet_secp_split_multipliers C.jet_secp_scalar_lambda_global
 C.jet_secp_beta_global C.jet_secp_beta_state.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge beta_block strauss_zero_block.

Definition scale_startup m :=
 strauss_zero_global_state m /\ split_constants_ready m /\ beta_initialized m.
Definition scale_startup_blocks := strauss_zero_block::strauss_readonly_blocks.

Definition scale_startup_at (bng:block) m :=
 zero_scalar_state bng m /\ split_constants_ready m /\ beta_initialized m.
Definition scale_startup_blocks_at (bng:block) := bng::strauss_readonly_blocks.

Lemma scale_startup_initializes m :
 Genv.init_mem jets_secp.prog=Some m -> scale_startup m.
Proof.
 intro Init;split;[apply strauss_zero_global_initializes;exact Init|];split;
 [apply split_constants_initializes|apply beta_initialized_from_init];exact Init.
Qed.
Lemma scale_startup_exists : exists m,Genv.init_mem jets_secp.prog=Some m /\ scale_startup m.
Proof.
 destruct strauss_zero_initialized_memory_exists as (m & Init & Zero);
 exists m;split;[exact Init|apply scale_startup_initializes;exact Init].
Qed.
Section Generic_scale_startup_readonly.
Context (bng:block).
Lemma scale_startup_readonly_at m mf :
 (scale_startup_at bng) m -> readonly_preserved m mf -> (scale_startup_at bng) mf.
Proof.
 intros (Zero & Split & Beta) Read;split.
 - eapply (strauss_zero_global_preserved_at bng);[exact Zero|exact Read].
 - split;[eapply split_constants_readonly|eapply beta_initialized_preserved];eassumption.
Qed.
End Generic_scale_startup_readonly.

Lemma scale_startup_readonly m mf :
 scale_startup m -> readonly_preserved m mf -> scale_startup mf.
Proof. exact (@scale_startup_readonly_at strauss_zero_block m mf). Qed.
Section Generic_scale_startup_not_writable.
Context (bng:block).
Lemma scale_startup_not_writable_at m :
 (scale_startup_at bng) m -> forall b,In b (scale_startup_blocks_at bng) ->
 forall pos,~Mem.perm m b pos Max Writable.
Proof.
 intros (Zero & Split & Beta) b [Same|Other] pos.
 - subst b;apply (readonly_bounds_not_writable _ _ _ _ (proj2 Zero)).
 - exact (strauss_readonly_blocks_not_writable m Split Beta b Other pos).
Qed.
End Generic_scale_startup_not_writable.

Lemma scale_startup_not_writable m :
 scale_startup m -> forall b,In b scale_startup_blocks ->
 forall pos,~Mem.perm m b pos Max Writable.
Proof. exact (@scale_startup_not_writable_at strauss_zero_block m). Qed.

Lemma scale_scalar_constant_lframe P m mf b words :
 scalar_constant_state b words m -> mem_forward m mf ->
 lframe P m mf -> (forall pos,P b pos) -> scalar_constant_state b words mf.
Proof.
 intros State Forward Frame Cover;pose proof (scalar_constant_valid b words m State) as Valid.
 destruct State as [Stored NoWrite];split.
 - eapply scalar_at_lframe;[exact Stored|exact Frame|exact Cover].
 - intros pos Write;apply (NoWrite pos);exact (proj2 (Forward b Valid) pos Writable Write).
Qed.

Lemma scale_beta_lframe P m mf :
 beta_initialized m -> mem_forward m mf -> lframe P m mf ->
 (forall pos,P beta_block pos) -> beta_initialized mf.
Proof.
 intros [[Valid [ReadRange Loads]] Bounds] Forward Frame Cover.
 assert (ReadableF:Mem.range_perm mf beta_block 0 40 Cur Readable).
 { intros pos Range;apply (proj1 (proj2 Frame));[exact Valid|apply Cover|apply ReadRange;exact Range]. }
 split.
 - split;[exact (proj1 (Forward beta_block Valid))|];split;[exact ReadableF|].
   intros i w Slot;rewrite (proj1 Frame Mint64 beta_block (8*Z.of_nat i));[exact (Loads i w Slot)|exact Valid|intros;apply Cover].
 - eapply readonly_bounds_transport;[exact Valid|exact Bounds|exact Forward|exact ReadableF].
Qed.

Section Generic_scale_startup_lframe.
Context (bng:block).
Lemma scale_startup_lframe_at P m mf :
 (scale_startup_at bng) m -> mem_forward m mf -> lframe P m mf ->
 (forall b,In b (scale_startup_blocks_at bng) -> forall pos,P b pos) -> (scale_startup_at bng) mf.
Proof.
 intros (Zero & [Multipliers [Basis Lambda]] & Beta) Forward Frame Cover.
 assert (CoverZ:forall pos,P bng pos) by
  (apply Cover;left;reflexivity).
 assert (CoverRO:forall b,In b strauss_readonly_blocks -> forall pos,P b pos) by
  (intros b Slot;apply Cover;right;exact Slot).
 split.
 - pose proof ((strauss_zero_global_valid_at bng) m Zero) as Valid;destruct Zero as [Stored Bounds].
   assert (StoredF:scalar_at mf bng 0 [Int64.zero;Int64.zero;Int64.zero;Int64.zero]).
   { eapply scalar_at_lframe;[exact Stored|exact Frame|exact CoverZ]. }
   split;[exact StoredF|];eapply readonly_bounds_transport;[exact Valid|exact Bounds|exact Forward|].
   exact (proj1 (proj2 (proj2 (proj2 (proj2 StoredF))))).
 - split.
   + split.
     * intro first;eapply scale_scalar_constant_lframe;[apply Multipliers|exact Forward|exact Frame|].
       apply CoverRO;destruct first;cbn [strauss_readonly_blocks In];tauto.
     * split.
       -- intro first;eapply scale_scalar_constant_lframe;[apply Basis|exact Forward|exact Frame|].
          apply CoverRO;destruct first;cbn [strauss_readonly_blocks In];tauto.
       -- eapply scale_scalar_constant_lframe;[exact Lambda|exact Forward|exact Frame|].
          apply CoverRO;cbn [strauss_readonly_blocks In];tauto.
   + eapply scale_beta_lframe;[exact Beta|exact Forward|exact Frame|].
     apply CoverRO;cbn [strauss_readonly_blocks In];tauto.
Qed.
End Generic_scale_startup_lframe.

Lemma scale_startup_lframe P m mf :
 scale_startup m -> mem_forward m mf -> lframe P m mf ->
 (forall b,In b scale_startup_blocks -> forall pos,P b pos) -> scale_startup mf.
Proof. exact (@scale_startup_lframe_at strauss_zero_block P m mf). Qed.

Section Generic_scale_startup_owned_separate.
Context (bng:block).
Lemma scale_startup_owned_separate_at m b :
 (scale_startup_at bng) m -> Mem.perm m b 0 Cur Freeable ->
 forall bg,In bg (scale_startup_blocks_at bng) -> b<>bg.
Proof.
 intros Ready Owned bg Global Same;subst b;apply ((scale_startup_not_writable_at bng) m Ready bg Global 0).
 apply Mem.perm_cur_max;eapply Mem.perm_implies;[exact Owned|constructor].
Qed.
End Generic_scale_startup_owned_separate.

Lemma scale_startup_owned_separate m b :
 scale_startup m -> Mem.perm m b 0 Cur Freeable ->
 forall bg,In bg scale_startup_blocks -> b<>bg.
Proof. exact (@scale_startup_owned_separate_at strauss_zero_block m b). Qed.

Section Generic_scale_startup_ecmult_call.
Context (bng:block).
Theorem scale_startup_ecmult_call_at m mf f args trace result br bk ba :
 (scale_startup_at bng) m ->
 (forall b hi,In (b,hi) [(br,128);(bk,32);(ba,128)] -> Mem.range_perm m b 0 hi Cur Freeable) ->
 Clight2.eval_funcall secp_ge m f args trace mf result ->
 lframe (fun b _=>~In b [br;bk;ba]) m mf -> (scale_startup_at bng) mf.
Proof.
 intros Ready Owned Call Frame;eapply (scale_startup_lframe_at bng);[exact Ready| |exact Frame|].
 - exact (proj2 (clight_exec_forward secp_ge) _ _ _ _ _ _ Call).
 - intros bg Global pos [Same|[Same|[Same|[]]]].
   + apply ((scale_startup_owned_separate_at bng) m br Ready
      (Owned br 128 ltac:(cbn [In];tauto) 0 ltac:(lia)) bg Global);exact Same.
   + apply ((scale_startup_owned_separate_at bng) m bk Ready
      (Owned bk 32 ltac:(cbn [In];tauto) 0 ltac:(lia)) bg Global);exact Same.
   + apply ((scale_startup_owned_separate_at bng) m ba Ready
      (Owned ba 128 ltac:(cbn [In];tauto) 0 ltac:(lia)) bg Global);exact Same.
Qed.
End Generic_scale_startup_ecmult_call.

Theorem scale_startup_ecmult_call m mf f args trace result br bk ba :
 scale_startup m ->
 (forall b hi,In (b,hi) [(br,128);(bk,32);(ba,128)] -> Mem.range_perm m b 0 hi Cur Freeable) ->
 Clight2.eval_funcall secp_ge m f args trace mf result ->
 lframe (fun b _=>~In b [br;bk;ba]) m mf -> scale_startup mf.
Proof. exact (@scale_startup_ecmult_call_at strauss_zero_block m mf f args trace result br bk ba). Qed.
