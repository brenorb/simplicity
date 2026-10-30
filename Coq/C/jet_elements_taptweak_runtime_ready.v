(** Shared initialized readiness at actual linked curve, SHA and tag addresses. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Clight Ctypes Memory Values Globalenvs.
Require Import C.jets_elements C.jet_sx_mem C.jet_clight_internal_preserve
 C.jet_elements_taptweak_program C.jet_elements_taptweak_pure C.jet_elements_taptweak_globals
 C.jet_elements_taptweak_generator_globals C.jet_elements_taptweak_split_constants C.jet_elements_taptweak_beta
 C.jet_elements_taptweak_modinfo C.jet_elements_taptweak_tag_state_at C.jet_secp_taptweak_writer_state.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition elements_taptweak_runtime_tag_block:=elements_taptweak_symbol_block jets_elements._taptweak.
Definition elements_taptweak_curve_state m:=
 (forall high,elements_taptweak_generator_table_state high m) /\elements_taptweak_split_ready m /\
 elements_taptweak_beta_initialized m /\elements_taptweak_modinfo_fe_state m.
Definition elements_taptweak_dispatch_extent m:=Mem.valid_block m elements_taptweak_sha_dispatch_block /\
 block_extent m elements_taptweak_sha_dispatch_block 8.
Definition elements_taptweak_runtime_ready m:=elements_taptweak_curve_state m /\
 elements_taptweak_sha_startup m /\elements_taptweak_tag_state_at elements_taptweak_runtime_tag_block m /\elements_taptweak_dispatch_extent m.
Lemma elements_taptweak_runtime_tag_info:
 Genv.find_var_info(Genv.globalenv elements_taptweak_linked_program)elements_taptweak_runtime_tag_block=
 Some jets_elements.v_taptweak.
Proof. vm_compute;reflexivity. Qed.
Local Opaque elements_taptweak_ge elements_taptweak_linked_program elements_taptweak_runtime_tag_block.
Lemma elements_taptweak_dispatch_extent_initial m:
 Genv.init_mem elements_taptweak_linked_program=Some m ->elements_taptweak_dispatch_extent m.
Proof.
 intro Init;destruct(Genv.init_mem_characterization elements_taptweak_linked_program _
 elements_taptweak_sha_dispatch_info Init)as(Perm & Bounds & Loads & Bytes).
 change(Mem.range_perm m elements_taptweak_sha_dispatch_block 0 8 Cur Writable)in Perm;split.
 - eapply Mem.perm_valid_block;apply(Perm 0);lia.
 - intros pos kind p Permission;exact(proj1(Bounds pos kind p Permission)).
Qed.
Theorem elements_taptweak_runtime_ready_initial m:
 Genv.init_mem elements_taptweak_linked_program=Some m ->elements_taptweak_runtime_ready m.
Proof.
 intro Init;split.
 - split;[intro high;apply elements_taptweak_generator_table_initializes;exact Init|].
   split;[apply elements_taptweak_split_initializes;exact Init|].
   split;[apply elements_taptweak_beta_initialized_from_init;exact Init|apply elements_taptweak_modinfo_initial;exact Init].
 - split;[apply elements_taptweak_sha_startup_initial;exact Init|].
   split;[eapply elements_taptweak_tag_initial_at;[exact elements_taptweak_runtime_tag_info|exact Init]|
    apply elements_taptweak_dispatch_extent_initial;exact Init].
Qed.
Theorem elements_taptweak_curve_state_readonly m mf:
 elements_taptweak_curve_state m ->readonly_preserved m mf ->elements_taptweak_curve_state mf.
Proof.
 intros(Tables & Split & Beta & Modinfo)Read;split.
 - intro high;eapply elements_taptweak_generator_readonly;[apply Tables|exact Read].
 - split;[eapply elements_taptweak_split_readonly;[exact Split|exact Read]|].
   split;[eapply elements_taptweak_beta_initialized_preserved;[exact Beta|exact Read]|
    eapply elements_taptweak_modinfo_readonly;[exact Modinfo|exact Read]].
Qed.
Theorem elements_taptweak_runtime_ready_owned m mf(slots:list(block*Z)):
 elements_taptweak_runtime_ready m ->readonly_preserved m mf ->
 (forall b hi,In(b,hi)slots ->0<hi /\Mem.range_perm m b 0 hi Cur Freeable) ->
 lframe(fun b _=>~In b(map fst slots))m mf ->elements_taptweak_runtime_ready mf.
Proof.
 intros(Curve & SHA & Tag & DispatchValid & DispatchBounds)Read Owned Frame;split.
 - eapply elements_taptweak_curve_state_readonly;[exact Curve|exact Read].
 - split.
   + eapply elements_taptweak_sha_startup_preserved;[exact SHA|exact Read|exact Frame|].
     intros ofs Member;apply in_map_iff in Member.
     destruct Member as([b hi] & Same & Slot);cbn in Same;subst b.
     destruct(Owned _ hi Slot)as[Positive Free].
     exact(proj1(elements_taptweak_sha_startup_separate m _ hi SHA Positive Free)eq_refl).
   + split.
     * eapply elements_taptweak_tag_framed_at;[exact Tag|exact(proj1 Read)|exact Frame|].
       intros ofs Member;apply in_map_iff in Member.
       destruct Member as([b hi] & Same & Slot);cbn in Same;subst b.
       destruct(Owned _ hi Slot)as[Positive Free].
       exact(elements_taptweak_tag_owned_separate_at _ m _ hi Tag Positive Free eq_refl).
     * split;[exact(proj1(proj1 Read _ DispatchValid))|].
       eapply block_extent_forward;[exact DispatchValid|exact DispatchBounds|exact(proj1 Read)].
Qed.
