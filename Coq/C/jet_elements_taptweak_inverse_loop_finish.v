(** Linked inverse loop, literal result, and all five actual frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.Word C.jet_toZ C.jet_predicate_spec.
Require Import C.extraMath C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_fe_inverse_loop C.jet_secp_fe_inverse_batch C.jet_secp_modinv_var_entry
 C.jet_secp_modinv_var_de C.jet_secp_modinv_var_fg C.jet_secp_modinv_var_zero
 C.jet_secp_modinv_var_shorten C.jet_secp_modinv_var_post C.jet_secp_modinv_var_tail
 C.jet_secp_modinv_var_invariant C.jet_secp_modinv_var_ranges C.jet_secp_modinv_var_seed
 C.jet_secp_modinv_var_finish C.jet_secp_modinv_var_free C.jet_secp_modinv_var_result
 C.jet_secp_modinv_de_numeric C.jet_secp_modinv_normalize62_exec C.jet_secp_fe_math
 C.jet_secp_modinfo_fe_global C.jet_secp_signed62_numeric C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_invert_literal
 C.jet_secp_closed_helpers C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_elements_taptweak_pure C.jet_elements_taptweak_modinfo C.jet_elements_taptweak_curve_transport
 C.jet_elements_taptweak_internal C.jet_elements_taptweak_inverse_phases C.jet_elements_taptweak_inverse_loop
 C.jet_clight_internal_frame C.jet_ctz_model.
Require Import C.jet_elements_taptweak_inverse_free.
Lemma elements_taptweak_inv_post_keeps_modinfo:~In _modinfo inv_post_modified.
Proof. vm_compute;intuition discriminate. Qed.
Lemma elements_taptweak_inv_post_keeps_x:~In _x inv_post_modified.
Proof. vm_compute;intuition discriminate. Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_modinfo_fe_block elements_taptweak_curve_helpers.

Definition elements_taptweak_field_inv_loop_finish_frame beta b ofs := field_inv_batch_frame beta b ofs /\
 norm62_outside(blk beta 2)elements_taptweak_modinfo_fe_block b ofs /\ b<>blk beta 0 /\ inv_free_outside beta b.

Theorem exec_elements_taptweak_field_inv_loop_finish(Model:ctz_model)value n beta e le m len rho :
 0<=value<feP -> field_inv_loop_ready value n beta e le m len rho ->
 blk beta 1=elements_taptweak_modinfo_fe_block -> bas beta 1=0 -> le!_x=Some(Vptr(blk beta 0)Ptrofs.zero) ->
 exists words lef mf mr,
 Clight2.exec_stmt elements_taptweak_ge e le m (Ssequence inv_caller_loop inv_finish) E0 lef mf Out_normal /\
 Mem.free_list mf(blocks_of_env elements_taptweak_ge e)=Some mr /\
 fe_at mr(blk beta 0)0(words5 words) /\ signed62_normalized words /\
 signed62_unsigned_value words=literal_invert_numeric value /\
 (forall input:Ty.tySem(Word 8),value=@toZ (WordToZ 8) input mod feP ->
  @fromZ (WordToZ 8)(signed62_unsigned_value words)=@literal_fe_invert Alg.CoreFunSem input) /\
 Mem.range_perm mr(blk beta 0)0 40 Cur Freeable /\ elements_taptweak_modinfo_fe_global_rep mr /\
 lframe(elements_taptweak_field_inv_loop_finish_frame beta) m mr /\ readonly_preserved m mr.
Proof.
 intros Range Ready Block Base X.
 pose proof Ready as(_ & _ & Env & _ & Modinfo & _).
 destruct(exec_elements_taptweak_field_inv_loop Model value n beta e le m len rho Range Ready)
  as(nf & lenf & rhof & lf & ml & Loop & Progress &
   (Length & Rep & Eta & Len & DE & State & Link & Limbs & Capacity & Low & Zero & Stop) & Temps & Frame & LoopReadonly).
 assert(ModinfoF:lf!_modinfo=Some(Vptr(blk beta 1)(Ptrofs.repr(bas beta 1)))).
 { rewrite(Temps _modinfo ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) elements_taptweak_inv_post_keeps_modinfo);exact Modinfo. }
 assert(XF:lf!_x=Some(Vptr(blk beta 0)Ptrofs.zero)).
 { rewrite(Temps _x ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) elements_taptweak_inv_post_keeps_x);exact X. }
 destruct(exec_elements_taptweak_inv_finish_literal value nf lenf rhof beta e lf ml Length Rep Env Block Base Len ModinfoF XF
  DE Range Low Link State Stop Zero)
  as(mf & mr & Finish & Free & Output & Normal & Numeric & Original & Owned & Global & FFrame).
 assert(Literal:forall input:Ty.tySem(Word 8),value=@toZ (WordToZ 8) input mod feP ->
  @fromZ (WordToZ 8)(signed62_unsigned_value(inv_finish_words lenf rhof))=
  @literal_fe_invert Alg.CoreFunSem input).
 { intros input Eq;rewrite literal_fe_invert_word;f_equal.
   apply Original;[apply word_value_bounds|exact Eq]. }
 exists(inv_finish_words lenf rhof),(inv_finish_temps lenf rhof lf),mf,mr;split.
 - eapply exec_Sseq_1 with(t1:=E0)(t2:=E0);[exact Loop|exact Finish].
 - split;[exact Free|];split;[exact Output|];split;[exact Normal|];split;[exact Numeric|];
   split;[exact Literal|];split;[exact Owned|];split;[exact Global|];split.
   + eapply lframe_trans;[eapply lframe_implies;[exact Frame|]|eapply lframe_implies;[exact FFrame|]];
     intros b ofs[LoopOutside FinishOutside] Valid;assumption.
   + eapply preserved_trans;[exact LoopReadonly|].
     eapply preserved_trans;[|eapply freelist_preserved;exact Free].
     eapply(proj1(internal_exec_preserved _ _ elements_taptweak_internal_table));
     [exact Finish|apply(inv_env_plain beta e Env)|].
     pose proof elements_taptweak_inverse_phases_closed as Closed;rewrite forallb_forall in Closed;
     apply Closed;unfold elements_taptweak_inverse_pure_phases;right;right;right;left;reflexivity.
Qed.
