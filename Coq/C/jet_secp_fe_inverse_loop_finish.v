(** Compose the real field inverse loop with the existing literal finishing
    proof and actual local frees. All terminal coefficient facts are derived. *)
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
Local Opaque secp_ge.

Definition field_inv_loop_finish_frame beta b ofs := field_inv_batch_frame beta b ofs /\
 norm62_outside(blk beta 2)modinfo_fe_block b ofs /\ b<>blk beta 0 /\ inv_free_outside beta b.

Theorem exec_field_inv_loop_finish value n beta e le m len rho :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 0<=value<feP -> field_inv_loop_ready value n beta e le m len rho ->
 blk beta 1=modinfo_fe_block -> bas beta 1=0 -> le!_x=Some(Vptr(blk beta 0)Ptrofs.zero) ->
 exists words lef mf mr,
 Clight2.exec_stmt secp_ge e le m (Ssequence inv_caller_loop inv_finish) E0 lef mf Out_normal /\
 Mem.free_list mf(blocks_of_env secp_ge e)=Some mr /\
 fe_at mr(blk beta 0)0(words5 words) /\ signed62_normalized words /\
 signed62_unsigned_value words=literal_invert_numeric value /\
 (forall input:Ty.tySem(Word 8),value=@toZ (WordToZ 8) input mod feP ->
  @fromZ (WordToZ 8)(signed62_unsigned_value words)=@literal_fe_invert Alg.CoreFunSem input) /\
 Mem.range_perm mr(blk beta 0)0 40 Cur Freeable /\ modinfo_fe_global_rep mr /\
 lframe(field_inv_loop_finish_frame beta) m mr /\ readonly_preserved m mr.
Proof.
 intros CountCall Range Ready Block Base X.
 pose proof Ready as(_ & _ & Env & _ & Modinfo & _).
 destruct(exec_field_inv_loop CountCall value n beta e le m len rho Range Ready)
  as(nf & lenf & rhof & lf & ml & Loop & Progress &
   (Length & Rep & Eta & Len & DE & State & Link & Limbs & Capacity & Low & Zero & Stop) & Temps & Frame & LoopReadonly).
 assert(ModinfoF:lf!_modinfo=Some(Vptr(blk beta 1)(Ptrofs.repr(bas beta 1)))).
 { rewrite(Temps _modinfo) by(unfold inv_post_modified,inv_test_modified,inv_shorten_modified;
   cbn [app In];intuition discriminate);exact Modinfo. }
 assert(XF:lf!_x=Some(Vptr(blk beta 0)Ptrofs.zero)).
 { rewrite(Temps _x) by(unfold inv_post_modified,inv_test_modified,inv_shorten_modified;
   cbn [app In];intuition discriminate);exact X. }
 destruct(exec_inv_finish_literal value nf lenf rhof beta e lf ml Length Rep Env Block Base Len ModinfoF XF
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
     intros b ofs[LoopOutside FinishOutside] Valid;tauto.
   + eapply preserved_trans;[exact LoopReadonly|].
     eapply preserved_trans;[|eapply freelist_preserved;exact Free].
     eapply secp_closed_stmt_preserved;[exact Finish|apply(inv_env_plain beta e Env)|exact secp_closed_finish].
Qed.
