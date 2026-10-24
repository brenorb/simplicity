(** Reuse the existing field-modulus startup state and readonly memory
    preservation. The complete core frame no longer excludes the global. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.Word C.jet_toZ C.jet_predicate_spec.
Require Import C.extraMath C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_modinfo_fe_global C.jet_secp_modinfo_fe_caller C.jet_secp_fe_inverse_core
 C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge C.jet_secp_signed62_numeric
 C.jet_secp_invert_literal C.jet_secp_scalar_io_preserve C.jet_clight_internal_preserve
 C.jet_clight_readonly_frame.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge modinfo_fe_block.

Lemma modinfo_fe_state_preserved m mf : modinfo_fe_state m -> readonly_preserved m mf ->
 modinfo_fe_state mf /\ lframe(fun b _=>b=modinfo_fe_block)m mf.
Proof.
 intros(Global & Readonly) Preserved.
 pose proof(preserved_readonly_block_frame m mf modinfo_fe_block Preserved(proj1 Global)Readonly) as Frame.
 split;[|exact Frame];split.
 - eapply modinfo_fe_global_lframe;[exact Global|exact Frame|];reflexivity.
 - intros ofs Write;apply(Readonly ofs).
   exact(proj2(proj1 Preserved modinfo_fe_block(proj1 Global)) ofs Writable Write).
Qed.

Theorem eval_field_inv_core_initialized w m bs :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 signed62_normalized w -> 0<=signed62_unsigned_value w<feP ->
 bs<>modinfo_fe_block -> fe_at m bs 0(words5 w) -> Mem.range_perm m bs 0 40 Cur Freeable ->
 modinfo_fe_state m -> exists words mr,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_var)
  [Vptr bs Ptrofs.zero;Vptr modinfo_fe_block Ptrofs.zero] E0 mr Vundef /\
 fe_at mr bs 0(words5 words) /\ signed62_normalized words /\
 signed62_unsigned_value words=literal_invert_numeric(signed62_unsigned_value w) /\
 (forall input:Ty.tySem(Word 8),signed62_unsigned_value w=@toZ (WordToZ 8) input mod feP ->
  @fromZ (WordToZ 8)(signed62_unsigned_value words)=@literal_fe_invert Alg.CoreFunSem input) /\
 Mem.range_perm mr bs 0 40 Cur Freeable /\ modinfo_fe_state mr /\
 lframe(fun b _=>b<>bs)m mr /\ readonly_preserved m mr.
Proof.
 intros CountCall Normal Range Sep Input Free Ready.
 destruct(eval_field_inv_core w m bs CountCall Normal Range Sep Input Free(proj1 Ready))
  as(words & mr & Call & Output & OutNormal & Numeric & Literal & Owned & Global & Frame & Preserved).
 destruct(modinfo_fe_state_preserved m mr Ready Preserved) as(ReadyF & GlobalFrame).
 exists words,mr;split;[exact Call|];split;[exact Output|];split;[exact OutNormal|];split;[exact Numeric|];
 split;[exact Literal|];split;[exact Owned|];split;[exact ReadyF|];split;[|exact Preserved].
 eapply lframe_add_block;[exact Frame|exact GlobalFrame|].
 intros b ofs Mod Different;split;assumption.
Qed.
