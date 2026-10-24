(** Bridge the original normalized reader storage through the real inverse
    to the original wide writer's exact output word. CTZ stays explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.extraMath C.modinv C.jet_word_repr C.jet_toZ C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_b32_exec C.jet_secp_canonical_normalize
 C.jet_secp_multiply_input_input C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge
 C.jet_secp_square_columns C.jet_secp_fe_inv_prefix C.jet_secp_fe_inverse_var
 C.jet_secp_modinfo_fe_caller C.jet_secp_invert_literal C.jet_secp_invert_modinv
 C.jet_secp_write_fe_wide_exec C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_fe_normalize literal_fe_invert.

Lemma literal_fe_invert_normalized_input (value:Ty.tySem(Word 8)) :
 @literal_fe_invert Alg.CoreFunSem (@canonical_fe_normalize Alg.CoreFunSem value)=
 @literal_fe_invert Alg.CoreFunSem value.
Proof.
 rewrite !literal_fe_invert_modInv,canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model.
 f_equal;apply modInv_eqm;unfold eqm;rewrite Z.mod_mod by(unfold feP,feR;lia);reflexivity.
Qed.
Lemma literal_invert_numeric_reduced z : 0<=z<2^256 ->
 literal_invert_numeric z mod feP=literal_invert_numeric z.
Proof.
 intro Range;rewrite literal_invert_numeric_modInv by exact Range.
 unfold modInv;rewrite Z.mod_mod by(unfold feP,feR;lia);reflexivity.
Qed.

Theorem fe_inverse_writer_from_reader m ba (value:Ty.tySem(Word 8)) :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 modinfo_fe_state m ->
 fe_at m ba 0(map Int64.repr(fe_limbs_of
  (@toZ (WordToZ 8)(@canonical_fe_normalize Alg.CoreFunSem value)))) ->
 Mem.range_perm m ba 0 40 Cur Freeable -> exists result mf,
 Clight2.eval_funcall secp_ge m(Internal f_secp256k1_fe_inv_var)
  [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef /\
 fe_at mf ba 0(words5 result) /\ square_input_bounds result /\
 wide_fe_output(result 0%nat)(result 1%nat)(result 2%nat)(result 3%nat)(result 4%nat)=
  @literal_fe_invert Alg.CoreFunSem value /\
 Mem.range_perm mf ba 0 40 Cur Freeable /\ modinfo_fe_state mf /\
 lframe(fun b _=>b<>ba)m mf /\ readonly_preserved m mf.
Proof.
 intros CountCall Ready Input Free.
 set(z:=@toZ (WordToZ 8)(@canonical_fe_normalize Alg.CoreFunSem value)).
 assert(Bounds:square_input_bounds(limb_rho z)).
 { intros i I;pose proof(limb_rho_bound z ltac:(apply word_toZ_range) i) as Bound.
   change(0<=Int64.unsigned(limb_rho z i)<=4503599627370495) in Bound.
   destruct(Nat.eqb i 4);lia. }
 assert(InputR:fe_at m ba 0(words5(limb_rho z))) by exact Input.
 destruct(eval_fe_inverse_var(limb_rho z)m ba ba CountCall Bounds InputR Ready Free)
  as(result & mf & Call & Output & ResultBounds & Numeric & Literal & Owned & ReadyF & Frame & Preserved).
 assert(Word:@fromZ (WordToZ 8)(radix_value result)=@literal_fe_invert Alg.CoreFunSem value).
 { rewrite <-(literal_fe_invert_normalized_input value);apply Literal.
   apply radix_limb_rho;apply word_toZ_range. }
 assert(Reduced:radix_value result mod feP=radix_value result).
 { rewrite Numeric;apply literal_invert_numeric_reduced;exact(proj2(fe_inv_value_range(limb_rho z))). }
 exists result,mf;split;[exact Call|];split;[exact Output|];split;[exact ResultBounds|];split.
 - unfold wide_fe_output;rewrite <-radix_value_matches_normalizer,Reduced;exact Word.
 - split;[exact Owned|];split;[exact ReadyF|];split;assumption.
Qed.
