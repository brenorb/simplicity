(** Interpret the actual scalar inverse finishing execution against the
    literal Simplicity scalar_invert. Terminal trajectory and coefficient
    facts are internal loop obligations, not extra public-jet assumptions. *)
From Coq Require Import ZArith Znumtheory List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.Word C.jet_toZ C.jet_predicate_spec.
Require Import C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_scalar_inverse_finish C.jet_secp_scalar_invert_literal
 C.jet_secp_modinfo_scalar_global C.jet_secp_scalar_inverse_caller C.jet_secp_canonical_scalar
 C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_de C.jet_secp_modinv_var_finish
 C.jet_secp_modinv_var_free C.jet_secp_modinv_var_result C.jet_secp_modinv_normalize62_exec
 C.jet_secp_modinv_normalize62_modulus C.jet_secp_modinv_normalize62_words
 C.jet_secp_signed62_numeric C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge C.modinv C.divstep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma scalar_inv_modulus_odd : Zodd canonical_group_order.
Proof. vm_compute;exact I. Qed.

Lemma scalar_inv_finish_abs_value len fw : (0<len<=5)%nat ->
 (forall i,(i<(len-1))%nat -> 0<=Int64.signed(fw i)<2^62) ->
 (if Int64.lt (fw (len-1)%nat) Int64.zero then -1 else 1)*
   norm62_value_z (len-1)%nat (fun i=>Int64.signed(fw i))=
 Z.abs(norm62_value_z (len-1)%nat (fun i=>Int64.signed(fw i))).
Proof.
 intros Len Low.
 pose proof(inv_active_negative_top (len-1) (fun i=>Int64.signed(fw i)) Low) as Sign.
 unfold Int64.lt;rewrite Int64.signed_zero.
 destruct(zlt (Int64.signed(fw (len-1)%nat)) 0) as [Negative|Nonnegative].
 - rewrite Z.abs_neq by (pose proof(proj2 Sign Negative);lia);ring.
 - rewrite Z.abs_eq by (destruct(Z_lt_ge_dec (norm62_value_z (len-1)%nat
     (fun i=>Int64.signed(fw i))) 0) as [Neg|Nonneg];[apply Sign in Neg;lia|lia]);ring.
Qed.

Lemma scalar_inv_terminal_literal value n len d fw : 0<=value<canonical_group_order ->
 (0<len<=5)%nat ->
 (forall i,(i<(len-1))%nat -> 0<=Int64.signed(fw i)<2^62) ->
 (value*norm62_value_z 4 (fun i=>Int64.signed(d i))) mod canonical_group_order=
   norm62_value_z (len-1)%nat (fun i=>Int64.signed(fw i)) mod canonical_group_order ->
 norm62_value_z (len-1)%nat (fun i=>Int64.signed(fw i))=
   f(fst(stepN n (init canonical_group_order value scalar_inv_modulus_odd))) ->
 g(fst(stepN n (init canonical_group_order value scalar_inv_modulus_odd)))=0 ->
 (value=0 -> norm62_value_z 4 (fun i=>Int64.signed(d i)) mod canonical_group_order=0) ->
 ((if Int64.lt (fw (len-1)%nat) Int64.zero then -1 else 1)*
   norm62_value_z 4 (fun i=>Int64.signed(d i))) mod canonical_group_order=
 literal_scalar_invert_numeric value.
Proof.
 intros Range Len Low Link Match Stop Zero.
 rewrite literal_scalar_invert_numeric_modInv by (unfold canonical_group_order in *;lia).
 destruct(Z.eq_dec value 0) as [Eq|Ne].
 - subst value;rewrite <-Zmult_mod_idemp_r,(Zero eq_refl),Z.mul_0_r,Zmod_0_l,modInv_zero;reflexivity.
 - assert(Unit : Z.abs(norm62_value_z (len-1)%nat (fun i=>Int64.signed(fw i)))=1).
   { rewrite Match;apply inv_terminal_unit;[|exact Stop].
     change(Z.gcd canonical_group_order value=1);apply scalar_gcd_nonmultiple;lia. }
   apply modInv_mul_unique_l.
   replace (((if Int64.lt (fw (len-1)%nat) Int64.zero then -1 else 1)*
     norm62_value_z 4 (fun i=>Int64.signed(d i)))*value) with
     ((if Int64.lt (fw (len-1)%nat) Int64.zero then -1 else 1)*
       (value*norm62_value_z 4 (fun i=>Int64.signed(d i)))) by ring.
   rewrite <-Zmult_mod_idemp_r,Link,Zmult_mod_idemp_r.
   rewrite scalar_inv_finish_abs_value by assumption;rewrite Unit.
   apply Z.mod_small;unfold canonical_group_order;lia.
Qed.

Lemma scalar_inv_literal_after_canonical_input raw : 0<=raw<2^256 ->
 literal_scalar_invert_numeric (raw mod canonical_group_order)=literal_scalar_invert_numeric raw.
Proof.
 intro Range.
 assert(Normalized : 0<=raw mod canonical_group_order<2^256).
 { pose proof(Z.mod_pos_bound raw canonical_group_order ltac:(unfold canonical_group_order;lia));
   unfold canonical_group_order in *;lia. }
 rewrite (literal_scalar_invert_numeric_modInv raw Range),
   (literal_scalar_invert_numeric_modInv (raw mod canonical_group_order) Normalized).
 apply modInv_eqm;unfold eqm;rewrite Z.mod_mod by (unfold canonical_group_order;lia);reflexivity.
Qed.

(** The real sign load, normalize call, copy-back and five frees are proved,
    not assumed. The unfinished loop must still establish the premises. *)
Theorem exec_scalar_inv_finish_literal value n len d fw beta e le m :
 (0<len<=5)%nat -> length beta=7%nat -> inv_loop_distinct beta ->
 ematch beta (snd inv_start_alloc) e -> blk beta 1=scalar_inv_modinfo_block ->
 le!_len=Some(Vint(Int.repr(Z.of_nat len))) ->
 le!_modinfo=Some(Vptr scalar_inv_modinfo_block Ptrofs.zero) ->
 le!_x=Some(Vptr (blk beta 0) Ptrofs.zero) ->
 modnorm62_limb_bounds d ->
 -2*canonical_group_order<norm62_value_z 4 (fun i=>Int64.signed(d i))<canonical_group_order ->
 fe_at m (blk beta 2) 0 (words5 d) -> fe_at m (blk beta 4) 0 (words5 fw) ->
 Mem.range_perm m (blk beta 0) 0 40 Cur Freeable ->
 (forall r,(2<=r<7)%nat -> Mem.range_perm m (blk beta r) 0 (inv_local_size r) Cur Freeable) ->
 modinfo_scalar_global_rep m -> 0<=value<canonical_group_order ->
 (forall i,(i<(len-1))%nat -> 0<=Int64.signed(fw i)<2^62) ->
 (value*norm62_value_z 4 (fun i=>Int64.signed(d i))) mod canonical_group_order=
   norm62_value_z (len-1)%nat (fun i=>Int64.signed(fw i)) mod canonical_group_order ->
 norm62_value_z (len-1)%nat (fun i=>Int64.signed(fw i))=
   f(fst(stepN n (init canonical_group_order value scalar_inv_modulus_odd))) ->
 g(fst(stepN n (init canonical_group_order value scalar_inv_modulus_odd)))=0 ->
 (value=0 -> norm62_value_z 4 (fun i=>Int64.signed(d i)) mod canonical_group_order=0) -> exists mf mr,
 Clight2.exec_stmt secp_ge e le m inv_finish E0 (scalar_inv_finish_temps len fw le) mf Out_normal /\
 Mem.free_list mf (blocks_of_env secp_ge e)=Some mr /\
 fe_at mr (blk beta 0) 0 (words5(scalar_inv_finish_words len d fw)) /\
 signed62_normalized(scalar_inv_finish_words len d fw) /\
 signed62_unsigned_value(scalar_inv_finish_words len d fw)=literal_scalar_invert_numeric value /\
 (forall raw,0<=raw<2^256 -> value=raw mod canonical_group_order ->
   signed62_unsigned_value(scalar_inv_finish_words len d fw)=literal_scalar_invert_numeric raw) /\
 (forall input : Ty.tySem (Word 8),value=@toZ (WordToZ 8) input mod canonical_group_order ->
   @fromZ (WordToZ 8) (signed62_unsigned_value(scalar_inv_finish_words len d fw))=
   @literal_scalar_invert Alg.CoreFunSem input) /\
 Mem.range_perm mr (blk beta 0) 0 40 Cur Freeable /\ modinfo_scalar_global_rep mr /\
 lframe (fun b ofs=>norm62_outside (blk beta 2) scalar_inv_modinfo_block b ofs /\
   b<>blk beta 0 /\ inv_free_outside beta b) m mr.
Proof.
 intros Len Size Distinct Env Block Length Modinfo X Bounds Value DField FField FreeX Owned Global
   Range Low Link Match Stop Zero.
 destruct(exec_scalar_inv_finish_and_free len d fw beta e le m Len Size Distinct Env Block
   Length Modinfo X Bounds Value DField FField FreeX Owned Global)
   as (mf & mr & Run & Free & Output & Normal & Numeric & XFree & GlobalR & Frame).
 rewrite (scalar_inv_terminal_literal value n len d fw Range Len Low Link Match Stop Zero) in Numeric.
 assert(Original : forall raw,0<=raw<2^256 -> value=raw mod canonical_group_order ->
   signed62_unsigned_value(scalar_inv_finish_words len d fw)=literal_scalar_invert_numeric raw).
 { intros raw Raw Eq;rewrite Numeric,Eq;apply scalar_inv_literal_after_canonical_input;exact Raw. }
 assert(Simplicity : forall input : Ty.tySem (Word 8),
   value=@toZ (WordToZ 8) input mod canonical_group_order ->
   @fromZ (WordToZ 8) (signed62_unsigned_value(scalar_inv_finish_words len d fw))=
   @literal_scalar_invert Alg.CoreFunSem input).
 { intros input Eq;rewrite (Original (@toZ (WordToZ 8) input) (word_value_bounds 8 input) Eq).
   symmetry;apply literal_scalar_invert_word. }
 exists mf,mr;repeat first[assumption|split].
Qed.
