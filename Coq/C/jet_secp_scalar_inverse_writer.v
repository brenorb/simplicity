(** Reconstruct the original writer's exact representation from the actual
    scalar inverse output. The counting-call execution obligation is explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.extraMath C.jet_word_repr C.jet_sx_mem C.jet_sx_state C.jet_sx_rep C.jet_secp_linkage C.jets_secp
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_scalar_add_initial C.jet_secp_scalar_overflow_numeric
 C.jet_secp_scalar_limb_bridge C.jet_secp_scalar_negate_canonical
 C.jet_secp_canonical_scalar C.jet_secp_scalar_invert_literal
 C.jet_secp_scalar_writer_run C.jet_secp_scalar_writer_storage
 C.jet_secp_modinfo_scalar_initialized C.jet_secp_scalar_inverse_initialized
 C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_scalar_normalize literal_scalar_invert.

Lemma scalar_values_limb_rho value : scalar_add_values (scalar_limb_rho value) 0=
 map Int64.repr(scalar_limbs_of value).
Proof. reflexivity. Qed.
Lemma scalar_values_roundtrip rho :
 map Int64.repr(scalar_limbs_of(scalar_limb_value rho))=scalar_add_values rho 0.
Proof.
 unfold scalar_limb_value;rewrite scalar_limbs_of_four_words.
 cbn [map];rewrite !Int64.repr_unsigned;reflexivity.
Qed.
Lemma scalar_limb_value_word_range rho : 0<=scalar_limb_value rho<2^256.
Proof.
 pose proof(Int64.unsigned_range(rho 0%nat)) as H0.
 pose proof(Int64.unsigned_range(rho 1%nat)) as H1.
 pose proof(Int64.unsigned_range(rho 2%nat)) as H2.
 pose proof(Int64.unsigned_range(rho 3%nat)) as H3.
 change Int64.modulus with (2^64) in *.
 unfold scalar_limb_value;lia.
Qed.

Theorem scalar_inverse_writer_from_reader m ba (value:Ty.tySem(Word 8)) :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 modinfo_scalar_initialized m ->
 scalar_at m ba 0 (map Int64.repr(scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))) ->
 Mem.range_perm m ba 0 32 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_inverse_var)
  [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef /\
 rep (scalar_limb_rho (@toZ (WordToZ 8) (@literal_scalar_invert Alg.CoreFunSem value)))
  [(ba,0)] scalar_writer_initial_regs mf /\
 Mem.range_perm mf ba 0 32 Cur Freeable /\ modinfo_scalar_initialized mf /\
 lframe(fun b _=>b<>ba) m mf /\ readonly_preserved m mf.
Proof.
 intros CountCall Ready Input Free.
 set(z:=@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)).
 assert(InputR:scalar_at m ba 0 (scalar_add_values(scalar_limb_rho z)0)).
 { rewrite scalar_values_limb_rho;exact Input. }
 assert(Value:scalar_limb_value(scalar_limb_rho z)=z).
 { apply scalar_limb_rho_value;apply word_toZ_range. }
 assert(Range:0<=scalar_limb_value(scalar_limb_rho z)<canonical_group_order).
 { rewrite Value;apply scalar_negate_normalize_range. }
 destruct(eval_scalar_inverse_var_initialized (scalar_limb_rho z) m ba ba CountCall Ready InputR Free Free Range)
  as(result & mf & Call & Output & Numeric & Literal & FreeF & ReadyF & Frame & Preserved).
 assert(Word:@fromZ (WordToZ 8) (scalar_limb_value result)=@literal_scalar_invert Alg.CoreFunSem value).
 { apply Literal;rewrite Value;apply canonical_scalar_normalize_numeric. }
 assert(OutputValue:@toZ (WordToZ 8) (@literal_scalar_invert Alg.CoreFunSem value)=scalar_limb_value result).
 { rewrite <-Word,to_fromZ.
   change (two_power_nat (ToZ.Theory.bitSize (WordToZ 8))) with (2^256).
   apply Z.mod_small;apply scalar_limb_value_word_range. }
 assert(Writer:rep (scalar_limb_rho (@toZ (WordToZ 8) (@literal_scalar_invert Alg.CoreFunSem value)))
  [(ba,0)] scalar_writer_initial_regs mf).
 { apply scalar_writer_initial_rep_from_storage;[|exact FreeF].
   rewrite OutputValue,scalar_values_roundtrip;exact Output. }
 exists mf;split;[exact Call|];split;[exact Writer|];split;[exact FreeF|];split;[exact ReadyF|];split;[|exact Preserved].
 eapply lframe_implies;[exact Frame|];intros b ofs Different Valid;split;exact Different.
Qed.
