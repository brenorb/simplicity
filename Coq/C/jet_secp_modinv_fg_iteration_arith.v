(** Internal numeric recurrence for the original inverse transition body. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import C.jet_secp_i128_accum_mul_numeric C.jet_secp_i128_mul_numeric.
Require Import C.jet_secp_i128_shift62_numeric C.jet_secp_i128_shift62.
Require Import C.jet_secp_modinv_normalize62_words.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fg_pair_value (p : int64*int64) := i128_signed_value (fst p) (snd p).
Definition fg_accum_words (p : int64*int64) a b :=
 (smul_accum_lo_word (fst p) a b,smul_accum_hi_word (fst p) (snd p) a b).
Definition fg_row_words p u v f g := fg_accum_words (fg_accum_words p u f) v g.
Definition fg_row_sum p u v f g :=
 fg_pair_value p+Int64.signed u*Int64.signed f+Int64.signed v*Int64.signed g.
Definition fg_row_bound p u v f g : Prop :=
 Z.abs (fg_pair_value p)<=2^63 /\
 Z.abs (Int64.signed u)+Z.abs (Int64.signed v)<=2^62 /\
 Z.abs (Int64.signed f)<=2^62 /\ Z.abs (Int64.signed g)<=2^62.

Lemma fg_accum_words_exact p a b :
 -2^127<=fg_pair_value p+Int64.signed a*Int64.signed b<2^127 ->
 fg_pair_value (fg_accum_words p a b)=fg_pair_value p+Int64.signed a*Int64.signed b.
Proof. destruct p;apply smul_accum_exact_if_in_range. Qed.

Lemma fg_row_sum_bounds p u v f g : fg_row_bound p u v f g ->
 Z.abs (fg_pair_value p+Int64.signed u*Int64.signed f)<=2^63+2^124 /\
 Z.abs (fg_row_sum p u v f g)<=2^63+2^124.
Proof.
 intros (C & Row & F & G).
 assert (UF : Z.abs (Int64.signed u*Int64.signed f)<=Z.abs (Int64.signed u)*2^62).
 { rewrite Z.abs_mul;apply Z.mul_le_mono_nonneg_l;[apply Z.abs_nonneg|exact F]. }
 assert (VG : Z.abs (Int64.signed v*Int64.signed g)<=Z.abs (Int64.signed v)*2^62).
 { rewrite Z.abs_mul;apply Z.mul_le_mono_nonneg_l;[apply Z.abs_nonneg|exact G]. }
 pose proof (Z.abs_nonneg (Int64.signed u)) as U.
 pose proof (Z.abs_nonneg (Int64.signed v)) as V.
 pose proof (Z.abs_triangle (fg_pair_value p) (Int64.signed u*Int64.signed f)) as First.
 pose proof (Z.abs_triangle (fg_pair_value p+Int64.signed u*Int64.signed f)
  (Int64.signed v*Int64.signed g)) as Second.
 unfold fg_row_sum;split;lia.
Qed.

Lemma fg_row_words_exact p u v f g : fg_row_bound p u v f g ->
 fg_pair_value (fg_row_words p u v f g)=fg_row_sum p u v f g.
Proof.
 intro Bound;destruct (fg_row_sum_bounds p u v f g Bound) as (First & Second).
 apply Z.abs_le in First;apply Z.abs_le in Second.
 assert (E : fg_pair_value (fg_accum_words p u f)=fg_pair_value p+Int64.signed u*Int64.signed f).
 { apply fg_accum_words_exact;lia. }
 unfold fg_row_words;rewrite fg_accum_words_exact;[unfold fg_row_sum;rewrite E;reflexivity|].
 rewrite E;change (-2^127<=fg_row_sum p u v f g<2^127);lia.
Qed.

Lemma fg_pair_mod62 p : fg_pair_value p mod 2^62=Int64.signed (fst p) mod 2^62.
Proof.
 destruct p as [lo hi];unfold fg_pair_value,i128_signed_value;cbn [fst snd].
 change Int64.modulus with (4*2^62).
 replace (Int64.signed hi*(4*2^62)+Int64.unsigned lo) with
  (Int64.unsigned lo+(Int64.signed hi*4)*2^62) by ring.
 rewrite Z_mod_plus_full;apply norm62_unsigned_signed_mod.
Qed.

Definition fg_row_limb p u v f g := Int64.and (fst (fg_row_words p u v f g)) (Int64.repr (2^62-1)).
Definition fg_row_carry p u v f g :=
 (i128_shift62_low (fst (fg_row_words p u v f g)) (snd (fg_row_words p u v f g)),
  i128_shift62_high (snd (fg_row_words p u v f g))).

Theorem fg_row_step_numeric p u v f g : fg_row_bound p u v f g ->
 fg_pair_value (fg_row_carry p u v f g)=fg_row_sum p u v f g/2^62 /\
 Int64.unsigned (fg_row_limb p u v f g)=fg_row_sum p u v f g mod 2^62 /\
 0<=Int64.signed (fg_row_limb p u v f g)<2^62 /\
 Z.abs (fg_pair_value (fg_row_carry p u v f g))<=2^63 /\
 fg_row_sum p u v f g=fg_pair_value (fg_row_carry p u v f g)*2^62+
  Int64.unsigned (fg_row_limb p u v f g).
Proof.
 intro Bound;pose proof (fg_row_words_exact p u v f g Bound) as Exact.
 assert (Carry : fg_pair_value (fg_row_carry p u v f g)=fg_row_sum p u v f g/2^62).
 { unfold fg_row_carry,fg_pair_value;cbn [fst snd];rewrite i128_shift62_numeric;exact (f_equal (fun z=>z/2^62) Exact). }
 assert (Limb : Int64.unsigned (fg_row_limb p u v f g)=fg_row_sum p u v f g mod 2^62).
 { unfold fg_row_limb;rewrite norm62_mask_unsigned,<-fg_pair_mod62,Exact;reflexivity. }
 pose proof (Z.mod_pos_bound (fg_row_sum p u v f g) (2^62) ltac:(lia)) as Rem.
 split;[exact Carry|];split;[exact Limb|];split.
 - unfold fg_row_limb;rewrite norm62_mask_signed,<-fg_pair_mod62,Exact;exact Rem.
 - split.
   + rewrite Carry;apply Z.abs_le.
     destruct (fg_row_sum_bounds p u v f g Bound) as (_ & Sum);apply Z.abs_le in Sum.
     split;[apply Z.div_le_lower_bound|apply Z.div_le_upper_bound];lia.
   + rewrite Carry,Limb,Z.mul_comm;apply Z.div_mod;lia.
Qed.
