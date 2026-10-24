(** Integer value and bounds of the original field coefficient update.
    All row/limb/value bounds are internal inverse-algorithm invariants;
    the public inverse caller must establish them from its actual state. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
Require Import C.jet_secp_modinv_de_recurrence_words C.jet_secp_modinv_de_correction.
Require Import C.jet_secp_modinv_de_correction_numeric C.jet_secp_modinv_fg_prefix_numeric.
Require Import C.jet_secp_modinv_fg_iteration_arith C.jet_secp_modinv_fg_finish_numeric.
Require Import C.jet_secp_i128_mul_numeric C.jet_secp_i128_accum_mul_numeric C.jet_secp_i128_shift62_numeric.
Require Import C.jet_secp_modinv_normalize62_words C.jet_secp_modinv_normalize62_numeric C.jet_secp_fe_math.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition de62_input_bound (rho : nat->int64) : Prop := forall i,(i<5)%nat ->
 Z.abs (Int64.signed (rho i))<=2^62 /\ Z.abs (Int64.signed (rho (5+i)%nat))<=2^62.
Definition de62_limb_sum (rho : nat->int64) (high : bool) i :=
 Int64.signed (rho (if high then 12%nat else 10%nat))*Int64.signed (rho i)+
 Int64.signed (rho (if high then 13%nat else 11%nat))*Int64.signed (rho (5+i)%nat).
Fixpoint de62_acc_value rho high k : Z := match k with
 | O=>de62_first_value rho high+(-4294968273)*de62_correction_value rho high
 | S n=>de62_acc_value rho high n/2^62+de62_limb_sum rho high (S n)+
   (if Nat.eqb (S n) 4 then 256*de62_correction_value rho high else 0)
 end.
Definition de62_acc_bound : Z := 2^125-2^62.

Lemma de62_first_pair_exact rho high : de62_row_bound rho high ->
 fg_pair_value
  (fg_row_low rho (if high then 12%nat else 10%nat) (if high then 13%nat else 11%nat),
   fg_row_high rho (if high then 12%nat else 10%nat) (if high then 13%nat else 11%nat))=
 de62_first_value rho high.
Proof.
 intro Row;unfold fg_pair_value;cbn [fst snd];unfold fg_row_low,fg_row_high.
 rewrite smul_accum_exact_if_in_range.
 - rewrite smul128_exact_product;reflexivity.
 - rewrite smul128_exact_product;apply fg_row_range;exact Row.
Qed.

Lemma de62_limb_sum_bound rho high i : de62_row_bound rho high ->
 de62_input_bound rho -> (i<5)%nat -> Z.abs (de62_limb_sum rho high i)<=2^124.
Proof.
 intros Row Inputs I;destruct (Inputs i I) as (F & G).
 set (u:=Int64.signed (rho (if high then 12%nat else 10%nat))) in *.
 set (v:=Int64.signed (rho (if high then 13%nat else 11%nat))) in *.
 pose proof (Z.abs_nonneg u) as U;pose proof (Z.abs_nonneg v) as V.
 assert (UF : Z.abs (u*Int64.signed (rho i))<=Z.abs u*2^62).
 { rewrite Z.abs_mul;apply Z.mul_le_mono_nonneg_l;assumption. }
 assert (VG : Z.abs (v*Int64.signed (rho (5+i)%nat))<=Z.abs v*2^62).
 { rewrite Z.abs_mul;apply Z.mul_le_mono_nonneg_l;assumption. }
 pose proof (Z.abs_triangle (u*Int64.signed (rho i)) (v*Int64.signed (rho (5+i)%nat))).
 change (Z.abs u+Z.abs v<=2^62) in Row.
 change (Z.abs (u*Int64.signed (rho i)+v*Int64.signed (rho (5+i)%nat))<=2^124);lia.
Qed.

Lemma de62_bounded_quotient value : Z.abs value<=de62_acc_bound ->
 Z.abs (value/2^62)<=2^63-1.
Proof.
 intro Bound;apply Z.abs_le in Bound;apply Z.abs_le;unfold de62_acc_bound in Bound.
 split;[apply Z.div_le_lower_bound|apply Z.div_le_upper_bound];lia.
Qed.
Lemma de62_shift_value p : fg_pair_value (de62_shift_words p)=fg_pair_value p/2^62.
Proof. unfold de62_shift_words,fg_pair_value;cbn [fst snd];apply i128_shift62_numeric. Qed.

Theorem de62_acc_exact rho high : de62_row_bound rho high -> de62_input_bound rho ->
 forall k,(k<5)%nat ->
 fg_pair_value (de62_acc_words rho high k)=de62_acc_value rho high k /\
 Z.abs (de62_acc_value rho high k)<=de62_acc_bound.
Proof.
 intros Row Inputs.
 destruct (de62_correction_signed rho high Row) as (Correction & CR).
 induction k as [|k IH];intro K.
 - pose proof (de62_limb_sum_bound rho high 0 Row Inputs ltac:(lia)) as First.
   change (Z.abs (de62_first_value rho high)<=2^124) in First;apply Z.abs_le in First.
   assert (Range : -2^127<=de62_first_value rho high+(-4294968273)*de62_correction_value rho high<2^127) by lia.
   cbn [de62_acc_words de62_acc_value];rewrite fg_accum_words_exact.
   + rewrite de62_first_pair_exact by exact Row.
     change (Int64.signed (Int64.repr (-4294968273))) with (-4294968273).
     rewrite Correction;split;[reflexivity|];apply Z.abs_le;unfold de62_acc_bound;lia.
   + rewrite de62_first_pair_exact by exact Row.
     change (Int64.signed (Int64.repr (-4294968273))) with (-4294968273).
     rewrite Correction;exact Range.
 - destruct (IH ltac:(lia)) as (Previous & PreviousBound).
   assert (Carry : fg_pair_value (de62_shift_words (de62_acc_words rho high k))=de62_acc_value rho high k/2^62)
    by (rewrite de62_shift_value,Previous;reflexivity).
   pose proof (de62_bounded_quotient _ PreviousBound) as CarryBound.
   destruct (Inputs (S k) K) as (F & G).
   assert (RB : fg_row_bound (de62_shift_words (de62_acc_words rho high k))
    (rho (if high then 12%nat else 10%nat)) (rho (if high then 13%nat else 11%nat))
    (rho (S k)) (rho (5+S k)%nat)).
   { split;[rewrite Carry;lia|];split;[exact Row|];split;assumption. }
   pose proof (fg_row_words_exact _ _ _ _ _ RB) as Next.
   destruct (fg_row_sum_bounds _ _ _ _ _ RB) as (_ & NextBound);apply Z.abs_le in NextBound.
   cbn [de62_acc_words de62_acc_value];destruct (Nat.eqb (S k) 4).
   + rewrite fg_accum_words_exact.
     * rewrite Next;unfold fg_row_sum;rewrite Carry.
       change (Int64.signed (Int64.repr 256)) with 256;rewrite Correction.
       split;[unfold de62_limb_sum;ring|].
       apply Z.abs_le;unfold de62_acc_bound.
       unfold fg_row_sum in NextBound;rewrite Carry in NextBound;unfold de62_limb_sum;lia.
     * rewrite Next;change (Int64.signed (Int64.repr 256)) with 256;rewrite Correction;lia.
   + rewrite Next;unfold fg_row_sum;rewrite Carry.
     split;[unfold de62_limb_sum;ring|].
     apply Z.abs_le;unfold de62_acc_bound.
     unfold fg_row_sum in NextBound;rewrite Carry in NextBound;unfold de62_limb_sum;lia.
Qed.

Definition de62_input_value (rho : nat->int64) (high : bool) :=
 norm62_value_z 4 (fun i=>Int64.signed (rho (if high then (5+i)%nat else i))).
Definition de62_matrix_value (rho : nat->int64) (high : bool) :=
 Int64.signed (rho (if high then 12%nat else 10%nat))*de62_input_value rho false+
 Int64.signed (rho (if high then 13%nat else 11%nat))*de62_input_value rho true.
Definition de62_output_value rho high :=
 norm62_value_z 4 (fun i=>Int64.signed (de62_recurrence_word rho high i)).

Lemma de62_lower_signed rho high i : de62_row_bound rho high -> de62_input_bound rho -> (i<4)%nat ->
 Int64.signed (de62_recurrence_word rho high i)=de62_acc_value rho high (S i) mod 2^62.
Proof.
 intros Row Inputs I;unfold de62_recurrence_word.
 assert (Test : Nat.eqb i 4=false) by (apply Nat.eqb_neq;lia);rewrite Test.
 rewrite norm62_mask_signed,<-(fg_pair_mod62 (de62_acc_words rho high (S i))).
 rewrite (proj1 (de62_acc_exact rho high Row Inputs (S i) ltac:(lia)));reflexivity.
Qed.
Lemma de62_upper_signed rho high : de62_row_bound rho high -> de62_input_bound rho ->
 Int64.signed (de62_recurrence_word rho high 4)=de62_acc_value rho high 4/2^62.
Proof.
 intros Row Inputs;destruct (de62_acc_exact rho high Row Inputs 4 ltac:(lia)) as (Value & Bound).
 pose proof (de62_bounded_quotient _ Bound) as Range;apply Z.abs_le in Range.
 change (Int64.signed (fst (de62_shift_words (de62_acc_words rho high 4)))=
   de62_acc_value rho high 4/2^62).
 rewrite fg_pair_low_signed.
 - rewrite de62_shift_value,Value;reflexivity.
 - rewrite de62_shift_value,Value;change Int64.min_signed with (-2^63);
   change Int64.max_signed with (2^63-1);lia.
Qed.

Lemma de62_telescope (a b : nat->Z) : a 0%nat mod 2^62=0 ->
 (forall i,(0<i<5)%nat -> a i=a (i-1)%nat/2^62+b i) ->
 2^62*(a 1%nat mod 2^62+2^62*(a 2%nat mod 2^62+
   2^62*(a 3%nat mod 2^62+2^62*(a 4%nat mod 2^62+2^62*(a 4%nat/2^62)))))=
 a 0%nat+2^62*b 1%nat+2^124*b 2%nat+2^186*b 3%nat+2^248*b 4%nat.
Proof.
 intros Zero Step.
 pose proof (Step 1%nat ltac:(lia)) as S1;pose proof (Step 2%nat ltac:(lia)) as S2.
 pose proof (Step 3%nat ltac:(lia)) as S3;pose proof (Step 4%nat ltac:(lia)) as S4.
 pose proof (Z.div_mod (a 0%nat) (2^62) ltac:(lia)) as D0.
 pose proof (Z.div_mod (a 1%nat) (2^62) ltac:(lia)) as D1.
 pose proof (Z.div_mod (a 2%nat) (2^62) ltac:(lia)) as D2.
 pose proof (Z.div_mod (a 3%nat) (2^62) ltac:(lia)) as D3.
 pose proof (Z.div_mod (a 4%nat) (2^62) ltac:(lia)) as D4.
 cbn [Nat.sub] in S1,S2,S3,S4;lia.
Qed.

Theorem de62_scaled_value rho high : de62_row_bound rho high -> de62_input_bound rho ->
 2^62*de62_output_value rho high=
 de62_matrix_value rho high+feP*de62_correction_value rho high.
Proof.
 intros Row Inputs.
 assert (Step : forall i,(0<i<5)%nat -> de62_acc_value rho high i=
   de62_acc_value rho high (i-1)%nat/2^62+
   (de62_limb_sum rho high i+(if Nat.eqb i 4 then 256*de62_correction_value rho high else 0))).
 { intros [|i] I;[lia|];cbn [de62_acc_value Nat.sub];rewrite Nat.sub_0_r;lia. }
 pose proof (de62_telescope (de62_acc_value rho high)
  (fun i=>de62_limb_sum rho high i+(if Nat.eqb i 4 then 256*de62_correction_value rho high else 0))
  (proj2 (proj2 (de62_correction_contract rho high Row))) Step) as Total.
 unfold de62_output_value;cbn [norm62_value_z].
 rewrite (de62_lower_signed rho high 0 Row Inputs ltac:(lia)),
  (de62_lower_signed rho high 1 Row Inputs ltac:(lia)),
  (de62_lower_signed rho high 2 Row Inputs ltac:(lia)),
  (de62_lower_signed rho high 3 Row Inputs ltac:(lia)),(de62_upper_signed rho high Row Inputs).
 rewrite Total.
 unfold de62_matrix_value,de62_input_value;cbn [norm62_value_z de62_acc_value Nat.eqb].
 unfold de62_first_value, C.jet_secp_modinv_fg_prefix_numeric.fg_row_value,de62_limb_sum,feP,feR.
 destruct high;cbn [Nat.add];ring.
Qed.

Theorem de62_quotient_value rho high : de62_row_bound rho high -> de62_input_bound rho ->
 de62_output_value rho high=
 (de62_matrix_value rho high+feP*de62_correction_value rho high)/2^62.
Proof.
 intros Row Inputs;rewrite <-(de62_scaled_value rho high Row Inputs),Z.mul_comm,Z.div_mul by lia;reflexivity.
Qed.
Theorem de62_modular_value rho high : de62_row_bound rho high -> de62_input_bound rho ->
 (2^62*de62_output_value rho high-de62_matrix_value rho high) mod feP=0.
Proof.
 intros Row Inputs;rewrite (de62_scaled_value rho high Row Inputs).
 replace (de62_matrix_value rho high+feP*de62_correction_value rho high-de62_matrix_value rho high)
  with (de62_correction_value rho high*feP) by ring.
 apply Z.mod_mul;unfold feP,feR;lia.
Qed.

Definition de62_array (rho : nat->int64) (high : bool) i := rho (if high then (5+i)%nat else i).
Definition de62_state_bounds rho :=
 (forall high,norm62_limb_bounds (de62_array rho high)) /\
 (forall high,-2*feP<de62_input_value rho high<feP).
Definition de62_balanced_value (rho : nat->int64) (high : bool) := de62_input_value rho high+
 if Int64.lt (rho (if high then 9%nat else 4%nat)) Int64.zero then feP else 0.

Lemma de62_state_input_bound rho : de62_state_bounds rho -> de62_input_bound rho.
Proof.
 intros (Limbs & Values) i I.
 pose proof (Limbs false i I) as D;pose proof (Limbs true i I) as E.
 split;apply Z.abs_le;change (-(2^62-1)<=Int64.signed (rho i)<=2^62-1) in D;
 change (-(2^62-1)<=Int64.signed (rho (5+i)%nat)<=2^62-1) in E;lia.
Qed.

Lemma de62_balanced_range rho high : de62_state_bounds rho ->
 -feP<de62_balanced_value rho high<feP.
Proof.
 intros (Limbs & Values).
 pose proof (norm62_first_range (de62_array rho high) Int64.zero (Limbs high) (Values high)) as Range.
 rewrite norm62_first_value in Range by apply Limbs.
 change (-feP<1*de62_balanced_value rho high<feP) in Range.
 rewrite Z.mul_1_l in Range;exact Range.
Qed.

Lemma de62_balanced_row_modulus M u v d e : 0<M -> Z.abs u+Z.abs v<=2^62 ->
 -M<d<M -> -M<e<M -> -2^62*M<u*d+v*e<2^62*M.
Proof.
 intros Positive Row D E.
 assert (AD : Z.abs d<=M-1) by (apply Z.abs_le;lia).
 assert (AE : Z.abs e<=M-1) by (apply Z.abs_le;lia).
 assert (UD : Z.abs (u*d)<=Z.abs u*(M-1)).
 { rewrite Z.abs_mul;apply Z.mul_le_mono_nonneg_l;[apply Z.abs_nonneg|exact AD]. }
 assert (VE : Z.abs (v*e)<=Z.abs v*(M-1)).
 { rewrite Z.abs_mul;apply Z.mul_le_mono_nonneg_l;[apply Z.abs_nonneg|exact AE]. }
 pose proof (Z.abs_triangle (u*d) (v*e)) as Triangle.
 pose proof (Z.abs_nonneg u);pose proof (Z.abs_nonneg v).
 assert (Sum : Z.abs (u*d+v*e)<=2^62*(M-1)) by nia.
 apply Z.abs_le in Sum;lia.
Qed.

Lemma de62_balanced_row u v d e : Z.abs u+Z.abs v<=2^62 ->
 -feP<d<feP -> -feP<e<feP -> -2^62*feP<u*d+v*e<2^62*feP.
Proof. exact(de62_balanced_row_modulus feP u v d e ltac:(unfold feP,feR;lia)). Qed.

Theorem de62_output_range rho high : de62_row_bound rho high -> de62_state_bounds rho ->
 -2*feP<de62_output_value rho high<feP.
Proof.
 intros Row Bounds.
 pose proof (de62_state_input_bound rho Bounds) as Inputs.
 pose proof (de62_balanced_row
  (Int64.signed (rho (if high then 12%nat else 10%nat)))
  (Int64.signed (rho (if high then 13%nat else 11%nat)))
  (de62_balanced_value rho false) (de62_balanced_value rho true) Row
  (de62_balanced_range rho false Bounds) (de62_balanced_range rho true Bounds)) as Balanced.
 set (rem:=(2866531139136965327*de62_first_value rho high+de62_multiple_value rho high) mod 2^62).
 pose proof (Z.mod_pos_bound
  (2866531139136965327*de62_first_value rho high+de62_multiple_value rho high) (2^62) ltac:(lia)) as Rem.
 change (0<=rem<2^62) in Rem.
 assert (Total : 2^62*de62_output_value rho high=
  Int64.signed (rho (if high then 12%nat else 10%nat))*de62_balanced_value rho false+
  Int64.signed (rho (if high then 13%nat else 11%nat))*de62_balanced_value rho true-feP*rem).
 { rewrite (de62_scaled_value rho high Row Inputs).
   unfold de62_matrix_value,de62_correction_value,de62_balanced_value,rem,de62_multiple_value.
   destruct (Int64.lt (rho 4%nat) Int64.zero), (Int64.lt (rho 9%nat) Int64.zero);ring. }
 unfold feP,feR in *;lia.
Qed.

Theorem de62_output_limb_bounds rho high : de62_row_bound rho high -> de62_state_bounds rho ->
 norm62_limb_bounds (de62_recurrence_word rho high).
Proof.
 intros Row Bounds;pose proof (de62_state_input_bound rho Bounds) as Inputs.
 assert (Low : forall i,(i<4)%nat -> 0<=Int64.signed (de62_recurrence_word rho high i)<2^62).
 { intros i I;rewrite de62_lower_signed by assumption;apply Z.mod_pos_bound;lia. }
 pose proof (de62_output_range rho high Row Bounds) as Range.
 pose proof (Low 0%nat ltac:(lia));pose proof (Low 1%nat ltac:(lia));
 pose proof (Low 2%nat ltac:(lia));pose proof (Low 3%nat ltac:(lia)).
 assert (Top : -(2^62-1)<=Int64.signed (de62_recurrence_word rho high 4)<=2^62-1).
 { unfold de62_output_value in Range;cbn [norm62_value_z] in Range;unfold feP,feR in *;lia. }
 intros i I;destruct (Nat.eq_dec i 4) as [->|Other];[exact Top|pose proof (Low i ltac:(lia));lia].
Qed.
