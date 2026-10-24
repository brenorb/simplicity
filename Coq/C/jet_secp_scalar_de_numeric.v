(** Exact integer recurrence for the scalar-order coefficient update.
    Internal matrix/limb bounds must be established by the inverse loop. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_scalar_de_exec C.jet_secp_scalar_de_recurrence C.jet_secp_scalar_normalize62
 C.jet_secp_modinfo_scalar_global C.jet_secp_canonical_scalar C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_modinv_de_correction C.jet_secp_modinv_de_correction_numeric
 C.jet_secp_modinv_de_numeric C.jet_secp_modinv_de_recurrence_words C.jet_secp_modinv_normalize62_words
 C.jet_secp_modinv_fg_prefix_numeric C.jet_secp_modinv_fg_iteration_arith
 C.jet_secp_modinv_fg_finish_numeric C.jet_secp_i128_accum_mul_numeric.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_de62_correction_value rho high := de62_multiple_value rho high-
 (3815112494326173377*de62_first_value rho high+de62_multiple_value rho high) mod 2^62.
Lemma scalar_de62_correction_signed rho high : de62_row_bound rho high ->
 Int64.signed(scalar_de62_correction_word rho high)=scalar_de62_correction_value rho high /\
 -2^63<scalar_de62_correction_value rho high<=2^62.
Proof.
 intro Row;pose proof(de62_multiple_bound rho high Row) as Bound;apply Z.abs_le in Bound.
 pose proof(Z.mod_pos_bound (3815112494326173377*de62_first_value rho high+
   de62_multiple_value rho high) (2^62) ltac:(lia)) as Rem.
 assert(Mask : Int64.signed(Int64.and
   (Int64.add (Int64.mul (Int64.repr 3815112494326173377)
     (fg_row_low rho (if high then 12%nat else 10%nat) (if high then 13%nat else 11%nat)))
     (de62_multiple_word rho high)) (Int64.repr(2^62-1)))=
   (3815112494326173377*de62_first_value rho high+de62_multiple_value rho high) mod 2^62).
 { rewrite (de62_mask_correction_word _ _ _ (de62_first_value rho high))
     by (apply de62_first_low_mod;exact Row).
   rewrite de62_multiple_signed by exact Row;reflexivity. }
 split.
 - unfold scalar_de62_correction_word;rewrite Int64.sub_signed.
   rewrite Mask,de62_multiple_signed by exact Row.
   apply Int64.signed_repr;unfold scalar_de62_correction_value;
   change Int64.min_signed with (-2^63);change Int64.max_signed with (2^63-1);lia.
 - unfold scalar_de62_correction_value;lia.
Qed.
Lemma scalar_de62_correction_contract rho high : de62_row_bound rho high ->
 Int64.signed(scalar_de62_correction_word rho high)=scalar_de62_correction_value rho high /\
 -2^63<scalar_de62_correction_value rho high<=2^62 /\
 (de62_first_value rho high+4598842128380346689*scalar_de62_correction_value rho high) mod 2^62=0.
Proof.
 intro Row;destruct(scalar_de62_correction_signed rho high Row) as (Value & Bound).
 split;[exact Value|];split;[exact Bound|].
 unfold scalar_de62_correction_value;apply de62_correction_divisible;[lia|exact modinfo_scalar_inverse62].
Qed.

Fixpoint scalar_de62_acc_value rho high k : Z := match k with
 | O=>de62_first_value rho high+
   Int64.signed(modinfo_scalar_limb 0)*scalar_de62_correction_value rho high
 | S n=>scalar_de62_acc_value rho high n/2^62+de62_limb_sum rho high (S n)+
   Int64.signed(modinfo_scalar_limb(S n))*scalar_de62_correction_value rho high
 end.
Definition scalar_de62_acc_bound : Z := 2^126.

Lemma scalar_de62_modulus_limb_bound i : (i<5)%nat ->
 Z.abs(Int64.signed(modinfo_scalar_limb i))<=2^62.
Proof. intro I;pose proof(scalar_norm62_modulus_bound i I);apply Z.abs_le;lia. Qed.
Lemma scalar_de62_quotient_bound x : Z.abs x<=scalar_de62_acc_bound -> Z.abs(x/2^62)<=2^64.
Proof.
 intro Bound;apply Z.abs_le in Bound;apply Z.abs_le;unfold scalar_de62_acc_bound in Bound.
 split;[apply Z.div_le_lower_bound|apply Z.div_le_upper_bound];lia.
Qed.

(** A shifted scalar accumulator need not fit in a signed 64-bit word.
    Retain its full signed-128 value while doing the next two products. *)
Lemma scalar_de62_row_exact p u v a b : Z.abs(fg_pair_value p)<=2^64 ->
 Z.abs(Int64.signed u)+Z.abs(Int64.signed v)<=2^62 ->
 Z.abs(Int64.signed a)<=2^62 -> Z.abs(Int64.signed b)<=2^62 ->
 fg_pair_value(fg_row_words p u v a b)=fg_row_sum p u v a b /\
 Z.abs(fg_row_sum p u v a b)<=2^64+2^124.
Proof.
 intros Carry Row A B.
 assert(UA : Z.abs(Int64.signed u*Int64.signed a)<=Z.abs(Int64.signed u)*2^62).
 { rewrite Z.abs_mul;apply Z.mul_le_mono_nonneg_l;[apply Z.abs_nonneg|exact A]. }
 assert(VB : Z.abs(Int64.signed v*Int64.signed b)<=Z.abs(Int64.signed v)*2^62).
 { rewrite Z.abs_mul;apply Z.mul_le_mono_nonneg_l;[apply Z.abs_nonneg|exact B]. }
 pose proof(Z.abs_nonneg(Int64.signed u));pose proof(Z.abs_nonneg(Int64.signed v)).
 pose proof(Z.abs_triangle (fg_pair_value p) (Int64.signed u*Int64.signed a)) as First.
 pose proof(Z.abs_triangle (fg_pair_value p+Int64.signed u*Int64.signed a)
   (Int64.signed v*Int64.signed b)) as Second.
 assert(FBound : Z.abs(fg_pair_value p+Int64.signed u*Int64.signed a)<=2^64+2^124) by lia.
 assert(SBound : Z.abs(fg_row_sum p u v a b)<=2^64+2^124) by (unfold fg_row_sum;lia).
 split;[|exact SBound];apply Z.abs_le in FBound;pose proof SBound as Sum;apply Z.abs_le in Sum.
 assert(E : fg_pair_value(fg_accum_words p u a)=fg_pair_value p+Int64.signed u*Int64.signed a).
 { apply fg_accum_words_exact;lia. }
 unfold fg_row_words;rewrite fg_accum_words_exact;
 [unfold fg_row_sum;rewrite E;reflexivity|rewrite E;change(-2^127<=fg_row_sum p u v a b<2^127);lia].
Qed.

Theorem scalar_de62_acc_exact rho high : de62_row_bound rho high -> de62_input_bound rho ->
 forall k,(k<5)%nat ->
 fg_pair_value(scalar_de62_acc_words rho high k)=scalar_de62_acc_value rho high k /\
 Z.abs(scalar_de62_acc_value rho high k)<=scalar_de62_acc_bound.
Proof.
 intros Row Inputs;destruct(scalar_de62_correction_signed rho high Row) as (Correction & CR).
 assert(CBound : Z.abs(scalar_de62_correction_value rho high)<=2^63) by (apply Z.abs_le;lia).
 induction k as [|k IH];intro K.
 - pose proof(de62_limb_sum_bound rho high 0 Row Inputs ltac:(lia)) as First.
   change(Z.abs(de62_first_value rho high)<=2^124) in First.
   pose proof(scalar_de62_modulus_limb_bound 0 ltac:(lia)) as Mu.
   assert(Product : Z.abs(Int64.signed(modinfo_scalar_limb 0)*scalar_de62_correction_value rho high)<=2^125).
   { rewrite Z.abs_mul;nia. }
   pose proof(Z.abs_triangle (de62_first_value rho high)
     (Int64.signed(modinfo_scalar_limb 0)*scalar_de62_correction_value rho high)) as Sum.
   assert(Total : Z.abs(scalar_de62_acc_value rho high 0)<=scalar_de62_acc_bound)
     by (cbn [scalar_de62_acc_value];unfold scalar_de62_acc_bound;lia).
   cbn [scalar_de62_acc_words scalar_de62_acc_value];rewrite fg_accum_words_exact.
   + rewrite de62_first_pair_exact by exact Row;rewrite Correction;split;[reflexivity|exact Total].
   + rewrite de62_first_pair_exact by exact Row;rewrite Correction.
     apply Z.abs_le in Total;unfold scalar_de62_acc_bound in Total;exact(ltac:(cbn [scalar_de62_acc_value] in Total;lia)).
 - destruct(IH ltac:(lia)) as (Previous & PreviousBound).
   assert(Carry : fg_pair_value(de62_shift_words(scalar_de62_acc_words rho high k))=
     scalar_de62_acc_value rho high k/2^62) by (rewrite de62_shift_value,Previous;reflexivity).
   pose proof(scalar_de62_quotient_bound _ PreviousBound) as CarryBound.
   destruct(Inputs (S k) K) as (D & E).
   destruct(scalar_de62_row_exact _ _ _ _ _ ltac:(rewrite Carry;exact CarryBound) Row D E)
     as (Next & NextBound).
   assert(Product : Z.abs(Int64.signed(modinfo_scalar_limb(S k))*scalar_de62_correction_value rho high)<=2^125).
   { pose proof(scalar_de62_modulus_limb_bound (S k) K);rewrite Z.abs_mul;nia. }
   cbn [scalar_de62_acc_words scalar_de62_acc_value];destruct(Nat.eqb (S k) 3) eqn:Index.
   + apply Nat.eqb_eq in Index.
     rewrite Next;unfold fg_row_sum;rewrite Carry.
     assert(MuZero : Int64.signed(modinfo_scalar_limb(S k))=0) by (rewrite Index;reflexivity).
     rewrite MuZero,Z.mul_0_l,Z.add_0_r;split;[unfold de62_limb_sum;ring|].
     unfold fg_row_sum in NextBound;rewrite Carry in NextBound;unfold scalar_de62_acc_bound,de62_limb_sum;lia.
   + assert(Total : Z.abs(fg_row_sum (de62_shift_words(scalar_de62_acc_words rho high k))
       (rho(if high then 12%nat else 10%nat)) (rho(if high then 13%nat else 11%nat))
       (rho(S k)) (rho(5+S k)%nat)+Int64.signed(modinfo_scalar_limb(S k))*
       scalar_de62_correction_value rho high)<=scalar_de62_acc_bound).
     { pose proof(Z.abs_triangle
         (fg_row_sum (de62_shift_words(scalar_de62_acc_words rho high k))
           (rho(if high then 12%nat else 10%nat)) (rho(if high then 13%nat else 11%nat))
           (rho(S k)) (rho(5+S k)%nat))
         (Int64.signed(modinfo_scalar_limb(S k))*scalar_de62_correction_value rho high));
       unfold scalar_de62_acc_bound;lia. }
     rewrite fg_accum_words_exact.
     * rewrite Next,Correction;unfold fg_row_sum;rewrite Carry.
       split;[unfold de62_limb_sum;ring|].
       unfold fg_row_sum in Total;rewrite Carry in Total.
       replace (scalar_de62_acc_value rho high k/2^62+de62_limb_sum rho high (S k)) with
         (scalar_de62_acc_value rho high k/2^62+
           Int64.signed(rho(if high then 12%nat else 10%nat))*Int64.signed(rho(S k))+
           Int64.signed(rho(if high then 13%nat else 11%nat))*Int64.signed(rho(5+S k)%nat))
         by (unfold de62_limb_sum;ring).
       exact Total.
     * rewrite Next,Correction;apply Z.abs_le in Total;unfold scalar_de62_acc_bound in Total;lia.
Qed.

Definition scalar_de62_output_value rho high :=
 norm62_value_z 4 (fun i=>Int64.signed(scalar_de62_recurrence_word rho high i)).

Lemma scalar_de62_lower_signed rho high i : de62_row_bound rho high -> de62_input_bound rho -> (i<4)%nat ->
 Int64.signed(scalar_de62_recurrence_word rho high i)=scalar_de62_acc_value rho high (S i) mod 2^62.
Proof.
 intros Row Inputs I;unfold scalar_de62_recurrence_word.
 assert(Test : Nat.eqb i 4=false) by (apply Nat.eqb_neq;lia);rewrite Test.
 rewrite norm62_mask_signed,<-(fg_pair_mod62(scalar_de62_acc_words rho high (S i))).
 rewrite (proj1(scalar_de62_acc_exact rho high Row Inputs (S i) ltac:(lia)));reflexivity.
Qed.

(** The last modulus limb is only 256. Thus the final carry fits a signed
    64-bit word, even though intermediate carries used the full 128 bits. *)
Lemma scalar_de62_final_bound rho high : de62_row_bound rho high -> de62_input_bound rho ->
 Z.abs(scalar_de62_acc_value rho high 4)<=de62_acc_bound.
Proof.
 intros Row Inputs.
 pose proof(proj2(scalar_de62_acc_exact rho high Row Inputs 3 ltac:(lia))) as Previous.
 pose proof(scalar_de62_quotient_bound _ Previous) as Carry.
 pose proof(de62_limb_sum_bound rho high 4 Row Inputs ltac:(lia)) as Limb.
 pose proof(proj2(scalar_de62_correction_signed rho high Row)) as CR.
 assert(Correction : Z.abs(scalar_de62_correction_value rho high)<=2^63) by (apply Z.abs_le;lia).
 pose proof(Z.abs_triangle (scalar_de62_acc_value rho high 3/2^62) (de62_limb_sum rho high 4)) as First.
 pose proof(Z.abs_triangle (scalar_de62_acc_value rho high 3/2^62+de62_limb_sum rho high 4)
   (256*scalar_de62_correction_value rho high)) as Sum.
 assert(Product : Z.abs(256*scalar_de62_correction_value rho high)<=2^71)
   by (rewrite Z.abs_mul;change(Z.abs 256) with 256;lia).
 change(Z.abs(scalar_de62_acc_value rho high 3/2^62+de62_limb_sum rho high 4+
   256*scalar_de62_correction_value rho high)<=de62_acc_bound).
 unfold de62_acc_bound;lia.
Qed.
Lemma scalar_de62_upper_signed rho high : de62_row_bound rho high -> de62_input_bound rho ->
 Int64.signed(scalar_de62_recurrence_word rho high 4)=scalar_de62_acc_value rho high 4/2^62.
Proof.
 intros Row Inputs.
 pose proof(proj1(scalar_de62_acc_exact rho high Row Inputs 4 ltac:(lia))) as Value.
 pose proof(de62_bounded_quotient _ (scalar_de62_final_bound rho high Row Inputs)) as Range.
 apply Z.abs_le in Range.
 change(Int64.signed(fst(de62_shift_words(scalar_de62_acc_words rho high 4)))=
   scalar_de62_acc_value rho high 4/2^62).
 rewrite fg_pair_low_signed.
 - rewrite de62_shift_value,Value;reflexivity.
 - rewrite de62_shift_value,Value;change Int64.min_signed with (-2^63);
   change Int64.max_signed with (2^63-1);lia.
Qed.

Theorem scalar_de62_scaled_value rho high : de62_row_bound rho high -> de62_input_bound rho ->
 2^62*scalar_de62_output_value rho high=
 de62_matrix_value rho high+canonical_group_order*scalar_de62_correction_value rho high.
Proof.
 intros Row Inputs.
 assert(Step : forall i,(0<i<5)%nat -> scalar_de62_acc_value rho high i=
   scalar_de62_acc_value rho high (i-1)%nat/2^62+
   (de62_limb_sum rho high i+Int64.signed(modinfo_scalar_limb i)*scalar_de62_correction_value rho high)).
 { intros [|i] I;[lia|];cbn [scalar_de62_acc_value Nat.sub];rewrite Nat.sub_0_r;lia. }
 pose proof(de62_telescope (scalar_de62_acc_value rho high)
   (fun i=>de62_limb_sum rho high i+Int64.signed(modinfo_scalar_limb i)*scalar_de62_correction_value rho high)
   (proj2(proj2(scalar_de62_correction_contract rho high Row))) Step) as Total.
 unfold scalar_de62_output_value;cbn [norm62_value_z].
 rewrite (scalar_de62_lower_signed rho high 0 Row Inputs ltac:(lia)),
   (scalar_de62_lower_signed rho high 1 Row Inputs ltac:(lia)),
   (scalar_de62_lower_signed rho high 2 Row Inputs ltac:(lia)),
   (scalar_de62_lower_signed rho high 3 Row Inputs ltac:(lia)),(scalar_de62_upper_signed rho high Row Inputs).
 rewrite Total,<-scalar_norm62_modulus_value.
 unfold de62_matrix_value,de62_input_value;cbn [norm62_value_z scalar_de62_acc_value].
 unfold de62_first_value,C.jet_secp_modinv_fg_prefix_numeric.fg_row_value,de62_limb_sum.
 destruct high;cbn [Nat.add];ring.
Qed.
Theorem scalar_de62_quotient_value rho high : de62_row_bound rho high -> de62_input_bound rho ->
 scalar_de62_output_value rho high=
 (de62_matrix_value rho high+canonical_group_order*scalar_de62_correction_value rho high)/2^62.
Proof.
 intros Row Inputs;rewrite <-(scalar_de62_scaled_value rho high Row Inputs),Z.mul_comm,Z.div_mul by lia;reflexivity.
Qed.
Theorem scalar_de62_modular_value rho high : de62_row_bound rho high -> de62_input_bound rho ->
 (2^62*scalar_de62_output_value rho high-de62_matrix_value rho high) mod canonical_group_order=0.
Proof.
 intros Row Inputs;rewrite (scalar_de62_scaled_value rho high Row Inputs).
 replace (de62_matrix_value rho high+canonical_group_order*scalar_de62_correction_value rho high-
   de62_matrix_value rho high) with (scalar_de62_correction_value rho high*canonical_group_order) by ring.
 apply Z.mod_mul;unfold canonical_group_order;lia.
Qed.

(** Exact equation for both rows, attached to the real helper execution and
    resulting memory. This is still an internal inverse-loop boundary. *)
Theorem eval_scalar_de_value rho beta m : rep rho beta scalar_de62_regs m ->
 (forall high,de62_row_bound rho high) -> de62_input_bound rho -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_update_de_62)
  [Vptr(blk beta 0)(Ptrofs.repr(bas beta 0));Vptr(blk beta 1)(Ptrofs.repr(bas beta 1));
   Vptr(blk beta 2)(Ptrofs.repr(bas beta 2));Vptr(blk beta 3)(Ptrofs.repr(bas beta 3))] E0 mf Vundef /\
 (forall (high : bool) i,(i<5)%nat -> Mem.load Mint64 mf (blk beta (if high then 1 else 0))
   (bas beta (if high then 1 else 0)+8*Z.of_nat i)=Some(Vlong(scalar_de62_recurrence_word rho high i))) /\
 (forall high,2^62*scalar_de62_output_value rho high=
   de62_matrix_value rho high+canonical_group_order*scalar_de62_correction_value rho high /\
   (2^62*scalar_de62_output_value rho high-de62_matrix_value rho high) mod canonical_group_order=0) /\
 rep rho beta (sregs scalar_de62_state) mf /\
 lframe (fun b ofs=>~foot beta (map rshape scalar_de62_regs) b ofs) m mf.
Proof.
 intros Rep Rows Inputs;destruct(eval_scalar_de_recurrence rho beta m Rep)
   as (mf & Call & Words & Out & Frame).
 exists mf;split;[exact Call|];split;[exact Words|];split.
 - intro high;split;[apply scalar_de62_scaled_value|apply scalar_de62_modular_value];[apply Rows|exact Inputs|apply Rows|exact Inputs].
 - split;assumption.
Qed.
