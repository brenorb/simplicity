(** Arithmetic meaning of the correction words assigned by the original C. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_modinfo_fe_global.
Require Import C.jet_secp_modinv_fg_prefix_numeric C.jet_secp_modinv_normalize62_words.
Require Import C.jet_secp_i128_mul_numeric C.jet_secp_i128_accum_mul_numeric C.jet_secp_i128_shift62_numeric.
Require Import C.jet_secp_modinv_fg_iteration_arith.
Require Import C.jet_secp_modinv_de_correction.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma de62_repr_mod62 z : Int64.signed (Int64.repr z) mod 2^62=z mod 2^62.
Proof.
 rewrite <-norm62_unsigned_signed_mod;symmetry.
 destruct (Int64.eqm_unsigned_repr z) as (k & Eq);rewrite Eq at 1.
 change Int64.modulus with (4*2^62).
 replace (k*(4*2^62)+Int64.unsigned (Int64.repr z)) with
  (Int64.unsigned (Int64.repr z)+(k*4)*2^62) by ring.
 rewrite Z_mod_plus_full;reflexivity.
Qed.
Lemma de62_mul_mod62 a b : Int64.signed (Int64.mul a b) mod 2^62=
 (Int64.signed a*Int64.signed b) mod 2^62.
Proof. rewrite Int64.mul_signed;apply de62_repr_mod62. Qed.
Lemma de62_mask_correction low start x : Int64.signed low mod 2^62=x mod 2^62 ->
 Int64.signed (Int64.and (Int64.add (Int64.mul (Int64.repr 2866531139136965327) low) start)
  (Int64.repr (2^62-1)))=(2866531139136965327*x+Int64.signed start) mod 2^62.
Proof.
 intro Low;rewrite norm62_mask_signed,Int64.add_signed,de62_repr_mod62.
 rewrite <-Z.add_mod_idemp_l by lia;rewrite de62_mul_mod62.
 change (Int64.signed (Int64.repr 2866531139136965327)) with 2866531139136965327.
 rewrite <-Z.mul_mod_idemp_r by lia;rewrite Low,Z.mul_mod_idemp_r,Z.add_mod_idemp_l by lia;reflexivity.
Qed.

Definition de62_row_bound (rho : nat->int64) (high : bool) :=
 Z.abs (Int64.signed (rho (if high then 12%nat else 10%nat)))+
 Z.abs (Int64.signed (rho (if high then 13%nat else 11%nat)))<=2^62.
Definition de62_multiple_value (rho : nat->int64) (high : bool) :=
 (if Int64.lt (rho 4%nat) Int64.zero then Int64.signed (rho (if high then 12%nat else 10%nat)) else 0)+
 (if Int64.lt (rho 9%nat) Int64.zero then Int64.signed (rho (if high then 13%nat else 11%nat)) else 0).
Definition de62_first_value (rho : nat->int64) (high : bool) :=
 fg_row_value rho (if high then 12%nat else 10%nat) (if high then 13%nat else 11%nat).
Definition de62_correction_value rho high := de62_multiple_value rho high-
 (2866531139136965327*de62_first_value rho high+de62_multiple_value rho high) mod 2^62.

Lemma de62_multiple_bound rho high : de62_row_bound rho high -> Z.abs (de62_multiple_value rho high)<=2^62.
Proof.
 intro Row;unfold de62_multiple_value.
 pose proof (Z.abs_nonneg (Int64.signed (rho (if high then 12%nat else 10%nat)))) as U.
 pose proof (Z.abs_nonneg (Int64.signed (rho (if high then 13%nat else 11%nat)))) as V.
 pose proof (Z.abs_triangle (Int64.signed (rho (if high then 12%nat else 10%nat)))
  (Int64.signed (rho (if high then 13%nat else 11%nat)))) as Sum.
 destruct (Int64.lt (rho 4%nat) Int64.zero), (Int64.lt (rho 9%nat) Int64.zero);
 rewrite ?Z.add_0_l,?Z.add_0_r,?Z.abs_0;unfold de62_row_bound in Row;lia.
Qed.
Lemma de62_multiple_signed rho high : de62_row_bound rho high ->
 Int64.signed (de62_multiple_word rho high)=de62_multiple_value rho high.
Proof.
 intro Row;pose proof (de62_multiple_bound rho high Row) as Bound;apply Z.abs_le in Bound.
 unfold de62_multiple_word;change (Int64.repr 63) with (Int64.repr (Int64.zwordsize-1)).
 rewrite !Int64.shr_lt_zero.
 destruct (Int64.lt (rho 4%nat) Int64.zero) eqn:D, (Int64.lt (rho 9%nat) Int64.zero) eqn:E;
 rewrite ?Int64.and_mone,?Int64.and_zero,?Int64.add_zero,?Int64.add_zero_l.
 - unfold de62_multiple_value in Bound|-*;rewrite D,E in *.
   rewrite Int64.add_signed;apply Int64.signed_repr;
   change Int64.min_signed with (-2^63);change Int64.max_signed with (2^63-1);lia.
 - unfold de62_multiple_value;rewrite D,E;lia.
 - unfold de62_multiple_value;rewrite D,E;lia.
 - unfold de62_multiple_value;rewrite D,E;reflexivity.
Qed.

Lemma de62_first_low_mod rho high : de62_row_bound rho high ->
 Int64.signed (fg_row_low rho (if high then 12%nat else 10%nat) (if high then 13%nat else 11%nat)) mod 2^62=
 de62_first_value rho high mod 2^62.
Proof.
 intro Row.
 set (u:=if high then 12%nat else 10%nat);set (v:=if high then 13%nat else 11%nat).
 pose proof (fg_pair_mod62 (fg_row_low rho u v,fg_row_high rho u v)) as Low.
 change (i128_signed_value (fg_row_low rho u v) (fg_row_high rho u v) mod 2^62=
  Int64.signed (fg_row_low rho u v) mod 2^62) in Low.
 assert (Value : i128_signed_value (fg_row_low rho u v) (fg_row_high rho u v)=de62_first_value rho high).
 { unfold fg_row_low,fg_row_high;rewrite smul_accum_exact_if_in_range.
   - rewrite smul128_exact_product;reflexivity.
   - rewrite smul128_exact_product;apply fg_row_range;exact Row. }
 rewrite Value in Low;symmetry;exact Low.
Qed.

Lemma de62_correction_signed rho high : de62_row_bound rho high ->
 Int64.signed (de62_correction_word rho high)=de62_correction_value rho high /\
 -2^63<de62_correction_value rho high<=2^62.
Proof.
 intro Row;pose proof (de62_multiple_bound rho high Row) as Bound;apply Z.abs_le in Bound.
 pose proof (Z.mod_pos_bound (2866531139136965327*de62_first_value rho high+de62_multiple_value rho high)
  (2^62) ltac:(lia)) as Rem.
 assert (Mask : Int64.signed (Int64.and
  (Int64.add (Int64.mul (Int64.repr 2866531139136965327)
   (fg_row_low rho (if high then 12%nat else 10%nat) (if high then 13%nat else 11%nat)))
   (de62_multiple_word rho high)) (Int64.repr (2^62-1)))=
  (2866531139136965327*de62_first_value rho high+de62_multiple_value rho high) mod 2^62).
 { rewrite (de62_mask_correction _ _ (de62_first_value rho high))
    by (apply de62_first_low_mod;exact Row).
   rewrite de62_multiple_signed by exact Row;reflexivity. }
 split.
 - unfold de62_correction_word;rewrite Int64.sub_signed.
   rewrite Mask,de62_multiple_signed by exact Row.
   apply Int64.signed_repr;unfold de62_correction_value;
   change Int64.min_signed with (-2^63);change Int64.max_signed with (2^63-1);lia.
 - unfold de62_correction_value;lia.
Qed.

Lemma de62_correction_divisible modulus inverse radix x offset : 0<radix -> (modulus*inverse) mod radix=1 ->
 (x+modulus*(offset-(inverse*x+offset) mod radix)) mod radix=0.
Proof.
 intros Positive Inverse.
 pose proof (Z.div_mod (modulus*inverse) radix ltac:(lia)) as Inv;rewrite Inverse in Inv.
 pose proof (Z.div_mod (inverse*x+offset) radix ltac:(lia)) as Rem.
 replace ((inverse*x+offset) mod radix) with
  (inverse*x+offset-radix*((inverse*x+offset)/radix)) by lia.
 replace (x+modulus*(offset-(inverse*x+offset-radix*((inverse*x+offset)/radix)))) with
  (x-(modulus*inverse)*x+(modulus*((inverse*x+offset)/radix))*radix) by ring.
 rewrite Inv.
 replace (x-(radix*(modulus*inverse/radix)+1)*x+(modulus*((inverse*x+offset)/radix))*radix) with
  ((modulus*((inverse*x+offset)/radix)-(modulus*inverse/radix)*x)*radix) by ring.
 apply Z.mod_mul;lia.
Qed.

Theorem de62_correction_contract rho high : de62_row_bound rho high ->
 Int64.signed (de62_correction_word rho high)=de62_correction_value rho high /\
 -2^63<de62_correction_value rho high<=2^62 /\
 (de62_first_value rho high+(-4294968273)*de62_correction_value rho high) mod 2^62=0.
Proof.
 intro Row;destruct (de62_correction_signed rho high Row) as (Value & Range).
 split;[exact Value|];split;[exact Range|].
 unfold de62_correction_value;apply de62_correction_divisible;[lia|exact modinfo_fe_inverse62].
Qed.

(** These are the values in the real prefix's temporary environment, not
    merely a property of a separately proposed arithmetic formula. The
    row bound is internal to the inverse algorithm; its caller must derive
    it from the actual divstep matrix. *)
Theorem exec_de62_correction_values rho beta e le m :
 rep rho beta (sregs de62_initial) m -> tmatch rho beta (stemps de62_initial) le ->
 ematch beta (snd de62_alloc) e -> (forall high, de62_row_bound rho high) ->
 exists lef mf,
 Clight2.exec_stmt secp_ge e le m de62_correction_prefix E0 lef mf Out_normal /\
 (forall (high : bool), lef!(if high then _me else _md)=
    Some (Vlong (Int64.repr (de62_correction_value rho high))) /\
   -2^63<de62_correction_value rho high<=2^62 /\
   (de62_first_value rho high+(-4294968273)*de62_correction_value rho high) mod 2^62=0) /\
 rep rho beta (sregs de62_correction_state) mf /\
 tmatch rho beta (stemps de62_correction_state) lef /\
 lframe (fun b ofs=>~foot beta (map rshape (sregs de62_initial)) b ofs) m mf.
Proof.
 intros Rep Temps Env Rows.
 destruct (exec_de62_correction_prefix rho beta e le m Rep Temps Env)
  as (lef & mf & Exec & MD & ME & Out & Match & Frame).
 exists lef,mf;split;[exact Exec|];split.
 - intro high;destruct (de62_correction_contract rho high (Rows high)) as (Value & Range & Divisible).
   split.
   + rewrite <-Value,Int64.repr_signed;destruct high;assumption.
   + split;assumption.
 - split;[exact Out|];split;assumption.
Qed.
