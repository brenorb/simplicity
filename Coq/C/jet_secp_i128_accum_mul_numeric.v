(** Numeric value of the actual signed multiply-accumulate, including wrap. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_i128_accum_mul_exec.
Require Import C.jet_secp_i128_mul_numeric C.jet_secp_i128_shift62_numeric.
Require Import C.jet_secp_u64_carry C.jet_secp_u128_accum_mul_numeric.
Local Open Scope Z_scope.
Import ListNotations.
Set Default Timeout 10.

Definition smul_accum_lo_word lo a b := Int64.add lo (smul128_lo_word a b).
Definition smul_accum_hi_word lo hi a b := Int64.add hi
 (Int64.add (smul128_hi_word a b)
 (Int64.repr (Int.signed (if Int64.ltu (smul_accum_lo_word lo a b) (smul128_lo_word a b)
 then Int.one else Int.zero)))).

Lemma smul128_hi_unsigned a b : Int64.unsigned (smul128_hi_word a b)=
 ((Int64.signed a*Int64.signed b)/Int64.modulus) mod Int64.modulus.
Proof.
 rewrite <-(Int64.repr_signed (smul128_hi_word a b)),Int64.unsigned_repr_eq.
 rewrite (proj1 (smul128_machine_observation a b));reflexivity.
Qed.

Lemma i128_signed_range lo hi : -2^127<=i128_signed_value lo hi<2^127.
Proof.
 unfold i128_signed_value.
 pose proof (Int64.signed_range hi) as H;pose proof (Int64.unsigned_range lo) as L.
 change Int64.min_signed with (-2^63) in H;change Int64.max_signed with (2^63-1) in H.
 change Int64.modulus with (2^64) in *;lia.
Qed.

Lemma i128_signed_mod lo hi :
 i128_signed_value lo hi mod (Int64.modulus*Int64.modulus)=
 Int64.unsigned hi*Int64.modulus+Int64.unsigned lo.
Proof.
 destruct (Int64.eqm_signed_unsigned hi) as (k & E).
 unfold i128_signed_value;rewrite E.
 replace ((k*Int64.modulus+Int64.unsigned hi)*Int64.modulus+Int64.unsigned lo) with
  ((Int64.unsigned hi*Int64.modulus+Int64.unsigned lo)+k*(Int64.modulus*Int64.modulus)) by ring.
 rewrite Z_mod_plus_full;apply Z.mod_small.
 pose proof (Int64.unsigned_range hi);pose proof (Int64.unsigned_range lo).
 change Int64.modulus with (2^64) in *;lia.
Qed.

Lemma i128_signed_add_mod lo hi z :
 (i128_signed_value lo hi+z) mod (Int64.modulus*Int64.modulus)=
 (Int64.unsigned hi*Int64.modulus+Int64.unsigned lo+z) mod (Int64.modulus*Int64.modulus).
Proof.
 destruct (Int64.eqm_signed_unsigned hi) as (k & E).
 unfold i128_signed_value;rewrite E.
 replace ((k*Int64.modulus+Int64.unsigned hi)*Int64.modulus+Int64.unsigned lo+z) with
  ((Int64.unsigned hi*Int64.modulus+Int64.unsigned lo+z)+k*(Int64.modulus*Int64.modulus)) by ring.
 rewrite Z_mod_plus_full;reflexivity.
Qed.

Lemma i128_signed_remainder_unique x y : -2^127<=x<2^127 -> -2^127<=y<2^127 ->
 x mod (Int64.modulus*Int64.modulus)=y mod (Int64.modulus*Int64.modulus) -> x=y.
Proof.
 intros X Y E.
 pose proof (Z.div_mod x (Int64.modulus*Int64.modulus) ltac:(change (2^128<>0);lia)).
 pose proof (Z.div_mod y (Int64.modulus*Int64.modulus) ltac:(change (2^128<>0);lia)).
 rewrite E in H;change Int64.modulus with (2^64) in *;lia.
Qed.

Lemma smul_accum_unsigned lo hi a b :
 let product := Int64.signed a*Int64.signed b in
 Int64.unsigned (smul_accum_hi_word lo hi a b)*Int64.modulus+
 Int64.unsigned (smul_accum_lo_word lo a b)=
 (Int64.unsigned hi*Int64.modulus+Int64.unsigned lo+product) mod (Int64.modulus*Int64.modulus).
Proof.
 intro product.
 assert (L : Int64.unsigned (smul_accum_lo_word lo a b)=
  (Int64.unsigned lo+product mod Int64.modulus) mod Int64.modulus).
 { unfold smul_accum_lo_word;rewrite Int64.add_unsigned,Int64.unsigned_repr_eq,
    (proj2 (smul128_machine_observation a b));reflexivity. }
 assert (H : Int64.unsigned (smul_accum_hi_word lo hi a b)=
  (Int64.unsigned hi+product/Int64.modulus+
   (Int64.unsigned lo+product mod Int64.modulus)/Int64.modulus) mod Int64.modulus).
 { unfold smul_accum_hi_word,smul_accum_lo_word.
   rewrite Int64.add_unsigned,Int64.unsigned_repr_eq.
   rewrite Int64.add_unsigned,Int64.unsigned_repr_eq.
   rewrite u64_add_carry_bit_right,smul128_hi_unsigned,
    (proj2 (smul128_machine_observation a b)).
   rewrite Z.add_mod_idemp_r by (pose proof Int64.modulus_pos;lia).
   rewrite <-(Z.add_mod_idemp_r (Int64.unsigned hi)) by (pose proof Int64.modulus_pos;lia).
   rewrite Z.add_mod_idemp_l by (pose proof Int64.modulus_pos;lia).
   rewrite Z.add_mod_idemp_r by (pose proof Int64.modulus_pos;lia).
   unfold product;rewrite Z.add_assoc;reflexivity. }
 rewrite H,L;apply accum_mul_two_limb_mod;pose proof Int64.modulus_pos;lia.
Qed.

Lemma smul_accum_signed_mod lo hi a b :
 i128_signed_value (smul_accum_lo_word lo a b) (smul_accum_hi_word lo hi a b)
  mod (Int64.modulus*Int64.modulus)=
 (i128_signed_value lo hi+Int64.signed a*Int64.signed b) mod (Int64.modulus*Int64.modulus).
Proof. rewrite i128_signed_mod,i128_signed_add_mod;apply smul_accum_unsigned. Qed.

Lemma smul_accum_exact_if_in_range lo hi a b :
 -2^127<=i128_signed_value lo hi+Int64.signed a*Int64.signed b<2^127 ->
 i128_signed_value (smul_accum_lo_word lo a b) (smul_accum_hi_word lo hi a b)=
 i128_signed_value lo hi+Int64.signed a*Int64.signed b.
Proof.
 intro Range;apply i128_signed_remainder_unique;
 [apply i128_signed_range|exact Range|apply smul_accum_signed_mod].
Qed.

Lemma smul_accum_lo_den rho layout : den rho layout smul_accum_lo=
 Vlong (smul_accum_lo_word (rho 2%nat) (rho 0%nat) (rho 1%nat)).
Proof. reflexivity. Qed.
Lemma smul_accum_hi_den rho layout : den rho layout smul_accum_hi=
 Vlong (smul_accum_hi_word (rho 2%nat) (rho 3%nat) (rho 0%nat) (rho 1%nat)).
Proof. reflexivity. Qed.

Theorem eval_i128_accum_mul_numeric rho layout m : rep rho layout smul_accum_regs m ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_i128_accum_mul)
  [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));Vlong (rho 0%nat);Vlong (rho 1%nat)] E0 mf Vundef /\
 Mem.load Mint64 mf (blk layout 0) (bas layout 0)=
  Some (Vlong (smul_accum_lo_word (rho 2%nat) (rho 0%nat) (rho 1%nat))) /\
 Mem.load Mint64 mf (blk layout 0) (bas layout 0+8)=
  Some (Vlong (smul_accum_hi_word (rho 2%nat) (rho 3%nat) (rho 0%nat) (rho 1%nat))) /\
 i128_signed_value (smul_accum_lo_word (rho 2%nat) (rho 0%nat) (rho 1%nat))
  (smul_accum_hi_word (rho 2%nat) (rho 3%nat) (rho 0%nat) (rho 1%nat))
  mod (Int64.modulus*Int64.modulus)=
 (i128_signed_value (rho 2%nat) (rho 3%nat)+Int64.signed (rho 0%nat)*Int64.signed (rho 1%nat))
  mod (Int64.modulus*Int64.modulus) /\
 rep rho layout smul_accum_out mf /\
 lframe (fun b ofs=>~foot layout (map rshape smul_accum_regs) b ofs) m mf.
Proof.
 intro Rep;destruct (eval_i128_accum_mul_symbolic rho layout m Rep) as (mf & Call & Out & Frame).
 pose proof (rep_region rho layout _ mf 0 _ Out eq_refl) as Region.
 pose proof (region_load rho layout mf 0 _ 0 Mint64 smul_accum_lo Region
  ltac:(cbn [smul_accum_out rcells u64_cells];left;reflexivity)) as Low.
 pose proof (region_load rho layout mf 0 _ 8 Mint64 smul_accum_hi Region
  ltac:(cbn [smul_accum_out rcells u64_cells];right;left;reflexivity)) as High.
 rewrite Z.add_0_r,smul_accum_lo_den in Low;rewrite smul_accum_hi_den in High.
 exists mf;split;[exact Call|];split;[exact Low|];split;[exact High|];
 split;[apply smul_accum_signed_mod|];split;assumption.
Qed.
