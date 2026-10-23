(** Machine observations of the actual signed product's partial words. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers Values AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jet_secp_i128_mul_exec C.jet_secp_i128_mul_arith.
Require Import C.jet_sx_expr.
Require Import C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_secp_linkage C.jets_secp.
Require Import C.jet_umul128_value C.jet_divmod96_value C.jet_secp_modinv_normalize62_words.
Require Import C.jet_secp_i128_shift62_numeric.
Local Open Scope Z_scope.
Import ListNotations.
Set Default Timeout 10.

Definition smul128_low32 := C.jet_umul128_value.umul128_low.
Definition smul128_high32 a := Int64.shr a (Int64.repr 32).
Definition smul128_ll_word := C.jet_umul128_value.umul128_ll.
Definition smul128_lh_word a b := Int64.mul (smul128_low32 a) (smul128_high32 b).
Definition smul128_hl_word a b := Int64.mul (smul128_high32 a) (smul128_low32 b).
Definition smul128_hh_word a b := Int64.mul (smul128_high32 a) (smul128_high32 b).
Definition smul128_mid_word a b := C.jet_umul128_value.umul128_mid
 (smul128_ll_word a b) (smul128_lh_word a b) (smul128_hl_word a b).
Definition smul128_lo_word a b := C.jet_umul128_value.umul128_lo
 (smul128_ll_word a b) (smul128_mid_word a b).
Definition smul128_hi_word a b := Int64.add
 (Int64.add (Int64.add (smul128_hh_word a b) (smul128_high32 (smul128_lh_word a b)))
  (smul128_high32 (smul128_hl_word a b))) (divmod96_high (smul128_mid_word a b)).

Lemma smul128_lo_den rho layout : den rho layout smul128_lo=
 Vlong (smul128_lo_word (rho 0%nat) (rho 1%nat)).
Proof. reflexivity. Qed.
Lemma smul128_hi_den rho layout : den rho layout smul128_hi=
 Vlong (smul128_hi_word (rho 0%nat) (rho 1%nat)).
Proof. reflexivity. Qed.

Lemma smul128_mod32_bits w : Int64.unsigned w mod 2^32=Int64.signed w mod 2^32.
Proof.
 destruct (Int64.eqm_signed_unsigned w) as (k & E);rewrite E.
 change Int64.modulus with ((2^32)*(2^32)).
 replace (k*(2^32*2^32)+Int64.unsigned w) with
  (Int64.unsigned w+(k*2^32)*2^32) by ring.
 rewrite Z_mod_plus_full;reflexivity.
Qed.
Lemma smul128_low32_unsigned w :
 Int64.unsigned (smul128_low32 w)=Int64.signed w mod 2^32.
Proof. unfold smul128_low32;rewrite umul128_low_unsigned,smul128_mod32_bits;reflexivity. Qed.
Lemma smul128_low32_signed w :
 Int64.signed (smul128_low32 w)=Int64.signed w mod 2^32.
Proof.
 rewrite Int64.signed_eq_unsigned;[apply smul128_low32_unsigned|].
 rewrite smul128_low32_unsigned.
 pose proof (Z.mod_pos_bound (Int64.signed w) (2^32) ltac:(lia)).
 change Int64.max_signed with (2^63-1);lia.
Qed.
Lemma smul128_word_signed_range w : -2^63<=Int64.signed w<2^63.
Proof.
 pose proof (Int64.signed_range w).
 change Int64.min_signed with (-2^63) in *;change Int64.max_signed with (2^63-1) in *;lia.
Qed.
Lemma smul128_mul_signed a b :
 Int64.min_signed<=Int64.signed a*Int64.signed b<=Int64.max_signed ->
 Int64.signed (Int64.mul a b)=Int64.signed a*Int64.signed b.
Proof. intro Bound;rewrite Int64.mul_signed;apply Int64.signed_repr;exact Bound. Qed.

Lemma smul128_ll_unsigned a b : Int64.unsigned (smul128_ll_word a b)=
 (Int64.signed a mod 2^32)*(Int64.signed b mod 2^32).
Proof.
 unfold smul128_ll_word,umul128_ll.
 rewrite umul128_mul_unsigned.
 - rewrite <-!smul128_low32_unsigned;reflexivity.
 - rewrite !smul128_low32_unsigned.
   pose proof (Z.mod_pos_bound (Int64.signed a) (2^32) ltac:(lia)).
   pose proof (Z.mod_pos_bound (Int64.signed b) (2^32) ltac:(lia)).
   change Int64.modulus with (2^64);nia.
Qed.

Lemma smul128_lh_signed a b : Int64.signed (smul128_lh_word a b)=
 (Int64.signed a mod 2^32)*(Int64.signed b/2^32).
Proof.
 unfold smul128_lh_word,smul128_high32.
 rewrite smul128_mul_signed.
 - rewrite smul128_low32_signed,norm62_signed_shr by lia;reflexivity.
 - rewrite smul128_low32_signed,norm62_signed_shr by lia.
   pose proof (smul128_half_bounds (Int64.signed b) (smul128_word_signed_range b)) as (BM & BH).
   pose proof (smul128_low_high_product (Int64.signed a mod 2^32) (Int64.signed b/2^32)
    (Z.mod_pos_bound (Int64.signed a) (2^32) ltac:(lia)) BH).
   change Int64.min_signed with (-2^63);change Int64.max_signed with (2^63-1);lia.
Qed.

Lemma smul128_hl_signed a b : Int64.signed (smul128_hl_word a b)=
 (Int64.signed a/2^32)*(Int64.signed b mod 2^32).
Proof.
 unfold smul128_hl_word,smul128_high32.
 rewrite smul128_mul_signed.
 - rewrite smul128_low32_signed,norm62_signed_shr by lia;reflexivity.
 - rewrite smul128_low32_signed,norm62_signed_shr by lia.
   pose proof (smul128_half_bounds (Int64.signed a) (smul128_word_signed_range a)) as (AM & AH).
   pose proof (smul128_low_high_product (Int64.signed b mod 2^32) (Int64.signed a/2^32)
    (Z.mod_pos_bound (Int64.signed b) (2^32) ltac:(lia)) AH).
   change Int64.min_signed with (-2^63);change Int64.max_signed with (2^63-1);nia.
Qed.

Lemma smul128_hh_signed a b : Int64.signed (smul128_hh_word a b)=
 (Int64.signed a/2^32)*(Int64.signed b/2^32).
Proof.
 unfold smul128_hh_word,smul128_high32.
 rewrite smul128_mul_signed.
 - rewrite !norm62_signed_shr by lia;reflexivity.
 - rewrite !norm62_signed_shr by lia.
   pose proof (smul128_half_bounds (Int64.signed a) (smul128_word_signed_range a)) as (AM & AH).
   pose proof (smul128_half_bounds (Int64.signed b) (smul128_word_signed_range b)) as (BM & BH).
   pose proof (smul128_high_high_product _ _ AH BH).
   change Int64.min_signed with (-2^63);change Int64.max_signed with (2^63-1);lia.
Qed.

Lemma smul128_mid_unsigned a b : Int64.unsigned (smul128_mid_word a b)=
 ((Int64.signed a mod 2^32)*(Int64.signed b mod 2^32))/2^32+
 ((Int64.signed a mod 2^32)*(Int64.signed b/2^32)) mod 2^32+
 ((Int64.signed a/2^32)*(Int64.signed b mod 2^32)) mod 2^32.
Proof.
 pose proof (smul128_limb_balance (2^32) (Int64.signed a) (Int64.signed b) ltac:(lia))
  as (RLL & RMID & RLO & Balance & HI & LO).
 unfold smul128_mid_word,umul128_mid.
 rewrite umul128_sum3_unsigned;
  rewrite divmod96_high_unsigned,!smul128_low32_unsigned,
   smul128_ll_unsigned,smul128_lh_signed,smul128_hl_signed.
 - reflexivity.
 - change Int64.modulus with (2^64);change divmod96_radix with (2^32);lia.
Qed.

Lemma smul128_logical_high_signed w :
 Int64.signed (divmod96_high w)=Int64.unsigned w/2^32.
Proof.
 rewrite Int64.signed_eq_unsigned.
 - apply divmod96_high_unsigned.
 - rewrite divmod96_high_unsigned.
   pose proof (Int64.unsigned_range w) as Range.
   change Int64.modulus with (2^64) in Range.
   change Int64.max_signed with (2^63-1).
   assert (Q : Int64.unsigned w/2^32<2^32) by (apply Z.div_lt_upper_bound;lia).
   change divmod96_radix with (2^32);lia.
Qed.

Lemma smul128_hi_signed a b : Int64.signed (smul128_hi_word a b)=
 (Int64.signed a/2^32)*(Int64.signed b/2^32)+
 ((Int64.signed a mod 2^32)*(Int64.signed b/2^32))/2^32+
 ((Int64.signed a/2^32)*(Int64.signed b mod 2^32))/2^32+
 Int64.unsigned (smul128_mid_word a b)/2^32.
Proof.
 pose proof (smul128_half_bounds (Int64.signed a) (smul128_word_signed_range a)) as (AM & AH).
 pose proof (smul128_half_bounds (Int64.signed b) (smul128_word_signed_range b)) as (BM & BH).
 pose proof (smul128_high_high_product _ _ AH BH) as HH.
 pose proof (smul128_low_high_product _ _ AM BH) as LH.
 pose proof (smul128_low_high_product _ _ BM AH) as HL.
 assert (LQ : -2^31<=((Int64.signed a mod 2^32)*(Int64.signed b/2^32))/2^32<2^31).
 { split;[apply Z.div_le_lower_bound|apply Z.div_lt_upper_bound];lia. }
 assert (HQ : -2^31<=((Int64.signed a/2^32)*(Int64.signed b mod 2^32))/2^32<2^31).
 { split;[apply Z.div_le_lower_bound|apply Z.div_lt_upper_bound];nia. }
 pose proof (smul128_limb_balance (2^32) (Int64.signed a) (Int64.signed b) ltac:(lia))
  as (RLL & RMID & RLO & Balance & HI & LO).
 rewrite <-smul128_mid_unsigned in RMID.
 assert (MQ : 0<=Int64.unsigned (smul128_mid_word a b)/2^32<3).
 { split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia. }
 unfold smul128_hi_word.
 assert (E1 : Int64.signed (Int64.add (smul128_hh_word a b) (smul128_high32 (smul128_lh_word a b)))=
  (Int64.signed a/2^32)*(Int64.signed b/2^32)+
  ((Int64.signed a mod 2^32)*(Int64.signed b/2^32))/2^32).
 { rewrite norm62_signed_add.
   - unfold smul128_high32;rewrite norm62_signed_shr by lia;
      rewrite smul128_hh_signed,smul128_lh_signed;reflexivity.
   - unfold smul128_high32;rewrite norm62_signed_shr by lia;
      rewrite smul128_hh_signed,smul128_lh_signed;
      change Int64.min_signed with (-2^63);change Int64.max_signed with (2^63-1);lia. }
 assert (E2 : Int64.signed (Int64.add
  (Int64.add (smul128_hh_word a b) (smul128_high32 (smul128_lh_word a b)))
   (smul128_high32 (smul128_hl_word a b)))=
  (Int64.signed a/2^32)*(Int64.signed b/2^32)+
  ((Int64.signed a mod 2^32)*(Int64.signed b/2^32))/2^32+
  ((Int64.signed a/2^32)*(Int64.signed b mod 2^32))/2^32).
 { rewrite norm62_signed_add.
   - rewrite E1;unfold smul128_high32;rewrite norm62_signed_shr by lia;
      rewrite smul128_hl_signed;reflexivity.
   - rewrite E1;unfold smul128_high32;rewrite norm62_signed_shr by lia;
      rewrite smul128_hl_signed;
      change Int64.min_signed with (-2^63);change Int64.max_signed with (2^63-1);lia. }
 rewrite norm62_signed_add.
 - rewrite E2,smul128_logical_high_signed;reflexivity.
 - rewrite E2,smul128_logical_high_signed;
    change Int64.min_signed with (-2^63);change Int64.max_signed with (2^63-1);lia.
Qed.

Theorem smul128_machine_observation a b :
 Int64.signed (smul128_hi_word a b)=(Int64.signed a*Int64.signed b)/Int64.modulus /\
 Int64.unsigned (smul128_lo_word a b)=(Int64.signed a*Int64.signed b) mod Int64.modulus.
Proof.
 pose proof (smul128_limb_balance (2^32) (Int64.signed a) (Int64.signed b) ltac:(lia))
  as (RLL & RMID & RLO & Balance & HI & LO).
 change Int64.modulus with ((2^32)*(2^32)).
 split.
 - rewrite smul128_hi_signed,smul128_mid_unsigned;exact HI.
 - unfold smul128_lo_word;rewrite umul128_lo_modular,Int64.unsigned_repr_eq,
    smul128_mid_unsigned,umul128_low_unsigned,smul128_ll_unsigned,<-LO.
   symmetry;apply Z.mod_unique with
    ((((Int64.signed a mod 2^32)*(Int64.signed b mod 2^32))/2^32+
    ((Int64.signed a mod 2^32)*(Int64.signed b/2^32)) mod 2^32+
    ((Int64.signed a/2^32)*(Int64.signed b mod 2^32)) mod 2^32)/2^32).
   + left;exact RLO.
   + pose proof (Z.div_mod
      (((Int64.signed a mod 2^32)*(Int64.signed b mod 2^32))/2^32+
      ((Int64.signed a mod 2^32)*(Int64.signed b/2^32)) mod 2^32+
      ((Int64.signed a/2^32)*(Int64.signed b mod 2^32)) mod 2^32) (2^32) ltac:(lia)).
     change divmod96_radix with (2^32);change Int64.modulus with ((2^32)*(2^32));nia.
Qed.

Theorem smul128_exact_product a b :
 i128_signed_value (smul128_lo_word a b) (smul128_hi_word a b)=Int64.signed a*Int64.signed b.
Proof.
 destruct (smul128_machine_observation a b) as (HI & LO).
 unfold i128_signed_value;rewrite HI,LO.
 pose proof (Z.div_mod (Int64.signed a*Int64.signed b) Int64.modulus ltac:(change (2^64<>0);lia)).
 lia.
Qed.

Theorem eval_i128_mul_exact rho layout m : rep rho layout smul128_regs m ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_i128_mul)
  [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));Vlong (rho 0%nat);Vlong (rho 1%nat)] E0 mf Vundef /\
 Mem.load Mint64 mf (blk layout 0) (bas layout 0)=
  Some (Vlong (smul128_lo_word (rho 0%nat) (rho 1%nat))) /\
 Mem.load Mint64 mf (blk layout 0) (bas layout 0+8)=
  Some (Vlong (smul128_hi_word (rho 0%nat) (rho 1%nat))) /\
 i128_signed_value (smul128_lo_word (rho 0%nat) (rho 1%nat))
  (smul128_hi_word (rho 0%nat) (rho 1%nat))=Int64.signed (rho 0%nat)*Int64.signed (rho 1%nat) /\
 rep rho layout smul128_out mf /\
 lframe (fun b ofs=>~foot layout (map rshape smul128_regs) b ofs) m mf.
Proof.
 intro Rep;destruct (eval_i128_mul_symbolic rho layout m Rep) as (mf & Call & Out & Frame).
 pose proof (rep_region rho layout _ mf 0 _ Out eq_refl) as Region.
 pose proof (region_load rho layout mf 0 _ 0 Mint64 smul128_lo Region
  ltac:(cbn [smul128_out rcells u64_cells];left;reflexivity)) as Low.
 pose proof (region_load rho layout mf 0 _ 8 Mint64 smul128_hi Region
  ltac:(cbn [smul128_out rcells u64_cells];right;left;reflexivity)) as High.
 rewrite Z.add_0_r,smul128_lo_den in Low;rewrite smul128_hi_den in High.
 exists mf;split;[exact Call|];split;[exact Low|];split;[exact High|];
 split;[apply smul128_exact_product|];split;assumption.
Qed.
