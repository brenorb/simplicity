(** Connect the actual signed128 C shift to its two's-complement integer
    value, for every input pattern (including negative high words). This is
    an inverse-batch dependency, not another registered jet. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Values Memory Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_i128_shift62.
Require Import C.jet_secp_modinv_normalize62_words.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition i128_signed_value lo hi := Int64.signed hi*Int64.modulus+Int64.unsigned lo.

Lemma i128_shru62_unsigned value :
 Int64.unsigned (Int64.shru value (Int64.repr 62))=Int64.unsigned value/2^62.
Proof.
 rewrite Int64.shru_div_two_p.
 change (Int64.unsigned (Int64.repr (Int64.unsigned value/2^62))=Int64.unsigned value/2^62).
 apply Int64.unsigned_repr.
 pose proof (Int64.unsigned_range value) as Range.
 change (0<=Int64.unsigned value<18446744073709551616) in Range.
 change (0<=Int64.unsigned value/2^62<=18446744073709551615).
 assert (Q : 0<=Int64.unsigned value/2^62<4).
 { split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia]. }
 lia.
Qed.

Lemma i128_shift62_low_unsigned lo hi :
 Int64.unsigned (i128_shift62_low lo hi)=
 (Int64.unsigned hi*4+Int64.unsigned lo/2^62) mod Int64.modulus.
Proof.
 unfold i128_shift62_low;rewrite Int64.mul_commut,Int64.mul_one.
 rewrite Int64.shifted_or_is_add.
 - rewrite Int64.unsigned_repr_eq,i128_shru62_unsigned;reflexivity.
 - change (0<=2<64);lia.
 - rewrite i128_shru62_unsigned.
   change (Int64.unsigned lo/2^62<4).
   apply Z.div_lt_upper_bound;[lia|].
   pose proof (Int64.unsigned_range lo);change Int64.modulus with 18446744073709551616 in *;lia.
Qed.

Lemma i128_shift62_low_signed lo hi :
 Int64.unsigned (i128_shift62_low lo hi)=
 (Int64.signed hi mod 2^62)*4+Int64.unsigned lo/2^62.
Proof.
 rewrite i128_shift62_low_unsigned,<-norm62_unsigned_signed_mod.
 pose proof (Z.div_mod (Int64.unsigned hi) (2^62) ltac:(lia)) as Division.
 pose proof (Z.mod_pos_bound (Int64.unsigned hi) (2^62) ltac:(lia)) as Rem.
 pose proof (Int64.unsigned_range lo) as Lo.
 change Int64.modulus with (4*2^62) in *.
 assert (Q : 0<=Int64.unsigned lo/2^62<4).
 { split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia]. }
 symmetry;apply Z.mod_unique with (Int64.unsigned hi/2^62);[left;nia|nia].
Qed.

Theorem i128_shift62_numeric lo hi :
 i128_signed_value (i128_shift62_low lo hi) (i128_shift62_high hi)=
 i128_signed_value lo hi/2^62.
Proof.
 unfold i128_signed_value,i128_shift62_high.
 rewrite norm62_signed_shr by lia;rewrite i128_shift62_low_signed.
 pose proof (Z.div_mod (Int64.signed hi) (2^62) ltac:(lia)) as High.
 pose proof (Z.div_mod (Int64.unsigned lo) (2^62) ltac:(lia)) as Low.
 pose proof (Z.mod_pos_bound (Int64.unsigned lo) (2^62) ltac:(lia)) as Rem.
 change Int64.modulus with (4*2^62).
 apply Z.div_unique with (Int64.unsigned lo mod 2^62);[left;lia|nia].
Qed.

Theorem eval_i128_shift62_exact m b lo hi :
 Mem.range_perm m b 0 16 Cur Writable ->
 Mem.load Mint64 m b 0=Some (Vlong lo) -> Mem.load Mint64 m b 8=Some (Vlong hi) ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_i128_rshift)
  (Vptr b Ptrofs.zero::Vint (Int.repr 62)::nil) E0 mf Vundef /\
 Mem.load Mint64 mf b 0=Some (Vlong (i128_shift62_low lo hi)) /\
 Mem.load Mint64 mf b 8=Some (Vlong (i128_shift62_high hi)) /\
 i128_signed_value (i128_shift62_low lo hi) (i128_shift62_high hi)=
   i128_signed_value lo hi/2^62 /\
 (forall bb ofs k p,Mem.perm m bb ofs k p -> Mem.perm mf bb ofs k p) /\
 lframe (fun bb ofs=>~(bb=b /\ 0<=ofs<16)) m mf.
Proof.
 intros Perm Lo Hi.
 destruct (eval_i128_shift62_from_storage m b lo hi Perm Lo Hi) as (mf & Call & OutLo & OutHi & Keep & Frame).
 exists mf;split;[exact Call|];split;[exact OutLo|];split;[exact OutHi|];
 split;[apply i128_shift62_numeric|];split;assumption.
Qed.
