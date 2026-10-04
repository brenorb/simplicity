(** Literal port of Programs.Bitcoin.buildTapleafSimplicity
      buildTapleafSimplicity = (unit >>> tapleafPrefix)
        &&& ((unit >>> (simplicityVersion &&& scribe (toWord8 32))) &&& iden >>> full_shift word16 word256 >>>
             (oh &&& ((((ih &&& (unit >>> scribe (toWord16 0x8000))) &&& (unit >>> zero word32))
                        &&& (unit >>> zero word64)) &&& (unit >>> scribe (toWord128 (512+16+256))))))
        >>> hashBlock
    ([full_shift word16 word256] is [full_right_shift1] over sixteen 16-bit
    elements), and the bytes of the block it compresses.  No C execution here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Simplicity.Alg Simplicity.SHA256.
Require Import C.jet_word_repr C.jet_buffer_input C.jet_read8s_layout C.jet_read32s_layout C.jet_word32_chunks.
Require Import C.jet_sha_ctx8_model C.jet_sha_be32_exec C.jet_sha_be32_write.
Require Import C.jet_sha_tapdata_spec C.jet_bitcoin_tapleaf_hash_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

Module AC := Alg.Core.Combinators.

(** ** The big-endian bytes of a 32-bit word and of a hash *)
Lemma be_bytes_word (w : Ty.tySem (Word 5)) :
  c_be32_bytes (Int64.repr (Int.unsigned (word32_array_value w))) =
    map word8_array_value (word_bytes w).
Proof.
  destruct w as [[b0 b1] [b2 b3]].
  change (word_bytes (b0, b1, (b2, b3))) with [b0; b1; b2; b3]. cbn [map].
  pose proof (word_toZ_range 3 b0) as R0. pose proof (word_toZ_range 3 b1) as R1.
  pose proof (word_toZ_range 3 b2) as R2. pose proof (word_toZ_range 3 b3) as R3.
  change (2 ^ Z.of_nat (Nat.pow 2 3)) with 256 in R0, R1, R2, R3.
  set (t0 := @toZ (WordToZ 3) b0) in *. set (t1 := @toZ (WordToZ 3) b1) in *.
  set (t2 := @toZ (WordToZ 3) b2) in *. set (t3 := @toZ (WordToZ 3) b3) in *.
  assert (HT : @toZ (WordToZ 5) (b0, b1, (b2, b3)) = (t0 * 256 + t1) * 65536 + (t2 * 256 + t3))
    by reflexivity.
  set (W := (t0 * 256 + t1) * 65536 + (t2 * 256 + t3)) in *.
  assert (HWr : 0 <= W < 4294967296) by (unfold W; lia).
  change (word32_array_value (b0, b1, (b2, b3))) with (Int.repr W).
  rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  assert (HX : Int64.unsigned (Int64.repr W) = W)
    by (apply Int64.unsigned_repr; change Int64.max_unsigned with 18446744073709551615; lia).
  unfold c_be32_bytes.
  rewrite !zero_ext8_loword, !and255_unsigned.
  rewrite (shru64_unsigned (Int64.repr W) 24), (shru64_unsigned (Int64.repr W) 16),
    (shru64_unsigned (Int64.repr W) 8) by lia. rewrite HX.
  change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  assert (E3 : W / 16777216 = t0)
    by (symmetry; apply (Z.div_unique_pos W 16777216 t0 (t1 * 65536 + t2 * 256 + t3)); unfold W; lia).
  assert (E2 : W / 65536 = t0 * 256 + t1)
    by (symmetry; apply (Z.div_unique_pos W 65536 (t0 * 256 + t1) (t2 * 256 + t3)); unfold W; lia).
  assert (E1 : W / 256 = (t0 * 256 + t1) * 256 + t2)
    by (symmetry; apply (Z.div_unique_pos W 256 ((t0 * 256 + t1) * 256 + t2) t3); unfold W; lia).
  rewrite E3, E2, E1. rewrite !Z.mod_mod by lia.
  assert (M3 : t0 mod 256 = t0) by (apply Z.mod_small; lia).
  assert (M2 : (t0 * 256 + t1) mod 256 = t1)
    by (rewrite Z.add_comm, Z.mod_add by lia; apply Z.mod_small; lia).
  assert (M1 : ((t0 * 256 + t1) * 256 + t2) mod 256 = t2)
    by (rewrite Z.add_comm, Z.mod_add by lia; apply Z.mod_small; lia).
  assert (M0 : W mod 256 = t3).
  { unfold W. replace ((t0 * 256 + t1) * 65536 + (t2 * 256 + t3)) with
      (t3 + ((t0 * 256 + t1) * 256 + t2) * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite M3, M2, M1, M0. reflexivity.
Qed.

Lemma be_bytes_words (ws : list (Ty.tySem (Word 5))) :
  be_bytes (map word32_array_value ws) = map word8_array_value (flat_map word_bytes ws).
Proof.
  induction ws as [|w ws IH]; [reflexivity|].
  unfold be_bytes in *. cbn [map flat_map]. rewrite map_app, IH, be_bytes_word. reflexivity.
Qed.

Lemma be_bytes_state_regs (h : Ty.tySem (Word 8)) :
  be_bytes (state_regs h) = map word8_array_value (vector_values (Word 3) 5 h).
Proof. unfold state_regs. rewrite be_bytes_words. reflexivity. Qed.

(** ** The program *)
Definition tl_version : Ty.tySem (Word 3) := @fromZ (WordToZ 3) 190.
Definition tl_w8000 : Ty.tySem (Word 4) := @fromZ (WordToZ 4) 32768.
Definition tl_len : Ty.tySem (Word 7) := @fromZ (WordToZ 7) 784.

Definition build_tapleaf_block {term : Alg.Core.Algebra} : @Alg.Core.domain term (Word 8) (Word 9) :=
  AC.comp
    (AC.pair (AC.comp AC.unit (AC.pair (Alg.scribe tl_version) (Alg.scribe byte32))) AC.iden)
    (AC.comp (@Word.full_right_shift1 (Word 4) 4 term)
      (AC.pair (AC.take AC.iden)
        (AC.pair
          (AC.pair
            (AC.pair (AC.pair (AC.drop AC.iden) (AC.comp AC.unit (Alg.scribe tl_w8000)))
              (AC.comp AC.unit (@Word.zero 5 term)))
            (AC.comp AC.unit (@Word.zero 6 term)))
          (AC.comp AC.unit (Alg.scribe tl_len))))).

Definition build_tapleaf_spec {term : Alg.Core.Algebra} : @Alg.Core.domain term (Word 8) (Word 8) :=
  AC.comp (AC.pair (AC.comp AC.unit (Alg.scribe tapleaf_prefix)) (@build_tapleaf_block term))
    (@Simplicity.SHA256.hashBlock term).

Lemma build_tapleaf_spec_parametric : Alg.Core.Parametric (@build_tapleaf_spec).
Proof.
  intros alg1 alg2 R. unfold build_tapleaf_spec, build_tapleaf_block.
  assert (US : forall A B (v : Ty.tySem B),
    @Alg.Core.Parametric.rel _ _ R A B (AC.comp AC.unit (Alg.scribe v)) (AC.comp AC.unit (Alg.scribe v))).
  { intros A B v. apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply Alg.scribe_Parametric]. }
  assert (UZ : forall A n, @Alg.Core.Parametric.rel _ _ R A (Word n) (AC.comp AC.unit (@Word.zero n alg1)) (AC.comp AC.unit (@Word.zero n alg2))).
  { intros A n. apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply Word.zero_Parametric]. }
  apply Alg.comp_Parametric; [|apply Simplicity.SHA256.hashBlock_Parametric].
  apply Alg.pair_Parametric; [apply US|].
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [|apply Alg.iden_Parametric].
    apply Alg.comp_Parametric; [apply Alg.unit_Parametric|].
    apply Alg.pair_Parametric; apply Alg.scribe_Parametric.
  - apply Alg.comp_Parametric; [apply Word.full_right_shift1_Parametric|].
    apply Alg.pair_Parametric; [apply Alg.take_Parametric, Alg.iden_Parametric|].
    apply Alg.pair_Parametric; [|apply US].
    apply Alg.pair_Parametric; [|apply UZ].
    apply Alg.pair_Parametric; [|apply UZ].
    apply Alg.pair_Parametric; [apply Alg.drop_Parametric, Alg.iden_Parametric|apply US].
Qed.

Definition tl_pad : list (Ty.tySem (Word 3)) :=
  map (@fromZ (WordToZ 3)) ([128] ++ repeat 0 27 ++ [3; 16]).

Lemma build_tapleaf_block_bytes (a : Ty.tySem (Word 8)) :
  vector_values (Word 3) 6 (@build_tapleaf_block Alg.CoreFunSem a) =
    [tl_version; byte32] ++ vector_values (Word 3) 5 a ++ tl_pad.
Proof.
  destruct a as [[[[[b0 b1] [b2 b3]] [[b4 b5] [b6 b7]]] [[[b8 b9] [b10 b11]] [[b12 b13] [b14 b15]]]] [[[[b16 b17] [b18 b19]] [[b20 b21] [b22 b23]]] [[[b24 b25] [b26 b27]] [[b28 b29] [b30 b31]]]]].
  vm_compute. reflexivity.
Qed.

Lemma build_tapleaf_spec_value (a : Ty.tySem (Word 8)) :
  @build_tapleaf_spec Alg.CoreFunSem a =
    @Simplicity.SHA256.hashBlock Alg.CoreFunSem (tapleaf_prefix, @build_tapleaf_block Alg.CoreFunSem a).
Proof.
  unfold build_tapleaf_spec.
  change (@Simplicity.SHA256.hashBlock Alg.CoreFunSem
      (@Alg.scribe Ty.Unit (Word 8) tapleaf_prefix Alg.CoreFunSem tt, @build_tapleaf_block Alg.CoreFunSem a) =
    @Simplicity.SHA256.hashBlock Alg.CoreFunSem (tapleaf_prefix, @build_tapleaf_block Alg.CoreFunSem a)).
  rewrite Alg.scribe_correct. reflexivity.
Qed.
