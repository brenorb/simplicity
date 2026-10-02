(** Literal Haskell Programs.Sha256.Lib.ctx8Init:
    buffer63Empty &&& (zero word64 &&& iv). Buffer63 and bufferEmpty are
    ported without replacing the canonical program by an arithmetic formula.
    The actual C initializer/writer/lifecycle remain separate obligations. *)
From Coq Require Import ZArith List.
Require Import Simplicity.Word Simplicity.Alg Simplicity.Translate.
Require Import C.jet_buffer_empty_spec C.jet_sha256_iv_init C.jet_uint32_array_init.
Require Import C.jet_write32s_layout.
Import ListNotations.
Module AC := Alg.Core.Combinators.
Set Default Timeout 10.

Definition sha256_ctx8_type := Ty.Prod (buffer_type (Word 3) 5) (Ty.Prod (Word 6) (Word 8)).
Definition sha256_ctx8_init_spec {term : Alg.Core.Algebra} : term Ty.Unit sha256_ctx8_type :=
  AC.pair (buffer_empty_spec (Word 3) 5 Ty.Unit) (AC.pair (@Word.zero 6 term) (@sha256_iv_spec term)).

Lemma sha256_ctx8_init_spec_parametric : Alg.Core.Parametric (@sha256_ctx8_init_spec).
Proof.
  intros alg1 alg2 R. unfold sha256_ctx8_init_spec. apply Alg.pair_Parametric.
  - apply buffer_empty_spec_parametric.
  - apply Alg.pair_Parametric; [apply Word.zero_Parametric|apply sha256_iv_spec_parametric].
Qed.
Lemma sha256_ctx8_init_spec_value :
  @sha256_ctx8_init_spec Alg.CoreFunSem tt =
    (buffer_empty_value (Word 3) 5, (@Word.zero 6 Alg.CoreFunSem tt, @sha256_iv_spec Alg.CoreFunSem tt)).
Proof.
  change ((@buffer_empty_spec (Word 3) 5 Ty.Unit Alg.CoreFunSem tt,
    (@Word.zero 6 Alg.CoreFunSem tt, @sha256_iv_spec Alg.CoreFunSem tt)) =
    (buffer_empty_value (Word 3) 5, (@Word.zero 6 Alg.CoreFunSem tt, @sha256_iv_spec Alg.CoreFunSem tt))).
  rewrite buffer_empty_spec_value; reflexivity.
Qed.
Lemma encode_ctx_product A B (a : Ty.tySem A) (b : Ty.tySem B) :
  @encode (Ty.Prod A B) (a,b) = encode a ++ encode b.
Proof. reflexivity. Qed.
Lemma sha256_ctx8_init_spec_cells : encode (@sha256_ctx8_init_spec Alg.CoreFunSem tt) =
  buffer_empty_cells (Word 3) 5 ++
    (encode (@Word.zero 6 Alg.CoreFunSem tt) ++ uint32_word_cells sha256_iv_words).
Proof.
  rewrite sha256_ctx8_init_spec_value. unfold sha256_ctx8_type. rewrite !encode_ctx_product.
  rewrite buffer_empty_value_cells, sha256_iv_spec_cells; reflexivity.
Qed.
Lemma sha256_ctx8_type_bits : Translate.bitSize sha256_ctx8_type = 830%nat.
Proof. vm_compute; reflexivity. Qed.
