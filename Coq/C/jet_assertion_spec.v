(** Literal Programs.Bit.verify, including its canonical pruned-branch hash.
    Option semantics distinguish a successful unit result from assertion failure. *)
From Coq Require Import List.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Bit Simplicity.Util.Option.
Require Simplicity.Digest Simplicity.MerkleRoot.
Import ListNotations.
Set Default Timeout 10.

Definition assertion_hash0 : Simplicity.Digest.hash256 :=
  Simplicity.Digest.Hash256
    [Int.zero; Int.zero; Int.zero; Int.zero; Int.zero; Int.zero; Int.zero; Int.zero]
    eq_refl.
Definition assertion_cmr_fail0 : Simplicity.Digest.hash256 :=
  @Alg.Assertion.Combinators.fail Ty.Unit Ty.Unit
    Simplicity.MerkleRoot.CommitmentRoot_Assertion_alg (assertion_hash0, assertion_hash0).

Definition verify_spec {term : Alg.Assertion.Algebra} : term Bit Ty.Unit :=
  Alg.Core.Combinators.comp
    (Alg.Core.Combinators.pair Alg.Core.Combinators.iden Alg.Core.Combinators.unit)
    (Alg.Assertion.Combinators.assertr assertion_cmr_fail0
      (Alg.Core.Combinators.take Alg.Core.Combinators.iden)).

Lemma verify_spec_parametric : Alg.Assertion.Parametric (@verify_spec).
Proof.
  intros alg1 alg2 [R [HC HA]].
  unfold verify_spec.
  apply (Alg.comp_Parametric (Alg.Core.Parametric.Pack HC)).
  - apply (Alg.pair_Parametric (Alg.Core.Parametric.Pack HC));
      [apply Alg.iden_Parametric|apply Alg.unit_Parametric].
  - apply (Alg.assertr_Parametric (Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA))).
    apply (Alg.take_Parametric (Alg.Core.Parametric.Pack HC)). apply Alg.iden_Parametric.
Qed.

Lemma verify_spec_option (x : Bit) :
  @verify_spec (Alg.AssertionSem option_Monad_Zero) x =
    if Bit.toBool x then Some tt else None.
Proof. destruct x as [u | u]; destruct u; reflexivity. Qed.
