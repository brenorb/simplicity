(** Literal core programs from Haskell/Core/Simplicity/Programs/Elements.hs.
    These are dependencies of the primitive-based issuance getter specs,
    not claims about C execution or alternative arithmetic specifications. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.SHA256.
Require Import C.jet_sha256_iv_init.
Module IC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition issuance_op_hash_spec {core : Alg.Core.Algebra} :
    core (Ty.Prod Word256 Word32) Word256 :=
  IC.comp
    (IC.pair (IC.comp IC.unit sha256_iv_spec)
      (IC.pair
        (IC.comp
          (IC.pair (IC.comp IC.unit sha256_iv_spec)
            (IC.pair (IC.take IC.iden)
              (IC.pair
                (IC.pair
                  (IC.pair
                    (IC.drop (IC.pair
                      (IC.drop (IC.pair (IC.drop IC.iden) (IC.take IC.iden)))
                      (IC.take (IC.pair (IC.drop IC.iden) (IC.take IC.iden)))))
                    (Alg.scribe (@fromZ (WordToZ 5) (2 ^ 31))))
                  (IC.comp IC.unit (@Word.zero 6 core)))
                (IC.comp IC.unit (Alg.scribe (@fromZ (WordToZ 7) (256 + 32)))))))
          Simplicity.SHA256.hashBlock)
        (IC.comp IC.unit (Alg.scribe (@fromZ (WordToZ 8) (2 ^ 255 + 256))))))
    Simplicity.SHA256.hashBlock.

Ltac issuance_core_parametric :=
  solve [repeat first [apply sha256_iv_spec_parametric |
    apply Simplicity.SHA256.hashBlock_Parametric | apply Word.zero_Parametric |
    apply Alg.scribe_Parametric | apply Alg.comp_Parametric | apply Alg.pair_Parametric |
    apply Alg.take_Parametric | apply Alg.drop_Parametric | apply Alg.unit_Parametric |
    apply Alg.iden_Parametric]].

Lemma issuance_op_hash_spec_parametric : Alg.Core.Parametric (@issuance_op_hash_spec).
Proof. intros alg1 alg2 R. unfold issuance_op_hash_spec. issuance_core_parametric. Qed.

Definition calculate_issuance_entropy_spec {core : Alg.Core.Algebra} :
    core (Ty.Prod (Ty.Prod Word256 Word32) Word256) Word256 :=
  IC.comp (IC.pair (IC.comp IC.unit sha256_iv_spec)
    (IC.pair (IC.take issuance_op_hash_spec) (IC.drop IC.iden)))
    Simplicity.SHA256.hashBlock.

Lemma calculate_issuance_entropy_spec_parametric :
    Alg.Core.Parametric (@calculate_issuance_entropy_spec).
Proof.
  intros alg1 alg2 R. unfold calculate_issuance_entropy_spec.
  pose proof (issuance_op_hash_spec_parametric alg1 alg2 R) as HOp.
  solve [repeat first [exact HOp | apply sha256_iv_spec_parametric |
    apply Simplicity.SHA256.hashBlock_Parametric | apply Alg.comp_Parametric |
    apply Alg.pair_Parametric | apply Alg.take_Parametric | apply Alg.drop_Parametric |
    apply Alg.unit_Parametric | apply Alg.iden_Parametric]].
Qed.

Definition calculate_asset_spec {core : Alg.Core.Algebra} : core Word256 Word256 :=
  IC.comp (IC.pair (IC.comp IC.unit sha256_iv_spec)
    (IC.pair IC.iden (IC.comp IC.unit (@Word.zero 8 core))))
    Simplicity.SHA256.hashBlock.

Lemma calculate_asset_spec_parametric : Alg.Core.Parametric (@calculate_asset_spec).
Proof. intros alg1 alg2 R. unfold calculate_asset_spec. issuance_core_parametric. Qed.

Definition calculate_explicit_token_spec {core : Alg.Core.Algebra} : core Word256 Word256 :=
  IC.comp (IC.pair (IC.comp IC.unit sha256_iv_spec)
    (IC.pair IC.iden (IC.comp IC.unit (Alg.scribe (@fromZ (WordToZ 8) (2 ^ 248))))))
    Simplicity.SHA256.hashBlock.

Lemma calculate_explicit_token_spec_parametric : Alg.Core.Parametric (@calculate_explicit_token_spec).
Proof. intros alg1 alg2 R. unfold calculate_explicit_token_spec. issuance_core_parametric. Qed.

Definition calculate_confidential_token_spec {core : Alg.Core.Algebra} : core Word256 Word256 :=
  IC.comp (IC.pair (IC.comp IC.unit sha256_iv_spec)
    (IC.pair IC.iden (IC.comp IC.unit (Alg.scribe (@fromZ (WordToZ 8) (2 * 2 ^ 248))))))
    Simplicity.SHA256.hashBlock.

Lemma calculate_confidential_token_spec_parametric : Alg.Core.Parametric (@calculate_confidential_token_spec).
Proof. intros alg1 alg2 R. unfold calculate_confidential_token_spec. issuance_core_parametric. Qed.
