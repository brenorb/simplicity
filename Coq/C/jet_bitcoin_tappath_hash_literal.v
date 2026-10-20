(** Original tappath-hash C getter against the canonical primitive-bearing
    hashWord256s8 program. The existing environment/cache relation is retained. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_application_sep C.jets_bitcoin C.jet_bitcoin_linkage.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_bitcoin_words_hash.
Require Import C.jet_bitcoin_hash_getter_local C.jet_sha_hash_words_literal.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_bitcoin_tappath_hash {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  @literal_sha_hash_words 5 3 term Ty.Unit
    (@Alg.Core.Combinators.drop Ty.Unit (Word 3) (Ty.Sum Ty.Unit (Vector (Word 3) 5))
      (Alg.Assertion.toCore term) (@PF.Combinators.prim _ _ alg (BitcoinFull.Ext BitcoinExt.Tappath))).

Lemma literal_bitcoin_tappath_hash_matches alg :
  @literal_bitcoin_tappath_hash alg = @prim_words_hash_spec 5 3 (BitcoinFull.Ext BitcoinExt.Tappath) alg.
Proof.
  unfold literal_bitcoin_tappath_hash, prim_words_hash_spec.
  rewrite literal_sha_hash_words_matches. reflexivity.
Qed.

Theorem bitcoin_tappath_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tappath_hash bitcoin_ge ext_environment
    Ty.Unit Word256
    (hash_getter_rep (fun e => words_hash_of 5 3 (tappath_of e)) 8 40 176)
    (fun a environment => @literal_bitcoin_tappath_hash fullalg a environment).
Proof. rewrite literal_bitcoin_tappath_hash_matches. exact bitcoin_tappath_hash_local_spec. Qed.
