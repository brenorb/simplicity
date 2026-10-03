(** Bridge the actual unsigned C version carrier to the canonical Bitcoin
    Version primitive, including versions negative under signed interpretation.
    Not public C jet coverage without the actual function execution. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Primitive.Bitcoin.
Require Import C.jet_wide C.jet_wide_spec C.jet_word_repr.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma bitcoin_version_word_signed_unsigned (version : Int.int) :
  @fromZ (WordToZ 5) (Int.unsigned version) = @fromZ (WordToZ 5) (Int.signed version).
Proof.
  assert (HM : Int.signed version mod 4294967296 = Int.unsigned version).
  { change (Int.signed version mod Int.modulus = Int.unsigned version).
    rewrite <- Int.unsigned_repr_eq, Int.repr_signed; reflexivity. }
  rewrite <- (word_fromZ_mod 5 (Int.signed version)).
  change (@fromZ (WordToZ 5) (Int.unsigned version) =
    @fromZ (WordToZ 5) (Int.signed version mod 4294967296)).
  rewrite HM; reflexivity.
Qed.

Lemma bitcoin_version_carrier_matches_primitive r (environment : Bitcoin.env) :
  Int64.unsigned r = Int.unsigned (sigTxVersion (Bitcoin.envTx environment)) ->
  Some (decode_wide W32 (Int64.zero_ext 32 r)) =
    Bitcoin.sem Bitcoin.Version tt environment.
Proof.
  intro Hr.
  change (Some (@fromZ (WordToZ 5) (Int64.unsigned (Int64.zero_ext 32 r))) =
    Some (@fromZ (WordToZ 5) (Int.signed (sigTxVersion (Bitcoin.envTx environment))))).
  rewrite Int64.zero_ext_mod by (change (0 <= 32 < 64); lia).
  change (Some (@fromZ (WordToZ 5) (Int64.unsigned r mod 4294967296)) =
    Some (@fromZ (WordToZ 5) (Int.signed (sigTxVersion (Bitcoin.envTx environment))))).
  rewrite Hr, Z.mod_small by (pose proof (Int.unsigned_range (sigTxVersion (Bitcoin.envTx environment))); exact H).
  rewrite bitcoin_version_word_signed_unsigned; reflexivity.
Qed.
