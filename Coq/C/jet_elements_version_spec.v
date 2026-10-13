(** Bridge the actual unsigned C version carrier to the Elements Version
    primitive (an unsigned 32-bit word in the canonical semantics).
    Not public C jet coverage without the actual function execution. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word C.jet_elements_prim.
Require Import C.jet_wide C.jet_wide_spec C.jet_word_repr.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma elements_version_carrier_matches_primitive r (environment : Elements.env) :
  Int64.unsigned r = Int.unsigned (sigTxVersion (Elements.envTx environment)) ->
  Some (decode_wide W32 (Int64.zero_ext 32 r)) =
    Elements.sem Elements.Version tt environment.
Proof.
  intro Hr.
  change (Some (@fromZ (WordToZ 5) (Int64.unsigned (Int64.zero_ext 32 r))) =
    Some (@fromZ (WordToZ 5) (Int.unsigned (sigTxVersion (Elements.envTx environment))))).
  rewrite Int64.zero_ext_mod by (change (0 <= 32 < 64); lia).
  change (Some (@fromZ (WordToZ 5) (Int64.unsigned r mod 4294967296)) =
    Some (@fromZ (WordToZ 5) (Int.unsigned (sigTxVersion (Elements.envTx environment))))).
  rewrite Hr, Z.mod_small by (pose proof (Int.unsigned_range (sigTxVersion (Elements.envTx environment))); exact H).
  reflexivity.
Qed.
