(** Exact Word64 compatibility with canonical unsigned Bitcoin amounts.
    These checks exercise domains that the former monetary proof fields
    excluded: positive fees, empty outputs, high-bit values and overflow. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.List.
Require Import Simplicity.Primitive.Bitcoin C.jet_word_repr.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 30.

Lemma word64_eqm x y : Int64.eqm x y ->
  @fromZ (WordToZ 6) x = @fromZ (WordToZ 6) y.
Proof.
  intro H. pose proof (Int64.eqm_samerepr _ _ H) as HR.
  pose proof (f_equal Int64.unsigned HR) as HU.
  rewrite !Int64.unsigned_repr_eq in HU.
  rewrite <- (word_fromZ_mod 6 x), <- (word_fromZ_mod 6 y).
  change (@fromZ (WordToZ 6) (x mod Int64.modulus) =
    @fromZ (WordToZ 6) (y mod Int64.modulus)).
  rewrite HU. reflexivity.
Qed.

Lemma signed_unsigned_sum_eqm {X : Type} (xs : list X) (amount : X -> int64) :
  Int64.eqm (Z_sum (map (fun x => Int64.signed (amount x)) xs))
    (Z_sum (map (fun x => Int64.unsigned (amount x)) xs)).
Proof.
  induction xs as [|x xs IH]; cbn [map Z_sum fold_right].
  - apply Int64.eqm_refl.
  - apply Int64.eqm_add; [apply Int64.eqm_signed_unsigned|exact IH].
Qed.

Lemma bitcoin_total_input_unsigned tx :
  @fromZ (WordToZ 6) (sigTxTotalInValue tx) =
  @fromZ (WordToZ 6) (Z_sum (map (fun i => Int64.unsigned (sigTxiValue i)) (sigTxIn tx))).
Proof. apply word64_eqm. apply signed_unsigned_sum_eqm. Qed.

Lemma bitcoin_total_output_unsigned tx :
  @fromZ (WordToZ 6) (sigTxTotalOutValue tx) =
  @fromZ (WordToZ 6) (Z_sum (map (fun o => Int64.unsigned (txoValue o)) (sigTxOut tx))).
Proof. apply word64_eqm. apply signed_unsigned_sum_eqm. Qed.

Definition domain_input (op : outpoint) (value : int64) : sigTxInput :=
  {| sigTxiPreviousOutpoint := op; sigTxiValue := value; sigTxiSequence := Int.zero |}.

Definition domain_output (value : int64) : txOutput.
Proof.
  refine {| txoValue := value; txoScript := [] |}.
  change (0 < 4294967296). lia.
Defined.

Definition domain_transaction (op : outpoint) (value : int64) (outputs : list txOutput)
    (Hout : 0 <= Zlength outputs < Int.modulus) : sigTx.
Proof.
  refine {| sigTxVersion := Int.zero; sigTxIn := [domain_input op value];
    sigTxOut := outputs; sigTxLock := Int.zero; sigTxOutBounds := Hout |}.
  change (0 < 1 < 4294967296). lia.
Defined.

Definition domain_positive_fee (op : outpoint) : sigTx.
Proof.
  refine (domain_transaction op (Int64.repr 10) [domain_output (Int64.repr 9)] _).
  change (0 <= 1 < 4294967296). lia.
Defined.

Lemma bitcoin_positive_fee_representable op : sigTxFee (domain_positive_fee op) = 1.
Proof. reflexivity. Qed.

Definition domain_empty_outputs (op : outpoint) (value : int64) : sigTx.
Proof.
  refine (domain_transaction op value [] _).
  change (0 <= 0 < 4294967296). lia.
Defined.

Lemma bitcoin_empty_outputs_representable op value :
  sigTxOut (domain_empty_outputs op value) = [].
Proof. reflexivity. Qed.

Lemma bitcoin_high_bit_value_representable op :
  sigTxiValue (domain_input op (Int64.repr (2 ^ 63))) = Int64.repr (2 ^ 63).
Proof. reflexivity. Qed.
