(** Raw-data meaning of the extended Bitcoin primitives, following the pinned
    Haskell Bitcoin/DataTypes.hs and Bitcoin/Primitive.hs.  Cached C hashes are
    representations of these computations, not independent primitive inputs.
    The tap path bound belongs to projection into the C-compatible cache model;
    the raw semantics itself permits arbitrary paths. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import Simplicity.Primitive.Bitcoin C.jet_bitcoin_ext_prim.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 30.

Record raw_input_data :=
{ raw_redeemed_script : list byte
; raw_annex : option (list byte)
; raw_script_sig : list byte
}.

Record raw_bitcoin_environment :=
{ raw_base : Bitcoin.environment
; raw_inputs : list raw_input_data
; raw_inputs_length : length raw_inputs = length (sigTxIn (Bitcoin.envTx raw_base))
; raw_leaf_version : byte
; raw_tap_path : list hash256
; raw_internal_key : hash256
}.

Definition put_bytes_le (width : nat) (value : Z) : list byte :=
  map (fun i => Byte.repr (value / 2 ^ (8 * Z.of_nat i))) (seq 0 width).

(** The canonical non-witness serializer uses CompactSize for counts and
    lengths.  All representable C counts/lengths are below 2^32. *)
Definition put_compact_size (n : nat) : list byte :=
  let value := Z.of_nat n in
  if value <=? 252 then [Byte.repr value]
  else if value <=? 65535 then Byte.repr 253 :: put_bytes_le 2 value
  else if value <=? 4294967295 then Byte.repr 254 :: put_bytes_le 4 value
  else Byte.repr 255 :: put_bytes_le 8 value.

Definition put_raw_input (input : sigTxInput * raw_input_data) : list byte :=
  let '(txi, data) := input in
  putOutpoint (sigTxiPreviousOutpoint txi) ++
  put_compact_size (length (raw_script_sig data)) ++ raw_script_sig data ++
  putInt32le (sigTxiSequence txi).

Definition put_raw_output (output : txOutput) : list byte :=
  putInt64le (txoValue output) ++ put_compact_size (length (txoScript output)) ++ txoScript output.

Definition put_no_witness_transaction (environment : raw_bitcoin_environment) : list byte :=
  let tx := Bitcoin.envTx (raw_base environment) in
  putInt32le (sigTxVersion tx) ++ put_compact_size (length (sigTxIn tx)) ++
  concat (map put_raw_input (combine (sigTxIn tx) (raw_inputs environment))) ++
  put_compact_size (length (sigTxOut tx)) ++ concat (map put_raw_output (sigTxOut tx)) ++
  putInt32le (sigTxLock tx).

Definition raw_transaction_id (environment : raw_bitcoin_environment) : hash256 :=
  byteStringHash (hash256_to_bytelist (byteStringHash (put_no_witness_transaction environment))).

Definition project_raw_environment (environment : raw_bitcoin_environment)
    (Hpath : (length (raw_tap_path environment) <= 128)%nat) : ext_environment.
Proof.
  refine {| extBase := raw_base environment;
    extInScriptHash := map (fun i => byteStringHash (raw_redeemed_script i)) (raw_inputs environment);
    extInAnnexHash := map (fun i => option_map byteStringHash (raw_annex i)) (raw_inputs environment);
    extInScriptSigHash := map (fun i => byteStringHash (raw_script_sig i)) (raw_inputs environment);
    extTapleafVersion := Byte.unsigned (raw_leaf_version environment);
    extTappath := raw_tap_path environment;
    extInternalKey := raw_internal_key environment;
    extTxid := raw_transaction_id environment;
    extTappath_len := Hpath |}.
  - rewrite map_length. exact (raw_inputs_length environment).
  - rewrite map_length. exact (raw_inputs_length environment).
  - rewrite map_length. exact (raw_inputs_length environment).
  - exact (Byte.unsigned_range (raw_leaf_version environment)).
Defined.

Definition raw_ext_sem {A B} (p : BitcoinExt.t A B) (a : Ty.tySem A)
    (environment : raw_bitcoin_environment) : option (Ty.tySem B) :=
  let cast {C : Ty} (x : option (Ty.tySem C)) : Ty.tySem (Ty.Sum Ty.Unit C) :=
    match x with Some c => inr c | None => inl tt end in
  (match p in BitcoinExt.prim A B return Ty.tySem A -> option (Ty.tySem B) with
   | BitcoinExt.CurrentIndex => fun _ =>
       Some (fromZ (Z.of_nat (Bitcoin.envIx (raw_base environment))))
   | BitcoinExt.InputScriptHash => fun i =>
       Some (cast (option_map (fun data => from_hash256 (byteStringHash (raw_redeemed_script data)))
         (nth_error (raw_inputs environment) (Z.to_nat (toZ i)))))
   | BitcoinExt.InputAnnexHash => fun i =>
       Some (match nth_error (raw_inputs environment) (Z.to_nat (toZ i)) with
             | None => inl tt
             | Some data => inr (cast (option_map (fun bytes => from_hash256 (byteStringHash bytes)) (raw_annex data)))
             end)
   | BitcoinExt.InputScriptSigHash => fun i =>
       Some (cast (option_map (fun data => from_hash256 (byteStringHash (raw_script_sig data)))
         (nth_error (raw_inputs environment) (Z.to_nat (toZ i)))))
   | BitcoinExt.TapleafVersion => fun _ => Some (fromZ (Byte.unsigned (raw_leaf_version environment)))
   | BitcoinExt.Tappath => fun i =>
       Some (cast (option_map from_hash256 (nth_error (raw_tap_path environment) (Z.to_nat (toZ i)))))
   | BitcoinExt.InternalKey => fun _ => Some (from_hash256 (raw_internal_key environment))
   | BitcoinExt.TransactionId => fun _ => Some (from_hash256 (raw_transaction_id environment))
   end) a.

Lemma bitcoin_ext_raw_projection {A B} (p : BitcoinExt.t A B) a environment Hpath :
  BitcoinExt.sem p a (project_raw_environment environment Hpath) = raw_ext_sem p a environment.
Proof.
  destruct p; cbn [BitcoinExt.sem raw_ext_sem]; try reflexivity;
    cbn [extInScriptHash extInAnnexHash extInScriptSigHash project_raw_environment];
    rewrite nth_error_map; destruct (nth_error (raw_inputs environment) (Z.to_nat (toZ a))) as [data|];
    cbn; try reflexivity.
  destruct (raw_annex data); reflexivity.
Qed.
