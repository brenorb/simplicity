(** Bitcoin primitives absent from the base Coq model: the per-input hashes of
    the redeemed output's script, the segwit annex and the scriptSig, the
    taproot leaf version and path, the internal key and the transaction id.
    They are specified exactly as in Haskell's [Simplicity.Bitcoin.Primitive];
    the environment extends the base [Bitcoin.env] by the data those primitives
    read.  [CurrentIndex] is repeated so that programs over this signature can
    compose it with the new primitives. *)
From Coq Require Import ZArith String List.
From compcert Require Import Integers.
Require Import Simplicity.Digest Simplicity.MerkleRoot Simplicity.Primitive Simplicity.Ty Simplicity.Word.
Require Import Simplicity.Primitive.Bitcoin.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Record ext_environment :=
{ extBase : Bitcoin.environment
; extInScriptHash : list hash256
; extInAnnexHash : list (option hash256)
; extInScriptSigHash : list hash256
; extTapleafVersion : Z
; extTappath : list hash256
; extInternalKey : hash256
; extTxid : hash256
; extInScriptHash_len : length extInScriptHash = length (sigTxIn (Bitcoin.envTx extBase))
; extInAnnexHash_len : length extInAnnexHash = length (sigTxIn (Bitcoin.envTx extBase))
; extInScriptSigHash_len : length extInScriptSigHash = length (sigTxIn (Bitcoin.envTx extBase))
; extTapleafVersion_range : 0 <= extTapleafVersion < 256
; extTappath_len : (length extTappath <= 128)%nat
}.

Module BitcoinExt <: PrimitiveSig.

Inductive prim : Ty -> Ty -> Set :=
| CurrentIndex : prim Unit Word32
| InputScriptHash : prim Word32 (Sum Unit Word256)
| InputAnnexHash : prim Word32 (Sum Unit (Sum Unit Word256))
| InputScriptSigHash : prim Word32 (Sum Unit Word256)
| TapleafVersion : prim Unit Word8
| Tappath : prim Word8 (Sum Unit Word256)
| InternalKey : prim Unit Word256
| TransactionId : prim Unit Word256.
Definition t := prim.

Definition primName : string := "BitcoinExt".

Definition name {a b} (p : t a b) : string :=
match p with
| CurrentIndex => "currentIndex"
| InputScriptHash => "inputScriptHash"
| InputAnnexHash => "inputAnnexHash"
| InputScriptSigHash => "inputScriptSigHash"
| TapleafVersion => "tapleafVersion"
| Tappath => "tappath"
| InternalKey => "internalKey"
| TransactionId => "transactionId"
end.

Definition tag_def {A B} (p : t A B) : hash256.
pose (nm := name p).
revert p nm; intros [] nm;
exact (MerkleRoot.tag (primitivePrefix primName ++ [nm])).
Defined.

Definition tag {A B} (p : t A B) := Eval vm_compute in (tag_def p).

Definition env := ext_environment.

Definition sem {A B} (p : t A B) (a : A) (e : env) : option B :=
let cast {C : Ty} (x : option C) : tySem (Unit + C) :=
  match x with Some c => inr c | None => inl tt end in
(match p in prim A B return A -> option B with
 | CurrentIndex => fun _ => Some (fromZ (Z.of_nat (Bitcoin.envIx (extBase e))))
 | InputScriptHash => fun i =>
     Some (cast (option_map (fun h => from_hash256 h) (nth_error (extInScriptHash e) (Z.to_nat (toZ i)))))
 | InputAnnexHash => fun i =>
     Some (match nth_error (extInAnnexHash e) (Z.to_nat (toZ i)) with
           | None => inl tt
           | Some None => inr (inl tt)
           | Some (Some h) => inr (inr (from_hash256 h))
           end)
 | InputScriptSigHash => fun i =>
     Some (cast (option_map (fun h => from_hash256 h) (nth_error (extInScriptSigHash e) (Z.to_nat (toZ i)))))
 | TapleafVersion => fun _ => Some (fromZ (extTapleafVersion e))
 | Tappath => fun i =>
     Some (cast (option_map (fun h => from_hash256 h) (nth_error (extTappath e) (Z.to_nat (toZ i)))))
 | InternalKey => fun _ => Some (from_hash256 (extInternalKey e))
 | TransactionId => fun _ => Some (from_hash256 (extTxid e))
 end) a.

End BitcoinExt.

Module PrimitiveBitcoinExt := PrimitiveModule BitcoinExt.
