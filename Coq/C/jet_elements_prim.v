(** Elements primitives: a Coq port of the canonical Haskell definitions.

    The Coq library has no Elements primitive module.  This file ports, as
    literally as the two languages allow,
    [Haskell/Elements/Simplicity/Elements/DataTypes.hs] (data types, the
    no-witness transaction serialization behind [txid], and the null-data
    script parser) and [Haskell/Elements/Simplicity/Elements/Primitive.hs]
    (the [Prim] signature, [primName] and [primSem]).  It follows the shape of
    the accepted [Simplicity.Primitive.Bitcoin].

    STATUS: a port awaiting source review against the Haskell files; it is
    not an accepted canonical module.  Deliberate representation choices:

    - 256-bit values that Haskell keeps as [Hash256], [Word256], a secp256k1
      field element ([FE], via [fe_repr]/[fe_pack]) or an x-only public key
      are all carried as [hash256] (eight 32-bit registers, big-endian),
      the carrier this development already uses for [from_hash256].  A field
      element is therefore not constrained to be below the field prime: the
      Coq environments are a superset of the Haskell ones, never a subset.
    - Haskell's [Vector]/lazy [ByteString] become lists; the length bounds
      stated in comments of the Haskell records ("strictly less than 2^32")
      are record fields here, as in [Bitcoin.txOutput].
    - [sigTx] carries [sigTxInBounds] and [sigTxOutBounds], the count bounds
      of the accepted [Bitcoin.sigTx] (inputs non-empty, both below 2^32):
      the C interface passes counts as 32-bit words and the Simplicity
      loops and searches over inputs and outputs range over Word32.
    - [envIx] (a [Word32] in Haskell) is a [nat] with its 32-bit range and
      the bound that [primEnv] checks. *)
From Coq Require Import ZArith String List.
From compcert Require Import Integers.
Require Import Simplicity.Util.List.
Require Import Simplicity.Digest Simplicity.MerkleRoot Simplicity.Primitive Simplicity.Ty.
Require Import Simplicity.Word.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

(** * Data types ([DataTypes.hs]) *)

Definition script := list byte.

(** [data Point = Point Bool FE] (parity of y, x coordinate). *)
Record point : Set := Point { pointOdd : bool; pointX : hash256 }.

(** [data Confidential prf a = Explicit a | Confidential Point prf]. *)
Inductive confidential (prf A : Set) : Set :=
| Explicit (a : A)
| Confidential (pt : point) (p : prf).
Arguments Explicit {prf A} a.
Arguments Confidential {prf A} pt p.

(** [prf_] set to [()]: [clearAssetPrf], [clearAmountPrf]. *)
Definition clearPrf {prf A : Set} (c : confidential prf A) : confidential unit A :=
  match c with
  | Explicit a => Explicit a
  | Confidential pt _ => Confidential pt tt
  end.

(** [view prf_]: the proof bytes, or the empty string for an explicit value. *)
Definition viewPrf {A : Set} (c : confidential (list byte) A) : list byte :=
  match c with
  | Explicit _ => []
  | Confidential _ p => p
  end.

(** [AssetWith prf], [AmountWith prf] (newtypes over [Confidential]). *)
Definition assetWith (prf : Set) : Set := confidential prf hash256.
Definition amountWith (prf : Set) : Set := confidential prf int64.

(** [newtype Nonce = Nonce { nonce :: Either (Bool, Word256) Hash256 }]. *)
Definition nonce : Set := (bool * hash256) + hash256.

Record newIssuance : Set :=
 { newIssuanceContractHash : hash256
 ; newIssuanceAmount : amountWith (list byte)
 ; newIssuanceTokenAmount : amountWith (list byte)
 }.

Record reissuance : Set :=
 { reissuanceBlindingNonce : hash256
 ; reissuanceEntropy : hash256
 ; reissuanceAmount : amountWith (list byte)
 }.

(** [type Issuance = Either NewIssuance Reissuance]. *)
Definition issuance : Set := newIssuance + reissuance.

Record outpoint : Set :=
 { opHash : hash256
 ; opIndex : int
 }.

Record utxo : Set :=
 { utxoAsset : assetWith unit
 ; utxoAmount : amountWith unit
 ; utxoScript : script
 ; utxoScript_bound : Zlength utxoScript < Int.modulus
 }.

Record sigTxInput : Set :=
 { sigTxiPegin : option hash256
 ; sigTxiPreviousOutpoint : outpoint
 ; sigTxiTxo : utxo
 ; sigTxiSequence : int
 ; sigTxiIssuance : option issuance
 ; sigTxiAnnex : option (list byte)
 ; sigTxiScriptSig : script
 ; sigTxiScriptSig_bound : Zlength sigTxiScriptSig < Int.modulus
 }.

Record txOutput : Set :=
 { txoAsset : assetWith (list byte)
 ; txoAmount : amountWith (list byte)
 ; txoNonce : option nonce
 ; txoScript : script
 ; txoScript_bound : Zlength txoScript < Int.modulus
 }.

Record sigTx : Set :=
 { sigTxVersion : int
 ; sigTxIn : list sigTxInput
 ; sigTxOut : list txOutput
 ; sigTxLock : int
 ; sigTxInBounds : (0 < Zlength sigTxIn < Int.modulus)%Z
 ; sigTxOutBounds : (0 <= Zlength sigTxOut < Int.modulus)%Z
 }.

Record tapEnv : Set :=
 { tapleafVersion : byte
 ; tapInternalKey : hash256
 ; tappath : list hash256
 ; tapScriptCMR : hash256
 }.

(** ** Null data ([TxNullDatumF], [getTxNullDatum], [txNullData]) *)

Inductive txNullDatumF (A : Set) : Set :=
| Immediate (a : A) | PushData (a : A) | PushData2 (a : A) | PushData4 (a : A)
| OP1Negate | OPReserved
| OP1 | OP2 | OP3 | OP4 | OP5 | OP6 | OP7 | OP8
| OP9 | OP10 | OP11 | OP12 | OP13 | OP14 | OP15 | OP16.
Arguments Immediate {A} a.
Arguments PushData {A} a.
Arguments PushData2 {A} a.
Arguments PushData4 {A} a.
Arguments OP1Negate {A}.
Arguments OPReserved {A}.
Arguments OP1 {A}. Arguments OP2 {A}. Arguments OP3 {A}. Arguments OP4 {A}.
Arguments OP5 {A}. Arguments OP6 {A}. Arguments OP7 {A}. Arguments OP8 {A}.
Arguments OP9 {A}. Arguments OP10 {A}. Arguments OP11 {A}. Arguments OP12 {A}.
Arguments OP13 {A}. Arguments OP14 {A}. Arguments OP15 {A}. Arguments OP16 {A}.

(** [fmap] of [TxNullDatumF]. *)
Definition mapNullDatum {A B : Set} (f : A -> B) (d : txNullDatumF A) : txNullDatumF B :=
  match d with
  | Immediate a => Immediate (f a) | PushData a => PushData (f a)
  | PushData2 a => PushData2 (f a) | PushData4 a => PushData4 (f a)
  | OP1Negate => OP1Negate | OPReserved => OPReserved
  | OP1 => OP1 | OP2 => OP2 | OP3 => OP3 | OP4 => OP4
  | OP5 => OP5 | OP6 => OP6 | OP7 => OP7 | OP8 => OP8
  | OP9 => OP9 | OP10 => OP10 | OP11 => OP11 | OP12 => OP12
  | OP13 => OP13 | OP14 => OP14 | OP15 => OP15 | OP16 => OP16
  end.

(** [getLazyByteString n]: exactly [n] bytes or failure. *)
Definition getBytes (n : Z) (bs : list byte) : option (list byte * list byte) :=
  if Z.leb n (Zlength bs)
  then Some (firstn (Z.to_nat n) bs, skipn (Z.to_nat n) bs)
  else None.

(** Little-endian value of a byte list ([getWord16le], [getWord32le]). *)
Fixpoint leValue (bs : list byte) : Z :=
  match bs with
  | [] => 0
  | b :: rest => Byte.unsigned b + 256 * leValue rest
  end.

Definition getPush (width : Z) (bs : list byte) : option (list byte * list byte) :=
  match getBytes width bs with
  | Some (len, rest) => getBytes (leValue len) rest
  | None => None
  end.

(** [getTxNullDatum]: one push-data opcode and the remaining input. *)
Definition getTxNullDatum (bs : list byte) : option (txNullDatumF (list byte) * list byte) :=
  match bs with
  | [] => None
  | op :: rest =>
      let o := Byte.unsigned op in
      if Z.eqb o 96 then Some (OP16, rest) else
      if Z.eqb o 95 then Some (OP15, rest) else
      if Z.eqb o 94 then Some (OP14, rest) else
      if Z.eqb o 93 then Some (OP13, rest) else
      if Z.eqb o 92 then Some (OP12, rest) else
      if Z.eqb o 91 then Some (OP11, rest) else
      if Z.eqb o 90 then Some (OP10, rest) else
      if Z.eqb o 89 then Some (OP9, rest) else
      if Z.eqb o 88 then Some (OP8, rest) else
      if Z.eqb o 87 then Some (OP7, rest) else
      if Z.eqb o 86 then Some (OP6, rest) else
      if Z.eqb o 85 then Some (OP5, rest) else
      if Z.eqb o 84 then Some (OP4, rest) else
      if Z.eqb o 83 then Some (OP3, rest) else
      if Z.eqb o 82 then Some (OP2, rest) else
      if Z.eqb o 81 then Some (OP1, rest) else
      if Z.eqb o 80 then Some (OPReserved, rest) else
      if Z.eqb o 79 then Some (OP1Negate, rest) else
      if Z.eqb o 78 then option_map (fun p => (PushData4 (fst p), snd p)) (getPush 4 rest) else
      if Z.eqb o 77 then option_map (fun p => (PushData2 (fst p), snd p)) (getPush 2 rest) else
      if Z.eqb o 76 then option_map (fun p => (PushData (fst p), snd p)) (getPush 1 rest) else
      if Z.ltb o 76 then option_map (fun p => (Immediate (fst p), snd p)) (getBytes o rest)
      else None
  end.

(** The [go] loop of [txNullData]; every datum consumes at least one byte,
    so the input length bounds the number of iterations. *)
Fixpoint getTxNullData (fuel : nat) (bs : list byte) : option (list (txNullDatumF (list byte))) :=
  match bs with
  | [] => Some []
  | _ :: _ =>
      match fuel with
      | O => None
      | S fuel' =>
          match getTxNullDatum bs with
          | Some (d, rest) => option_map (cons d) (getTxNullData fuel' rest)
          | None => None
          end
      end
  end.

(** [txNullData]: the script must start with [0x6a] (OP_RETURN). *)
Definition txNullData (s : script) : option (list (txNullDatumF (list byte))) :=
  match s with
  | op :: rest => if Z.eqb (Byte.unsigned op) 106 then getTxNullData (length rest) rest else None
  | [] => None
  end.

(** ** Serialization ([putNoWitnessTx], [txid]) *)

Definition putHash256 (x : hash256) : list byte := hash256_to_bytelist x.

Definition putLE (n : nat) (z : Z) : list byte :=
  map (fun i => Byte.repr (z / two_power_nat (i * Byte.wordsize))) (seq 0 n).

Definition putBE (n : nat) (z : Z) : list byte := rev (putLE n z).

Definition putWord8 (z : Z) : list byte := [Byte.repr z].

(** [putVarInt] of [putNoWitnessTx]. *)
Definition putVarInt (x : Z) : list byte :=
  if Z.leb x 252 then putWord8 x else
  if Z.leb x 65535 then putWord8 253 ++ putLE 2 x else
  if Z.leb x 4294967295 then putWord8 254 ++ putLE 4 x else
  putWord8 255 ++ putLE 8 x.

(** [putFE = put . fe_pack]: 32 big-endian bytes. *)
Definition putFE (x : hash256) : list byte := putHash256 x.

Definition putAsset (a : assetWith unit) : list byte :=
  match a with
  | Explicit h => putWord8 1 ++ putHash256 h
  | Confidential (Point odd x) _ => putWord8 (if odd then 11 else 10) ++ putFE x
  end.

Definition putAmount (a : amountWith unit) : list byte :=
  match a with
  | Explicit v => putWord8 1 ++ putBE 8 (Int64.unsigned v)
  | Confidential (Point odd x) _ => putWord8 (if odd then 9 else 8) ++ putFE x
  end.

(** [putNonce = putMaybeConfidential put]. *)
Definition putNonce (n : option nonce) : list byte :=
  match n with
  | None => putWord8 0
  | Some (inr h) => putWord8 1 ++ putHash256 h
  | Some (inl (odd, x)) => putWord8 (if odd then 3 else 2) ++ putHash256 x
  end.

(** [putIssuanceAmount] of [putNoWitnessTx]: an explicit zero is one zero byte. *)
Definition putIssuanceAmount (a : amountWith unit) : list byte :=
  match a with
  | Explicit v => if Int64.eq v Int64.zero then putWord8 0 else putAmount a
  | Confidential _ _ => putAmount a
  end.

Definition zeroHash256Bytes : list byte := repeat Byte.zero 32.

Definition putTxIssuance (i : option issuance) : list byte :=
  match i with
  | None => []
  | Some (inl new) =>
      zeroHash256Bytes ++ putHash256 (newIssuanceContractHash new) ++
      putIssuanceAmount (clearPrf (newIssuanceAmount new)) ++
      putIssuanceAmount (clearPrf (newIssuanceTokenAmount new))
  | Some (inr re) =>
      putHash256 (reissuanceBlindingNonce re) ++ putHash256 (reissuanceEntropy re) ++
      putIssuanceAmount (clearPrf (reissuanceAmount re)) ++ putWord8 0
  end.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.

Definition putTxInput (txi : sigTxInput) : list byte :=
  let issuanceFlag := if isSome (sigTxiIssuance txi) then 2147483648 else 0 in
  let peginFlag := if isSome (sigTxiPegin txi) then 1073741824 else 0 in
  let flags := Z.lor issuanceFlag peginFlag in
  putHash256 (opHash (sigTxiPreviousOutpoint txi)) ++
  putLE 4 (Z.lor flags (Int.unsigned (opIndex (sigTxiPreviousOutpoint txi)))) ++
  putVarInt (Zlength (sigTxiScriptSig txi)) ++ sigTxiScriptSig txi ++
  putLE 4 (Int.unsigned (sigTxiSequence txi)) ++
  putTxIssuance (sigTxiIssuance txi).

Definition putTxOutput (txo : txOutput) : list byte :=
  putAsset (clearPrf (txoAsset txo)) ++ putAmount (clearPrf (txoAmount txo)) ++
  putNonce (txoNonce txo) ++ putVarInt (Zlength (txoScript txo)) ++ txoScript txo.

Definition putNoWitnessTx (tx : sigTx) : list byte :=
  putLE 4 (Int.unsigned (sigTxVersion tx)) ++ putWord8 0 ++
  putVarInt (Zlength (sigTxIn tx)) ++ concat (map putTxInput (sigTxIn tx)) ++
  putVarInt (Zlength (sigTxOut tx)) ++ concat (map putTxOutput (sigTxOut tx)) ++
  putLE 4 (Int.unsigned (sigTxLock tx)).

(** [bslDoubleHash]. *)
Definition byteStringDoubleHash (x : list byte) : hash256 :=
  byteStringHash (hash256_to_bytelist (byteStringHash x)).

Definition txid (tx : sigTx) : hash256 := byteStringDoubleHash (putNoWitnessTx tx).

(** * Primitives ([Primitive.hs]) *)

(** [Bit] as in [Simplicity.Bit] (not imported: it rebinds [true]/[false]). *)
Local Notation Bit := (Sum Unit Unit).
Local Notation Word2 := (Word 1).
Local Notation Word4 := (Word 2).
(** [type S a = Either () a], [type Conf a = Either (Bit, Word256) a],
    [type PubKey = Word256].  Local: [S] must not shadow the successor of
    [nat] in importing modules. *)
Local Notation S a := (Sum Unit a).
Local Notation Conf a := (Sum (Prod Bit Word256) a).

Module Elements <: PrimitiveSig.

Inductive prim : Ty -> Ty -> Set :=
| Version : prim Unit Word32
| LockTime : prim Unit Word32
| InputPegin : prim Word32 (S (S Word256))
| InputPrevOutpoint : prim Word32 (S (Prod Word256 Word32))
| InputAsset : prim Word32 (S (Conf Word256))
| InputAmount : prim Word32 (S (Conf Word64))
| InputScriptHash : prim Word32 (S Word256)
| InputSequence : prim Word32 (S Word32)
| InputAnnexHash : prim Word32 (S (S Word256))
| InputScriptSigHash : prim Word32 (S Word256)
| ReissuanceBlinding : prim Word32 (S (S Word256))
| NewIssuanceContract : prim Word32 (S (S Word256))
| ReissuanceEntropy : prim Word32 (S (S Word256))
| IssuanceAssetAmount : prim Word32 (S (S (Conf Word64)))
| IssuanceTokenAmount : prim Word32 (S (S (Conf Word64)))
| IssuanceAssetProof : prim Word32 (S Word256)
| IssuanceTokenProof : prim Word32 (S Word256)
| CurrentIndex : prim Unit Word32
| TapleafVersion : prim Unit Word8
| Tappath : prim Word8 (S Word256)
| InternalKey : prim Unit Word256
| OutputAsset : prim Word32 (S (Conf Word256))
| OutputAmount : prim Word32 (S (Conf Word64))
| OutputNonce : prim Word32 (S (S (Conf Word256)))
| OutputScriptHash : prim Word32 (S Word256)
| OutputNullDatum : prim (Prod Word32 Word32)
    (S (S (Sum (Prod Word2 Word256) (Sum Bit Word4))))
| OutputSurjectionProof : prim Word32 (S Word256)
| OutputRangeProof : prim Word32 (S Word256)
| GenesisBlockHash : prim Unit Word256
| ScriptCMR : prim Unit Word256
| TransactionId : prim Unit Word256.
Definition t := prim.

Definition primName : string := "Elements".

Definition name {a b} (p : t a b) : string :=
match p with
| Version => "version"
| LockTime => "lockTime"
| InputPegin => "inputPegin"
| InputPrevOutpoint => "inputPrevOutpoint"
| InputAsset => "inputAsset"
| InputAmount => "inputAmount"
| InputScriptHash => "inputScriptHash"
| InputSequence => "inputSequence"
| InputAnnexHash => "inputAnnexHash"
| InputScriptSigHash => "inputScriptSigHash"
| ReissuanceBlinding => "reissuanceBlinding"
| NewIssuanceContract => "newIssuanceContract"
| ReissuanceEntropy => "reissuanceEntropy"
| IssuanceAssetAmount => "issuanceAssetAmount"
| IssuanceTokenAmount => "issuanceTokenAmount"
| IssuanceAssetProof => "issuanceAssetProof"
| IssuanceTokenProof => "issuanceTokenProof"
| CurrentIndex => "currentIndex"
| TapleafVersion => "tapleafVersion"
| Tappath => "tappath"
| InternalKey => "internalKey"
| OutputAsset => "outputAsset"
| OutputAmount => "outputAmount"
| OutputNonce => "outputNonce"
| OutputScriptHash => "outputScriptHash"
| OutputNullDatum => "outputNullDatum"
| OutputSurjectionProof => "outputSurjectionProof"
| OutputRangeProof => "outputRangeProof"
| GenesisBlockHash => "genesisBlockHash"
| ScriptCMR => "scriptCMR"
| TransactionId => "transactionId"
end.

Section Tag.

Let tag_def {A B} (p : t A B) : hash256.
pose (nm := name p).
revert p nm; intros [] nm;
exact (MerkleRoot.tag (primitivePrefix primName ++ [nm])).
Defined.

Definition tag {A B} (p : t A B) := Eval vm_compute in (tag_def p).

End Tag.

(** [data PrimEnv]: [envIx :: Word32], hence its range; [envIxBounded] is the
    condition checked by [primEnv]. *)
Record environment : Set :=
{ envTx : sigTx
; envIx : nat
; envTap : tapEnv
; envGenesisBlock : hash256
; envIxBounded : (envIx < length (sigTxIn envTx))%nat
; envIxWord32 : (Z.of_nat envIx < 4294967296)%Z
}.
Definition env := environment.

Section primSem.

Let cast {A : Ty} (x : option A) : tySem (S A) :=
match x with
| Some a => inr a
| None => inl tt
end.

Let toBit (b : bool) : tySem Bit := if b then inr tt else inl tt.

Let encodeHash (h : hash256) : tySem Word256 := from_hash256 h.

Let encodeConfidential {A : Set} {B : Ty} (enc : A -> tySem B) (c : confidential unit A) :
    tySem (Conf B) :=
match c with
| Explicit a => inr (enc a)
| Confidential (Point odd x) _ => inl (toBit odd, from_hash256 x)
end.

Let encodeAsset (a : assetWith unit) : tySem (Conf Word256) := encodeConfidential encodeHash a.

Let encodeAmount (a : amountWith unit) : tySem (Conf Word64) :=
  encodeConfidential (fun v => fromZ (Int64.unsigned v) : tySem Word64) a.

Let encodeNonce (n : option nonce) : tySem (S (Conf Word256)) :=
  cast (option_map (fun x : nonce =>
    match x return tySem (Conf Word256) with
    | inl (odd, w) => inl (toBit odd, from_hash256 w)
    | inr h => inr (encodeHash h)
    end) n).

Let encodeOutpoint (op : outpoint) : tySem (Prod Word256 Word32) :=
 (encodeHash (opHash op), fromZ (Int.unsigned (opIndex op)) : tySem Word32).

Let encodeNullDatum (d : txNullDatumF hash256) :
    tySem (Sum (Prod Word2 Word256) (Sum Bit Word4)) :=
match d with
| Immediate h => inl (fromZ 0 : tySem Word2, encodeHash h)
| PushData h => inl (fromZ 1 : tySem Word2, encodeHash h)
| PushData2 h => inl (fromZ 2 : tySem Word2, encodeHash h)
| PushData4 h => inl (fromZ 3 : tySem Word2, encodeHash h)
| OP1Negate => inr (inl (toBit false))
| OPReserved => inr (inl (toBit true))
| OP1 => inr (inr (fromZ 0 : tySem Word4))
| OP2 => inr (inr (fromZ 1 : tySem Word4))
| OP3 => inr (inr (fromZ 2 : tySem Word4))
| OP4 => inr (inr (fromZ 3 : tySem Word4))
| OP5 => inr (inr (fromZ 4 : tySem Word4))
| OP6 => inr (inr (fromZ 5 : tySem Word4))
| OP7 => inr (inr (fromZ 6 : tySem Word4))
| OP8 => inr (inr (fromZ 7 : tySem Word4))
| OP9 => inr (inr (fromZ 8 : tySem Word4))
| OP10 => inr (inr (fromZ 9 : tySem Word4))
| OP11 => inr (inr (fromZ 10 : tySem Word4))
| OP12 => inr (inr (fromZ 11 : tySem Word4))
| OP13 => inr (inr (fromZ 12 : tySem Word4))
| OP14 => inr (inr (fromZ 13 : tySem Word4))
| OP15 => inr (inr (fromZ 14 : tySem Word4))
| OP16 => inr (inr (fromZ 15 : tySem Word4))
end.

(** [issuanceAmount = either newIssuanceAmount reissuanceAmount]. *)
Let issuanceAmount (i : issuance) : amountWith (list byte) :=
match i with
| inl new => newIssuanceAmount new
| inr re => reissuanceAmount re
end.

(** [issuanceTokenAmount = either newIssuanceTokenAmount (const (Amount (Explicit 0)))]. *)
Let issuanceTokenAmount (i : issuance) : amountWith (list byte) :=
match i with
| inl new => newIssuanceTokenAmount new
| inr _ => Explicit Int64.zero
end.

(** [view (to sigTxiIssuance . just_ . to f . under amount . prf_)]: the proof
    bytes when there is an issuance with a confidential amount, else empty. *)
Let issuanceProof (f : issuance -> amountWith (list byte)) (txi : sigTxInput) : list byte :=
match sigTxiIssuance txi with
| Some i => viewPrf (f i)
| None => []
end.

Definition sem {A B} (p : t A B) (a : A) (e : env) : option B :=
let tx := envTx e in
let ix := envIx e in
let atInput {A : Ty} (f : sigTxInput -> A) (i : Word32) : option (tySem (S A)) :=
  Some (cast (option_map f (nth_error (sigTxIn tx) (Z.to_nat (toZ i))))) in
let atOutput {A : Ty} (f : txOutput -> A) (i : Word32) : option (tySem (S A)) :=
  Some (cast (option_map f (nth_error (sigTxOut tx) (Z.to_nat (toZ i))))) in
(match p in prim A B return A -> option B with
 | Version => fun _ => Some (fromZ (Int.unsigned (sigTxVersion tx)))
 | LockTime => fun _ => Some (fromZ (Int.unsigned (sigTxLock tx)))
 | InputPegin => atInput (fun txi => cast (option_map encodeHash (sigTxiPegin txi)))
 | InputPrevOutpoint => atInput (fun txi => encodeOutpoint (sigTxiPreviousOutpoint txi))
 | InputAsset => atInput (fun txi => encodeAsset (utxoAsset (sigTxiTxo txi)))
 | InputAmount => atInput (fun txi => encodeAmount (utxoAmount (sigTxiTxo txi)))
 | InputScriptHash => atInput (fun txi => encodeHash (byteStringHash (utxoScript (sigTxiTxo txi))))
 | InputSequence => atInput (fun txi => fromZ (Int.unsigned (sigTxiSequence txi)))
 | InputAnnexHash => atInput (fun txi =>
     cast (option_map (fun x => encodeHash (byteStringHash x)) (sigTxiAnnex txi)))
 | InputScriptSigHash => atInput (fun txi => encodeHash (byteStringHash (sigTxiScriptSig txi)))
 | ReissuanceBlinding => atInput (fun txi =>
     cast (option_map encodeHash
       (match sigTxiIssuance txi with
        | Some (inr re) => Some (reissuanceBlindingNonce re)
        | _ => None
        end)))
 | NewIssuanceContract => atInput (fun txi =>
     cast (option_map encodeHash
       (match sigTxiIssuance txi with
        | Some (inl new) => Some (newIssuanceContractHash new)
        | _ => None
        end)))
 | ReissuanceEntropy => atInput (fun txi =>
     cast (option_map encodeHash
       (match sigTxiIssuance txi with
        | Some (inr re) => Some (reissuanceEntropy re)
        | _ => None
        end)))
 | IssuanceAssetAmount => atInput (fun txi =>
     cast (option_map (fun i => encodeAmount (clearPrf (issuanceAmount i))) (sigTxiIssuance txi)))
 | IssuanceTokenAmount => atInput (fun txi =>
     cast (option_map (fun i => encodeAmount (clearPrf (issuanceTokenAmount i))) (sigTxiIssuance txi)))
 | IssuanceAssetProof => atInput (fun txi =>
     encodeHash (byteStringHash (issuanceProof issuanceAmount txi)))
 | IssuanceTokenProof => atInput (fun txi =>
     encodeHash (byteStringHash (issuanceProof issuanceTokenAmount txi)))
 | CurrentIndex => fun _ => Some (fromZ (Z.of_nat ix))
 | TapleafVersion => fun _ => Some (fromZ (Byte.unsigned (tapleafVersion (envTap e))))
 | Tappath => fun i : Word8 =>
     Some (cast (option_map encodeHash (nth_error (tappath (envTap e)) (Z.to_nat (toZ i)))))
 | InternalKey => fun _ => Some (from_hash256 (tapInternalKey (envTap e)))
 | OutputAsset => atOutput (fun txo => encodeAsset (clearPrf (txoAsset txo)))
 | OutputAmount => atOutput (fun txo => encodeAmount (clearPrf (txoAmount txo)))
 | OutputNonce => atOutput (fun txo => encodeNonce (txoNonce txo))
 | OutputScriptHash => atOutput (fun txo => encodeHash (byteStringHash (txoScript txo)))
 | OutputNullDatum => fun ij =>
     let i : Word32 := fst ij in
     let j : Word32 := snd ij in
     Some (cast
       (match nth_error (sigTxOut tx) (Z.to_nat (toZ i)) with
        | Some txo =>
            match txNullData (txoScript txo) with
            | Some nullData =>
                Some (cast (option_map
                  (fun d => encodeNullDatum (mapNullDatum byteStringHash d))
                  (nth_error nullData (Z.to_nat (toZ j)))))
            | None => None
            end
        | None => None
        end))
 | OutputSurjectionProof => atOutput (fun txo => encodeHash (byteStringHash (viewPrf (txoAsset txo))))
 | OutputRangeProof => atOutput (fun txo => encodeHash (byteStringHash (viewPrf (txoAmount txo))))
 | GenesisBlockHash => fun _ => Some (encodeHash (envGenesisBlock e))
 | ScriptCMR => fun _ => Some (encodeHash (tapScriptCMR (envTap e)))
 | TransactionId => fun _ => Some (encodeHash (txid tx))
 end
) a.

End primSem.

End Elements.

Module Export PrimitiveElements := PrimitiveModule Elements.
