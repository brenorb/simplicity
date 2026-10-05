(** The union of the base Coq Bitcoin primitives and the extended ones of
    [jet_bitcoin_ext_prim], so that the SigHash programs, which mix both,
    can be stated over one signature; and the evaluation of the combinators
    in its option semantics. *)
From Coq Require Import ZArith String List.
From compcert Require Import Integers.
Require Import Simplicity.Digest Simplicity.MerkleRoot Simplicity.Primitive Simplicity.Ty Simplicity.Word.
Require Import Simplicity.Util.Option Simplicity.Util.Monad Simplicity.Util.Monad.Reader.
Require Simplicity.Alg.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_buffer_empty_spec C.jet_bitcoin_ext_prim C.jet_sha_ctx8_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Module BitcoinFull <: PrimitiveSig.

Inductive prim : Ty -> Ty -> Set :=
| Base : forall {A B}, Bitcoin.prim A B -> prim A B
| Ext : forall {A B}, BitcoinExt.prim A B -> prim A B.
Definition t := prim.

Definition tag {A B} (p : t A B) : hash256 :=
  match p with
  | Base q => Bitcoin.tag q
  | Ext q => BitcoinExt.tag q
  end.

Definition env := ext_environment.

Definition sem {A B} (p : t A B) (a : A) (e : env) : option B :=
  (match p in prim A B return A -> option B with
   | Base q => fun a => Bitcoin.sem q a (extBase e)
   | Ext q => fun a => BitcoinExt.sem q a e
   end) a.

End BitcoinFull.

Module PrimitiveBitcoinFull := PrimitiveModule BitcoinFull.

Notation fullalg := (PrimitiveBitcoinFull.Primitive.Theory.PrimitivePrimSem option_Monad_Zero).
Module PF := PrimitiveBitcoinFull.Primitive.
Notation fullassert := (PF.CanonicalStructures.toAssertion fullalg).
Notation fullcore := (Alg.Assertion.toCore (PF.CanonicalStructures.toAssertion fullalg)).

Lemma fx_comp {A B C : Ty} (s : @Alg.Core.domain fullcore A B) (t : @Alg.Core.domain fullcore B C) a e :
  @AC.comp A B C fullcore s t a e = match s a e with Some b => t b e | None => None end.
Proof. cbv. destruct (s a e); reflexivity. Qed.

Lemma fx_pair {A B C : Ty} (s : @Alg.Core.domain fullcore A B) (t : @Alg.Core.domain fullcore A C) a e :
  @AC.pair A B C fullcore s t a e =
    match s a e, t a e with Some b, Some c => Some (b, c) | _, _ => None end.
Proof. cbv. destruct (s a e), (t a e); reflexivity. Qed.

Lemma fx_prim {A B : Ty} (p : BitcoinFull.t A B) a e :
  @PF.Combinators.prim A B fullalg p a e = BitcoinFull.sem p a e.
Proof. cbv -[BitcoinFull.sem]. destruct (BitcoinFull.sem p a e); reflexivity. Qed.

Lemma fx_assert {A B : Ty} (t : forall alg : Alg.Assertion.Algebra, @Alg.Assertion.domain alg A B)
    (Ht : Alg.Assertion.Parametric t) (a : Ty.tySem A) e :
  t fullassert a e = t optalg a.
Proof.
  pose proof (@Alg.AssertionSem_initial (ReaderT_CIMonadZero BitcoinFull.env option_Monad_Zero) A B
    t Ht a) as Hs.
  refine (eq_trans (f_equal (fun f => f e) Hs) _).
  destruct (t optalg a); reflexivity.
Qed.

Lemma fx_core {A B : Ty} (t : forall alg : Alg.Core.Algebra, @Alg.Core.domain alg A B)
    (Ht : Alg.Core.Parametric t) (a : Ty.tySem A) e :
  t fullcore a e = Some (t Alg.CoreFunSem a).
Proof.
  pose proof (@Alg.CoreSem_initial (ReaderT_CIMonad BitcoinFull.env option_CIMonad) A B
    t Ht a) as Hs.
  refine (eq_trans (f_equal (fun f => f e) Hs) _). reflexivity.
Qed.
