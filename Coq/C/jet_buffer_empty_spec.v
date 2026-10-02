(** Literal Haskell Programs.Word.bufferEmpty (SingleB / DoubleB) port.
    Buffer depth 5 is Buffer63. This representation bridge is infrastructure
    for real C buffer writers, not a completed jet implementation proof. *)
From Coq Require Import List Lia PeanoNat.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Translate.
Import ListNotations.
Module AC := Alg.Core.Combinators.
Set Default Timeout 10.

Fixpoint buffer_type (X : Ty.Ty) (depth : nat) : Ty.Ty :=
  match depth with
  | Datatypes.O => Ty.Sum Ty.Unit X
  | Datatypes.S d => Ty.Prod (Ty.Sum Ty.Unit (Vector X (Datatypes.S d))) (buffer_type X d)
  end.
Fixpoint buffer_empty_spec (X : Ty.Ty) (depth : nat) (A : Ty.Ty) {term : Alg.Core.Algebra} :
    term A (buffer_type X depth) :=
  match depth with
  | Datatypes.O => AC.injl AC.unit
  | Datatypes.S d => AC.pair (AC.injl AC.unit) (buffer_empty_spec X d A)
  end.
Fixpoint buffer_empty_value (X : Ty.Ty) (depth : nat) : Ty.tySem (buffer_type X depth) :=
  match depth with
  | Datatypes.O => inl tt
  | Datatypes.S d => (inl tt, buffer_empty_value X d)
  end.
Fixpoint buffer_empty_cells (X : Ty.Ty) (depth : nat) : list BitMachine.Cell :=
  match depth with
  | Datatypes.O => Some Datatypes.false :: repeat None (Translate.bitSize X)
  | Datatypes.S d => (Some Datatypes.false :: repeat None (Translate.bitSize (Vector X (Datatypes.S d)))) ++
      buffer_empty_cells X d
  end.

Lemma buffer_empty_spec_parametric X depth A : Alg.Core.Parametric (@buffer_empty_spec X depth A).
Proof.
  intros alg1 alg2 R. induction depth; cbn [buffer_empty_spec].
  - apply Alg.injl_Parametric, Alg.unit_Parametric.
  - apply Alg.pair_Parametric; [apply Alg.injl_Parametric, Alg.unit_Parametric|exact IHdepth].
Qed.
Lemma buffer_empty_spec_value X depth A (a : Ty.tySem A) :
  @buffer_empty_spec X depth A Alg.CoreFunSem a = buffer_empty_value X depth.
Proof.
  induction depth; [reflexivity|].
  change (((inl tt : Ty.tySem (Ty.Sum Ty.Unit (Vector X (S depth)))),
    @buffer_empty_spec X depth A Alg.CoreFunSem a) = (inl tt, buffer_empty_value X depth)).
  now rewrite IHdepth.
Qed.

Lemma encode_empty_sum X : @encode (Ty.Sum Ty.Unit X) (inl tt) =
  Some Datatypes.false :: repeat None (Translate.bitSize X).
Proof.
  change (Some Datatypes.false :: (repeat None (Translate.bitSize X - 0) ++ []) =
    Some Datatypes.false :: repeat None (Translate.bitSize X)).
  rewrite Nat.sub_0_r, app_nil_r; reflexivity.
Qed.
Lemma buffer_empty_value_cells X depth :
  encode (buffer_empty_value X depth) = buffer_empty_cells X depth.
Proof.
  induction depth; [apply encode_empty_sum|].
  change (@encode (Ty.Sum Ty.Unit (Vector X (S depth))) (inl tt) ++
    encode (buffer_empty_value X depth) = buffer_empty_cells X (S depth)).
  rewrite encode_empty_sum, IHdepth; reflexivity.
Qed.
Lemma buffer_empty_spec_cells X depth A (a : Ty.tySem A) :
  encode (@buffer_empty_spec X depth A Alg.CoreFunSem a) = buffer_empty_cells X depth.
Proof. rewrite buffer_empty_spec_value; apply buffer_empty_value_cells. Qed.

Lemma buffer63_byte_cells_length : length (buffer_empty_cells (Word 3) 5) = 510%nat.
Proof. vm_compute; reflexivity. Qed.
