(** The literal Programs.Word padding terms
      left_pad_low / left_pad_high / right_pad_low / right_pad_high
    ([Haskell/Core/Simplicity/Programs/Word.hs]) over vectors of words, and
    their serialized cells.  Parametricity of the terms is by structural
    recursion; the cell computation is over the functional semantics. *)
From Coq Require Import ZArith List Lia PeanoNat.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.BitMachine Simplicity.Translate.
Require Import C.jet_encoding.
Import ListNotations.
Module AC := Alg.Core.Combinators.
Set Default Timeout 30.

Definition rep_cells (c : list Cell) (n : nat) : list Cell := concat (repeat c n).

Lemma rep_cells_add c a b : rep_cells c (a + b) = rep_cells c a ++ rep_cells c b.
Proof. unfold rep_cells. rewrite repeat_app, concat_app. reflexivity. Qed.

Lemma rep_cells_single b n : rep_cells [Some b] n = repeat (Some b) n.
Proof. unfold rep_cells. induction n as [|n IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

(** left_pad_pad / right_pad_pad over [k] doubling levels. *)
Fixpoint left_pad_pad {term : Alg.Core.Algebra} {a} (t : @Alg.Core.domain term a a) (k : nat) :
    @Alg.Core.domain term a (Vector a k) :=
  match k with
  | O => AC.iden
  | S k => AC.pair (fill (n := k) t) (left_pad_pad t k)
  end.

Fixpoint right_pad_pad {term : Alg.Core.Algebra} {a} (t : @Alg.Core.domain term a a) (k : nat) :
    @Alg.Core.domain term a (Vector a k) :=
  match k with
  | O => AC.iden
  | S k => AC.pair (right_pad_pad t k) (fill (n := k) t)
  end.

Definition low_word {term : Alg.Core.Algebra} (w : nat) : @Alg.Core.domain term Ty.Unit (Word w) :=
  fill (n := w) (@Bit.false Ty.Unit term).
Definition high_word {term : Alg.Core.Algebra} (w : nat) : @Alg.Core.domain term Ty.Unit (Word w) :=
  fill (n := w) (@Bit.true Ty.Unit term).

Definition left_pad_low_spec {term : Alg.Core.Algebra} (w k : nat) :
    @Alg.Core.domain term (Word w) (Vector (Word w) k) :=
  left_pad_pad (AC.comp AC.unit (low_word w)) k.
Definition left_pad_high_spec {term : Alg.Core.Algebra} (w k : nat) :
    @Alg.Core.domain term (Word w) (Vector (Word w) k) :=
  left_pad_pad (AC.comp AC.unit (high_word w)) k.
Definition right_pad_low_spec {term : Alg.Core.Algebra} (w k : nat) :
    @Alg.Core.domain term (Word w) (Vector (Word w) k) :=
  right_pad_pad (AC.comp AC.unit (low_word w)) k.
Definition right_pad_high_spec {term : Alg.Core.Algebra} (w k : nat) :
    @Alg.Core.domain term (Word w) (Vector (Word w) k) :=
  right_pad_pad (AC.comp AC.unit (high_word w)) k.

Lemma encode_vector_pair X n (v : Ty.tySem (Vector X n)) :
  @encode (Vector X (S n)) (v, v) = encode v ++ encode v.
Proof. reflexivity. Qed.

Lemma encode_fill {C X} n (t : @Alg.Core.domain Alg.CoreFunSem C X) (c : Ty.tySem C) :
  encode (@fill C X n Alg.CoreFunSem t c) = rep_cells (encode (t c)) (2 ^ n).
Proof.
  induction n as [|n IH].
  - cbn [fill]. unfold rep_cells. cbn. rewrite app_nil_r. reflexivity.
  - assert (Hs : @fill C X (S n) Alg.CoreFunSem t c =
      (@fill C X n Alg.CoreFunSem t c, @fill C X n Alg.CoreFunSem t c)) by reflexivity.
    rewrite Hs, encode_vector_pair, IH, <- rep_cells_add.
    f_equal. rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma pow2_pos k : (1 <= 2 ^ k)%nat.
Proof. induction k as [|k IH]; [cbn; lia|]. rewrite Nat.pow_succ_r'. lia. Qed.

Lemma encode_left_pad_pad {a} k (t : @Alg.Core.domain Alg.CoreFunSem a a) (x : Ty.tySem a) :
  encode (@left_pad_pad Alg.CoreFunSem a t k x) = rep_cells (encode (t x)) (2 ^ k - 1) ++ encode x.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - assert (Hs : @left_pad_pad Alg.CoreFunSem a t (S k) x =
      (@fill a a k Alg.CoreFunSem t x, @left_pad_pad Alg.CoreFunSem a t k x)) by reflexivity.
    rewrite Hs.
    assert (Hp : @encode (Vector a (S k)) (@fill a a k Alg.CoreFunSem t x, @left_pad_pad Alg.CoreFunSem a t k x) =
      encode (@fill a a k Alg.CoreFunSem t x) ++ encode (@left_pad_pad Alg.CoreFunSem a t k x)) by reflexivity.
    rewrite Hp, encode_fill, IH, app_assoc, <- rep_cells_add.
    pose proof (pow2_pos k) as Hk.
    replace (2 ^ k + (2 ^ k - 1)) with (2 ^ S k - 1); [reflexivity|].
    rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma encode_right_pad_pad {a} k (t : @Alg.Core.domain Alg.CoreFunSem a a) (x : Ty.tySem a) :
  encode (@right_pad_pad Alg.CoreFunSem a t k x) = encode x ++ rep_cells (encode (t x)) (2 ^ k - 1).
Proof.
  induction k as [|k IH].
  - cbn. rewrite app_nil_r. reflexivity.
  - assert (Hs : @right_pad_pad Alg.CoreFunSem a t (S k) x =
      (@right_pad_pad Alg.CoreFunSem a t k x, @fill a a k Alg.CoreFunSem t x)) by reflexivity.
    rewrite Hs.
    assert (Hp : @encode (Vector a (S k)) (@right_pad_pad Alg.CoreFunSem a t k x, @fill a a k Alg.CoreFunSem t x) =
      encode (@right_pad_pad Alg.CoreFunSem a t k x) ++ encode (@fill a a k Alg.CoreFunSem t x)) by reflexivity.
    rewrite Hp, encode_fill, IH, <- app_assoc, <- rep_cells_add.
    pose proof (pow2_pos k) as Hk.
    replace (2 ^ k - 1 + 2 ^ k) with (2 ^ S k - 1); [reflexivity|].
    rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma encode_low_word w : encode (@low_word Alg.CoreFunSem w tt) = repeat (Some Datatypes.false) (2 ^ w).
Proof.
  unfold low_word.
  refine (eq_trans (@encode_fill Ty.Unit Bit w (@Bit.false Ty.Unit Alg.CoreFunSem) tt) _).
  rewrite <- rep_cells_single. reflexivity.
Qed.
Lemma encode_high_word w : encode (@high_word Alg.CoreFunSem w tt) = repeat (Some Datatypes.true) (2 ^ w).
Proof.
  unfold high_word.
  refine (eq_trans (@encode_fill Ty.Unit Bit w (@Bit.true Ty.Unit Alg.CoreFunSem) tt) _).
  rewrite <- rep_cells_single. reflexivity.
Qed.

Section Cells.
Variable w k : nat.
Variable x : Ty.tySem (Word w).
Lemma encode_left_pad_low : encode (@left_pad_low_spec Alg.CoreFunSem w k x) =
  rep_cells (repeat (Some Datatypes.false) (2 ^ w)) (2 ^ k - 1) ++ encode x.
Proof.
  unfold left_pad_low_spec. rewrite encode_left_pad_pad.
  change (@encode (Word w) ((AC.comp AC.unit (@low_word Alg.CoreFunSem w)) x)) with
    (encode (@low_word Alg.CoreFunSem w tt)).
  rewrite encode_low_word. reflexivity.
Qed.
Lemma encode_left_pad_high : encode (@left_pad_high_spec Alg.CoreFunSem w k x) =
  rep_cells (repeat (Some Datatypes.true) (2 ^ w)) (2 ^ k - 1) ++ encode x.
Proof.
  unfold left_pad_high_spec. rewrite encode_left_pad_pad.
  change (@encode (Word w) ((AC.comp AC.unit (@high_word Alg.CoreFunSem w)) x)) with
    (encode (@high_word Alg.CoreFunSem w tt)).
  rewrite encode_high_word. reflexivity.
Qed.
Lemma encode_right_pad_low : encode (@right_pad_low_spec Alg.CoreFunSem w k x) =
  encode x ++ rep_cells (repeat (Some Datatypes.false) (2 ^ w)) (2 ^ k - 1).
Proof.
  unfold right_pad_low_spec. rewrite encode_right_pad_pad.
  change (@encode (Word w) ((AC.comp AC.unit (@low_word Alg.CoreFunSem w)) x)) with
    (encode (@low_word Alg.CoreFunSem w tt)).
  rewrite encode_low_word. reflexivity.
Qed.
Lemma encode_right_pad_high : encode (@right_pad_high_spec Alg.CoreFunSem w k x) =
  encode x ++ rep_cells (repeat (Some Datatypes.true) (2 ^ w)) (2 ^ k - 1).
Proof.
  unfold right_pad_high_spec. rewrite encode_right_pad_pad.
  change (@encode (Word w) ((AC.comp AC.unit (@high_word Alg.CoreFunSem w)) x)) with
    (encode (@high_word Alg.CoreFunSem w tt)).
  rewrite encode_high_word. reflexivity.
Qed.
End Cells.
