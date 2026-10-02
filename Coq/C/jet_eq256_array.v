(** Representation and actual array-load expressions for eq_256.
    The comparison loop and enclosing call must still be proved separately. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout.
Require Import C.jet_read32s_layout C.jet_word32_chunks C.jet_equality_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint eq256_words_equal (xs ys : list int) : bool :=
  match xs, ys with
  | [], [] => Datatypes.true
  | x :: xs, y :: ys => andb (Int.eq x y) (eq256_words_equal xs ys)
  | _, _ => Datatypes.false
  end.
Lemma eq256_words_equal_true xs ys :
  eq256_words_equal xs ys = Datatypes.true <-> xs = ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; cbn [eq256_words_equal].
  - split; reflexivity.
  - split; discriminate.
  - split; discriminate.
  - rewrite Bool.andb_true_iff, IH.
    pose proof (Int.eq_spec x y) as HE. destruct (Int.eq x y) eqn:E.
    + subst y. split; [intros [_ ->]; reflexivity|intros H; injection H; auto].
    + split; [intros [H _]; discriminate|intros H; injection H; contradiction].
Qed.
Lemma eq256_array_map_injective xs ys :
  map word32_array_value xs = map word32_array_value ys -> xs = ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] H; try discriminate; [reflexivity|].
  assert (HE : word32_array_value x = word32_array_value y).
  { exact (f_equal (fun zs => hd Int.zero zs) H). }
  assert (HT : map word32_array_value xs = map word32_array_value ys).
  { exact (f_equal (@tl int) H). }
  apply word32_array_value_injective in HE. subst y. f_equal. apply IH; exact HT.
Qed.
Definition eq256_array_result (x y : Ty.tySem (Word 8)) :=
  eq256_words_equal (map word32_array_value (word32_chunks 3 x))
    (map word32_array_value (word32_chunks 3 y)).
Lemma eq256_array_denotes x y :
  eq256_array_result x y = Bit.toBool (@equality_spec (Word 8) Alg.CoreFunSem (x, y)).
Proof.
  apply Bool.eq_true_iff_eq. unfold eq256_array_result.
  rewrite eq256_words_equal_true, equality_spec_true.
  split.
  - intros H. apply (word32_chunks_injective 3). apply eq256_array_map_injective; exact H.
  - intros ->; reflexivity.
Qed.

Definition eq256_env bl ba := PTree.set _arr (ba, tarray tuint 16) (e_one8 bl).
Lemma eval_eq256_array_load bl ba le m index index_expr x :
  0 <= index <= 15 ->
  typeof index_expr = tint ->
  eval_expr ge0 (eq256_env bl ba) le m index_expr (Vint (Int.repr index)) ->
  Mem.load Mint32 m ba (4 * index) = Some (Vint x) ->
  eval_expr ge0 (eq256_env bl ba) le m
    (Ederef (Ebinop Oadd (Evar _arr (tarray tuint 16)) index_expr (tptr tuint)) tuint) (Vint x).
Proof.
  intros HI HT HE HL.
  assert (HS : Int.signed (Int.repr index) = index).
  { apply Int.signed_repr. change (-2147483648 <= index <= 2147483647); lia. }
  assert (HM : 0 <= 4 * index <= Ptrofs.max_unsigned).
  { change (0 <= 4 * index <= 18446744073709551615); lia. }
  assert (HA : Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr index))) =
    Ptrofs.repr (4 * index)).
  { unfold Ptrofs.of_ints. rewrite HS. unfold Ptrofs.add, Ptrofs.mul.
    change (Ptrofs.unsigned Ptrofs.zero) with 0.
    change (Ptrofs.unsigned (Ptrofs.repr 4)) with 4.
    rewrite (Ptrofs.unsigned_repr index) by (change (0 <= index <= 18446744073709551615); lia).
    rewrite (Ptrofs.unsigned_repr (4 * index)) by exact HM. reflexivity. }
  eapply eval_Elvalue with (loc := ba) (ofs := Ptrofs.repr (4 * index)).
  - eapply eval_Ederef. eapply eval_Ebinop with (v1 := Vptr ba Ptrofs.zero)
      (v2 := Vint (Int.repr index)).
    + eapply eval_Elvalue; [eapply eval_Evar_local; reflexivity|].
      apply deref_loc_reference; reflexivity.
    + exact HE.
    + rewrite HT. change (Some (Vptr ba (Ptrofs.add Ptrofs.zero
        (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr index))))) =
        Some (Vptr ba (Ptrofs.repr (4 * index)))). rewrite HA; reflexivity.
  - apply deref_loc_value with (chunk := Mint32); [reflexivity|].
    unfold Mem.loadv. rewrite Ptrofs.unsigned_repr by exact HM. exact HL.
Qed.
