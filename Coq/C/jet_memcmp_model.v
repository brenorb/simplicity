(** Explicit model of the libc [memcmp] called by the fee tally of the
    Elements environment ([sumFees], elements/env.c), by the fee lookup of
    the Elements jets ([lookup_fee], elements/elementsJets.c) and by the
    program drivers (exec.c).  The generated programs declare it as
    [EF_external "memcmp"], whose CompCert semantics is the abstract
    parameter [external_functions_sem].  The statement below is the C
    standard contract of [memcmp] on two readable ranges of initialized
    bytes: no memory effect, no event, and a result whose *sign* is the
    lexicographic comparison of the two ranges read as unsigned bytes.  It
    is meant as an explicit premise of every theorem that reaches such a
    call.  Nothing here proves that a linked libc implements this contract;
    [C.jet_memcmp_impl] proves it for a reference implementation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs.
Import ListNotations.
Local Open Scope Z_scope.

Definition memcmp_sig : signature :=
  mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil) AST.Tint cc_default.

(** The bytes [l] are readable at [o] of block [b]. *)
Definition bytes_at (m : mem) (b : block) (o : Z) (l : list int) : Prop :=
  forall i, (i < length l)%nat ->
    Mem.load Mint8unsigned m b (o + Z.of_nat i) = Some (Vint (nth i l Int.zero)).

(** Lexicographic comparison as unsigned bytes. *)
Fixpoint bytes_cmp (l1 l2 : list int) : Datatypes.comparison :=
  match l1, l2 with
  | x :: l1', y :: l2' =>
      match Z.compare (Int.unsigned x) (Int.unsigned y) with
      | Eq => bytes_cmp l1' l2'
      | c => c
      end
  | _, _ => Eq
  end.

(** The C standard fixes only the sign of the result. *)
Definition memcmp_sign (c : Datatypes.comparison) (r : int) : Prop :=
  match c with
  | Eq => r = Int.zero
  | Lt => Int.signed r < 0
  | Gt => 0 < Int.signed r
  end.

Definition memcmp_model : Prop :=
  forall (ge : Senv.t) m b1 o1 b2 o2 (l1 l2 : list int),
    length l1 = length l2 ->
    Z.of_nat (length l1) <= Int64.max_unsigned ->
    Ptrofs.unsigned o1 + Z.of_nat (length l1) <= Ptrofs.max_unsigned + 1 ->
    Ptrofs.unsigned o2 + Z.of_nat (length l1) <= Ptrofs.max_unsigned + 1 ->
    bytes_at m b1 (Ptrofs.unsigned o1) l1 -> bytes_at m b2 (Ptrofs.unsigned o2) l2 ->
    exists r,
      external_call (EF_external "memcmp" memcmp_sig) ge
        [Vptr b1 o1; Vptr b2 o2; Vlong (Int64.repr (Z.of_nat (length l1)))] m E0 (Vint r) m /\
      memcmp_sign (bytes_cmp l1 l2) r.

(** Facts about the comparison that callers use. *)
Lemma bytes_cmp_refl l : bytes_cmp l l = Eq.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [bytes_cmp]. rewrite Z.compare_refl. exact IH. Qed.

Lemma bytes_cmp_eq : forall l1 l2, length l1 = length l2 -> bytes_cmp l1 l2 = Eq -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] HL HC; try discriminate; [reflexivity|].
  cbn [bytes_cmp] in HC. destruct (Z.compare (Int.unsigned x) (Int.unsigned y)) eqn:E; try discriminate.
  apply Z.compare_eq in E.
  assert (x = y) by (rewrite <- (Int.repr_unsigned x), <- (Int.repr_unsigned y), E; reflexivity).
  subst y. f_equal. apply IH; [injection HL; auto|exact HC].
Qed.

Lemma bytes_cmp_antisym : forall l1 l2, bytes_cmp l2 l1 = CompOpp (bytes_cmp l1 l2).
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2]; try reflexivity.
  cbn [bytes_cmp]. rewrite (Z.compare_antisym (Int.unsigned x) (Int.unsigned y)).
  destruct (Z.compare (Int.unsigned x) (Int.unsigned y)); cbn [CompOpp]; [apply IH|reflexivity|reflexivity].
Qed.

Lemma bytes_cmp_trans c : forall l1 l2 l3,
  bytes_cmp l1 l2 = c -> bytes_cmp l2 l3 = c -> length l1 = length l2 -> length l2 = length l3 ->
  bytes_cmp l1 l3 = c.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] [|z l3] H12 H23 L12 L23; try discriminate;
    cbn [bytes_cmp length] in *; try congruence.
  revert H12 H23.
  destruct (Z.compare_spec (Int.unsigned x) (Int.unsigned y)) as [E1|E1|E1];
    destruct (Z.compare_spec (Int.unsigned y) (Int.unsigned z)) as [E2|E2|E2];
    intros H12 H23; try congruence.
  - replace (Int.unsigned x ?= Int.unsigned z) with Eq by (symmetry; apply Z.compare_eq_iff; lia).
    eapply IH; [exact H12|exact H23|congruence|congruence].
  - replace (Int.unsigned x ?= Int.unsigned z) with Lt by (symmetry; apply Z.compare_lt_iff; lia).
    exact H23.
  - replace (Int.unsigned x ?= Int.unsigned z) with Gt by (symmetry; apply Z.compare_gt_iff; lia).
    exact H23.
  - replace (Int.unsigned x ?= Int.unsigned z) with Lt by (symmetry; apply Z.compare_lt_iff; lia).
    exact H12.
  - replace (Int.unsigned x ?= Int.unsigned z) with Lt by (symmetry; apply Z.compare_lt_iff; lia).
    exact H12.
  - replace (Int.unsigned x ?= Int.unsigned z) with Gt by (symmetry; apply Z.compare_gt_iff; lia).
    exact H12.
  - replace (Int.unsigned x ?= Int.unsigned z) with Gt by (symmetry; apply Z.compare_gt_iff; lia).
    exact H12.
Qed.

Lemma memcmp_sign_zero c r : memcmp_sign c r -> (r = Int.zero <-> c = Eq).
Proof.
  destruct c; cbn; intros H; split; intros H'; try reflexivity; try discriminate;
    try exact H; subst r; change (Int.signed Int.zero) with 0 in H; lia.
Qed.
