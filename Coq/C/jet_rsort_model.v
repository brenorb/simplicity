(** Explicit model of [simplicity_rsort(a, len)] (C/rsort.c) for the
    Elements environment unit, where it is an external declaration
    ([EF_external "simplicity_rsort"]): the fee outputs of
    [simplicity_elements_mallocTransaction] are sorted with it before
    [sumFees] tallies them.

    The statement is the contract rsort.h documents: on an array of [n]
    pointers to readable SHA-256 midstates, the call either fails (returns
    false, when its internal allocation fails) and changes nothing the
    caller can read, or returns true and leaves a permutation of the same
    pointers sorted for [memcmp] order -- the byte order [bytes_cmp] of
    C/jet_memcmp_model.v on the midstate words ([words_bytes]).  Only the
    pointer array is written.

    This is a premise for theorems about the unit in which rsort.c is not
    compiled.  It is not proven here: discharging it means adding rsort.c to
    a unit and verifying it (it is a radix sort that also calls [memset]),
    which is recorded as an open obligation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs.
Require Import C.jet_memcmp_model C.jet_memcmp_words.
Import ListNotations.
Local Open Scope Z_scope.

Definition rsort_sig : signature :=
  mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tint8unsigned cc_default.

(** Slot [k] of the pointer array holds the pointer [pb (s k), po (s k)]. *)
Definition ptr_array_at (m : mem) (ba : block) (oa : Z) (n : nat)
    (pb : nat -> block) (po : nat -> ptrofs) (s : nat -> nat) : Prop :=
  forall k, (k < n)%nat ->
    Mem.load Mptr m ba (oa + 8 * Z.of_nat k) = Some (Vptr (pb (s k)) (po (s k))).

(** [s] permutes the indices below [n]. *)
Definition perm_below (n : nat) (s : nat -> nat) : Prop :=
  (forall k, (k < n)%nat -> (s k < n)%nat) /\
  (forall j k, (j < n)%nat -> (k < n)%nat -> s j = s k -> j = k).

Definition rsort_model : Prop :=
  forall (ge : Senv.t) m ba oa (n : nat) (pb : nat -> block) (po : nat -> ptrofs) (W : nat -> list int),
    Z.of_nat n <= 4294967295 ->
    Ptrofs.unsigned oa + 8 * Z.of_nat n <= Ptrofs.max_unsigned ->
    ptr_array_at m ba (Ptrofs.unsigned oa) n pb po (fun k => k) ->
    Mem.range_perm m ba (Ptrofs.unsigned oa) (Ptrofs.unsigned oa + 8 * Z.of_nat n) Cur Writable ->
    (forall j, (j < n)%nat -> length (W j) = 8%nat /\
       Ptrofs.unsigned (po j) + 32 <= Ptrofs.max_unsigned /\
       (pb j <> ba \/ Ptrofs.unsigned (po j) + 32 <= Ptrofs.unsigned oa \/
        Ptrofs.unsigned oa + 8 * Z.of_nat n <= Ptrofs.unsigned (po j)) /\
       forall i x, nth_error (W j) i = Some x ->
         Mem.load Mint32 m (pb j) (Ptrofs.unsigned (po j) + 4 * Z.of_nat i) = Some (Vint x)) ->
    exists (ok : bool) m',
      external_call (EF_external "simplicity_rsort" rsort_sig) ge
        [Vptr ba oa; Vlong (Int64.repr (Z.of_nat n))] m E0
        (Vint (if ok then Int.one else Int.zero)) m' /\
      (forall b, Mem.valid_block m b -> Mem.valid_block m' b) /\
      (forall b ofs k p, Mem.valid_block m b -> (Mem.perm m' b ofs k p <-> Mem.perm m b ofs k p)) /\
      (forall ch b ofs, Mem.valid_block m b ->
         (b <> ba \/ ofs + size_chunk ch <= Ptrofs.unsigned oa \/
          Ptrofs.unsigned oa + 8 * Z.of_nat n <= ofs) ->
         Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
      (ok = false ->
         forall ch ofs, Mem.load ch m' ba ofs = Mem.load ch m ba ofs) /\
      (ok = true ->
         exists s, perm_below n s /\
           ptr_array_at m' ba (Ptrofs.unsigned oa) n pb po s /\
           forall i j, (i <= j)%nat -> (j < n)%nat ->
             bytes_cmp (words_bytes (W (s j))) (words_bytes (W (s i))) <> Lt).
