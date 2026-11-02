(** The libc [memcmp] model is consistent with CompCert's axioms on
    external functions, alone and together with the other three models.

    [memcmp_model] is a premise about the abstract parameter
    [external_functions_sem].  This module gives an external semantics for
    [memcmp] (compare the readable bytes, no memory effect, result [-1], [0]
    or [1]) that satisfies [extcall_properties], and extends the joint
    assignment of [C.jet_library_models_consistent] with it, so all four
    library models hold at once under one interpretation that meets
    CompCert's whole interface.  It is a relative-consistency result and
    discharges none of the models. *)
From Coq Require Import String ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memdata Memory Events Globalenvs.
Require Import C.jet_memcpy_model C.jet_memcpy_model_consistent C.jet_ctz_model
  C.jet_ctz_model_consistent C.jet_memset_model C.jet_memcmp_model C.jet_library_models_consistent.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 20.

Lemma match_traces_E0_inv ge t : match_traces ge E0 t -> t = E0.
Proof. intros H; inversion H; reflexivity. Qed.

Lemma lessdef_ptr_inv b o v : Val.lessdef (Vptr b o) v -> v = Vptr b o.
Proof. intros H; inversion H; reflexivity. Qed.

Lemma lessdef_long_inv x v : Val.lessdef (Vlong x) v -> v = Vlong x.
Proof. intros H; inversion H; reflexivity. Qed.

Lemma lessdef_int_inv x v : Val.lessdef (Vint x) v -> v = Vint x.
Proof. intros H; inversion H; reflexivity. Qed.

Definition memcmp_model_for (sem : extcall_sem) : Prop :=
  forall (ge : Senv.t) m b1 o1 b2 o2 (l1 l2 : list int),
    length l1 = length l2 ->
    Z.of_nat (length l1) <= Int64.max_unsigned ->
    Ptrofs.unsigned o1 + Z.of_nat (length l1) <= Ptrofs.max_unsigned + 1 ->
    Ptrofs.unsigned o2 + Z.of_nat (length l1) <= Ptrofs.max_unsigned + 1 ->
    bytes_at m b1 (Ptrofs.unsigned o1) l1 -> bytes_at m b2 (Ptrofs.unsigned o2) l2 ->
    exists r,
      sem ge [Vptr b1 o1; Vptr b2 o2; Vlong (Int64.repr (Z.of_nat (length l1)))] m E0 (Vint r) m /\
      memcmp_sign (bytes_cmp l1 l2) r.

Lemma memcmp_model_is_instance :
  memcmp_model <-> memcmp_model_for (external_functions_sem "memcmp" memcmp_sig).
Proof. reflexivity. Qed.


(** ** libc [memcmp]: compare [n] readable bytes, no memory effect; the
    result is [-1], [0] or [1]. *)

Definition cmp_int (c : Datatypes.comparison) : int :=
  match c with Eq => Int.zero | Lt => Int.mone | Gt => Int.one end.

Lemma cmp_int_sign c : memcmp_sign c (cmp_int c).
Proof. destruct c; cbn; [reflexivity|reflexivity|reflexivity]. Qed.

Definition libc_memcmp_sem : extcall_sem := fun _ args m t res m' =>
  exists b1 o1 b2 o2 i l1 l2, args = [Vptr b1 o1; Vptr b2 o2; Vlong i] /\
    length l1 = Z.to_nat (Int64.unsigned i) /\ length l2 = length l1 /\
    bytes_at m b1 (Ptrofs.unsigned o1) l1 /\ bytes_at m b2 (Ptrofs.unsigned o2) l2 /\
    t = E0 /\ m' = m /\ res = Vint (cmp_int (bytes_cmp l1 l2)).

Lemma bytes_at_extends m m' b o l : Mem.extends m m' -> bytes_at m b o l -> bytes_at m' b o l.
Proof.
  intros E B j J. destruct (Mem.load_extends _ _ _ _ _ _ E (B j J)) as (v & L & D).
  apply lessdef_int_inv in D; subst; exact L.
Qed.

Lemma bytes_at_inject f m m' b b' d o l :
  Mem.inject f m m' -> f b = Some (b', d) -> bytes_at m b (Ptrofs.unsigned o) l ->
  bytes_at m' b' (Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr d))) l.
Proof.
  intros I F B. destruct l as [|x l]; [intros j J; cbn in J; lia|].
  assert (A : Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr d)) = Ptrofs.unsigned o + d).
  { eapply Mem.address_inject; [exact I| |exact F].
    pose proof (Mem.load_valid_access _ _ _ _ _ (B 0%nat ltac:(cbn; lia))) as V.
    rewrite Z.add_0_r in V. eapply Mem.valid_access_perm; exact V. }
  intros j J. destruct (Mem.load_inject _ _ _ _ _ _ _ _ _ I (B j J) F) as (v & L & D).
  inversion D; subst. rewrite A. replace (Ptrofs.unsigned o + d + Z.of_nat j)
    with (Ptrofs.unsigned o + Z.of_nat j + d) by ring. exact L.
Qed.

Lemma bytes_at_det m b o l l' : length l = length l' ->
  bytes_at m b o l -> bytes_at m b o l' -> l = l'.
Proof.
  intros N B B'. apply nth_ext with Int.zero Int.zero; [exact N|].
  intros j J. pose proof (B j J) as L. rewrite (B' j ltac:(lia)) in L. congruence.
Qed.

Lemma libc_memcmp_sem_properties : extcall_properties libc_memcmp_sem memcmp_sig.
Proof.
  constructor.
  - intros * (b1 & o1 & b2 & o2 & i & l1 & l2 & _ & _ & _ & _ & _ & _ & _ & ->); cbn; auto.
  - intros * _ H; exact H.
  - intros * (b1 & o1 & b2 & o2 & i & l1 & l2 & _ & _ & _ & _ & _ & _ & -> & _) V; exact V.
  - intros * (b1 & o1 & b2 & o2 & i & l1 & l2 & _ & _ & _ & _ & _ & _ & -> & _) V P; exact P.
  - intros * (b1 & o1 & b2 & o2 & i & l1 & l2 & _ & _ & _ & _ & _ & _ & -> & _) V L N; exact L.
  - intros * (b1 & o1 & b2 & o2 & i & l1 & l2 & -> & N1 & N2 & B1 & B2 & -> & -> & ->) E LD.
    inversion LD as [|v1 v2 k1 k2 D1 LD1]; subst.
    inversion LD1 as [|v3 v4 k3 k4 D2 LD2]; subst.
    inversion LD2 as [|v5 v6 k5 k6 D3 LD3]; subst. inversion LD3; subst.
    apply lessdef_ptr_inv in D1, D2. apply lessdef_long_inv in D3. subst.
    exists (Vint (cmp_int (bytes_cmp l1 l2))), m1'.
    split; [exists b1, o1, b2, o2, i, l1, l2; repeat split; auto; eapply bytes_at_extends; eauto|].
    split; [constructor|]. split; [exact E|apply Mem.unchanged_on_refl].
  - intros * Sy (b1 & o1 & b2 & o2 & i & l1 & l2 & -> & N1 & N2 & B1 & B2 & -> & -> & ->) I IL.
    inversion IL as [|v1 v2 k1 k2 J1 IL1]; subst.
    inversion IL1 as [|v3 v4 k3 k4 J2 IL2]; subst.
    inversion IL2 as [|v5 v6 k5 k6 J3 IL3]; subst. inversion IL3; subst.
    inversion J3; subst.
    inversion J1 as [| | | |c1 p1 b1' p1' d1 F1 P1|]; subst.
    inversion J2 as [| | | |c2 p2 b2' p2' d2 F2 P2|]; subst.
    exists f, (Vint (cmp_int (bytes_cmp l1 l2))), m1'.
    split.
    { exists b1', (Ptrofs.add o1 (Ptrofs.repr d1)), b2', (Ptrofs.add o2 (Ptrofs.repr d2)), i, l1, l2.
      repeat split; auto; eapply bytes_at_inject; eauto. }
    split; [constructor|]. split; [exact I|].
    split; [apply Mem.unchanged_on_refl|]. split; [apply Mem.unchanged_on_refl|].
    split; [apply inject_incr_refl|]. intros c d e N F; congruence.
  - intros * (b1 & o1 & b2 & o2 & i & l1 & l2 & _ & _ & _ & _ & _ & -> & _); cbn; lia.
  - intros * H T. destruct H as (b1 & o1 & b2 & o2 & i & l1 & l2 & A & N1 & N2 & B1 & B2 & -> & M & R).
    apply match_traces_E0_inv in T; subst t2.
    exists vres1, m1. exists b1, o1, b2, o2, i, l1, l2; repeat split; auto.
  - intros * (b1 & o1 & b2 & o2 & i & l1 & l2 & -> & N1 & N2 & B1 & B2 & -> & -> & ->)
      (c1 & p1 & c2 & p2 & j & k1 & k2 & A & M1 & M2 & C1 & C2 & -> & -> & ->).
    injection A as <- <- <- <- <-.
    assert (E1 : l1 = k1) by (eapply bytes_at_det; [congruence|exact B1|exact C1]).
    assert (E2 : l2 = k2) by (eapply bytes_at_det; [congruence|exact B2|exact C2]).
    subst. split; [constructor|auto].
Qed.

Theorem memcmp_model_holds_for_libc_memcmp_sem : memcmp_model_for libc_memcmp_sem.
Proof.
  intros ge m b1 o1 b2 o2 l1 l2 N Max _ _ B1 B2.
  exists (cmp_int (bytes_cmp l1 l2)). split; [|apply cmp_int_sign].
  exists b1, o1, b2, o2, (Int64.repr (Z.of_nat (length l1))), l1, l2.
  rewrite Int64.unsigned_repr by lia. rewrite Nat2Z.id. repeat split; auto.
Qed.

(** One interpretation of every external function: the three-model
    assignment of [library_semantics], plus [memcmp]. *)
Definition library_semantics_with_memcmp (id : string) (sg : signature) : extcall_sem :=
  if string_dec id "memcmp" then
    if signature_eq sg memcmp_sig then libc_memcmp_sem else no_behaviour
  else library_semantics id sg.

Theorem library_models_consistent_with_memcmp :
  exists S : string -> signature -> extcall_sem,
    (forall id sg, extcall_properties (S id sg) sg) /\
    memcpy_model_for (S "memcpy"%string memcpy_sig) /\
    ctz_model_for (S "__builtin_ctzl"%string ctz_sig) /\
    memset_model_for (S "memset"%string memset_sig) /\
    memcmp_model_for (S "memcmp"%string memcmp_sig).
Proof.
  exists library_semantics_with_memcmp. split; [|split; [|split; [|split]]].
  - intros id sg. unfold library_semantics_with_memcmp.
    destruct (string_dec id "memcmp");
      [destruct (signature_eq sg memcmp_sig) as [->|];
       [exact libc_memcmp_sem_properties|apply no_behaviour_ok]|].
    unfold library_semantics.
    destruct (string_dec id "memcpy");
      [destruct (signature_eq sg memcpy_sig) as [->|];
       [exact libc_memcpy_sem_ok|apply no_behaviour_ok]|].
    destruct (string_dec id "__builtin_ctzl");
      [destruct (signature_eq sg ctz_sig) as [->|];
       [exact libc_ctz_sem_ok|apply no_behaviour_ok]|].
    destruct (string_dec id "memset");
      [destruct (signature_eq sg memset_sig) as [->|];
       [exact libc_memset_sem_ok|apply no_behaviour_ok]|apply no_behaviour_ok].
  - unfold library_semantics_with_memcmp, library_semantics; cbn.
    destruct (signature_eq memcpy_sig memcpy_sig) as [_|N]; [|contradiction].
    exact libc_memcpy_sem_models.
  - unfold library_semantics_with_memcmp, library_semantics; cbn.
    destruct (signature_eq ctz_sig ctz_sig) as [_|N]; [|contradiction].
    exact libc_ctz_sem_models.
  - unfold library_semantics_with_memcmp, library_semantics; cbn.
    destruct (signature_eq memset_sig memset_sig) as [_|N]; [|contradiction].
    exact libc_memset_sem_models.
  - unfold library_semantics_with_memcmp; cbn.
    destruct (signature_eq memcmp_sig memcmp_sig) as [_|N]; [|contradiction].
    exact memcmp_model_holds_for_libc_memcmp_sem.
Qed.
