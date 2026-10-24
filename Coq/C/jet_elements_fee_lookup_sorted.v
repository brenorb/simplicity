(** The proved C binary search implements ordinary key lookup on a uniquely
    sorted table. This does not identify the table with canonical fee sums. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jets_elements C.jet_elements_linkage C.jet_memcmp_model.
Require Import C.jet_elements_fee_lookup_table C.jet_elements_fee_lookup_loop.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fee_lookup_sorted (entries : list fee_entry) := forall i j x y,
  (i<j)%nat -> nth_error entries i=Some x -> nth_error entries j=Some y ->
  bytes_cmp (fee_entry_key x) (fee_entry_key y)=Lt.
Fixpoint fee_lookup_find key entries : option int64 := match entries with
  | []=>None
  | x::xs=>if list_eq_dec Int.eq_dec key (fee_entry_key x)
      then Some(fee_entry_amount x) else fee_lookup_find key xs end.
Definition fee_lookup_value key entries := match fee_lookup_find key entries with
  | None=>Int64.zero | Some value=>value end.

Lemma fee_lookup_find_app key xs ys : fee_lookup_find key (xs++ys)=
  match fee_lookup_find key xs with Some value=>Some value | None=>fee_lookup_find key ys end.
Proof.
  induction xs as [|x xs IH];[reflexivity|];cbn [app fee_lookup_find].
  destruct (list_eq_dec Int.eq_dec key (fee_entry_key x));[reflexivity|exact IH].
Qed.
Lemma fee_lookup_find_absent key entries : Forall (fun x=>key<>fee_entry_key x) entries ->
  fee_lookup_find key entries=None.
Proof.
  intro Absent;induction Absent as [|x xs Ne Rest IH];[reflexivity|].
  cbn [fee_lookup_find];destruct (list_eq_dec Int.eq_dec key (fee_entry_key x));[contradiction|exact IH].
Qed.
Lemma fee_lookup_find_head key x xs : key=fee_entry_key x ->
  fee_lookup_find key (x::xs)=Some(fee_entry_amount x).
Proof.
  intro Equal;cbn [fee_lookup_find];destruct (list_eq_dec Int.eq_dec key (fee_entry_key x));congruence.
Qed.

Lemma fee_split_at {A} j (entries : list A) x : nth_error entries j=Some x ->
  entries=firstn j entries++x::skipn (S j) entries.
Proof.
  induction j as [|j IH] in entries|-*;destruct entries as [|y entries];cbn;intro At;try discriminate.
  - injection At as <-;reflexivity.
  - f_equal;apply IH;exact At.
Qed.

Lemma fee_lookup_sorted_firstn k entries : fee_lookup_sorted entries -> fee_lookup_sorted (firstn k entries).
Proof.
  intros Sorted i j x y IJ X Y;eapply Sorted;[exact IJ|exact (fee_firstn_entry k entries i x X)|
    exact (fee_firstn_entry k entries j y Y)].
Qed.
Lemma fee_lookup_sorted_skipn k entries : fee_lookup_sorted entries -> fee_lookup_sorted (skipn k entries).
Proof.
  intros Sorted i j x y IJ X Y;rewrite fee_skipn_entry in X,Y.
  eapply (Sorted (k+i)%nat (k+j)%nat x y);[lia|exact X|exact Y].
Qed.
Lemma fee_lookup_sorted_part high entries : fee_lookup_sorted entries -> fee_lookup_sorted (fee_search_part high entries).
Proof.
  intro Sorted;destruct high;unfold fee_search_part;[apply fee_lookup_sorted_skipn|apply fee_lookup_sorted_firstn];exact Sorted.
Qed.

Lemma fee_lookup_pivot_order entries j x : fee_lookup_sorted entries -> nth_error entries j=Some x ->
  Forall (fun y=>bytes_cmp (fee_entry_key y) (fee_entry_key x)=Lt) (firstn j entries) /\
  Forall (fun y=>bytes_cmp (fee_entry_key x) (fee_entry_key y)=Lt) (skipn (S j) entries).
Proof.
  intros Sorted At;split;apply Forall_forall;intros y InPart;apply In_nth_error in InPart as [i Y].
  - assert (I : (i<j)%nat).
    { assert (B : (i<length(firstn j entries))%nat) by (apply nth_error_Some;rewrite Y;discriminate).
      rewrite firstn_length in B;lia. }
    eapply Sorted;[exact I|exact (fee_firstn_entry j entries i y Y)|exact At].
  - rewrite fee_skipn_entry in Y;eapply (Sorted j (S j+i)%nat x y);[lia|exact At|exact Y].
Qed.

Lemma fee_lookup_partition key entries j x : nth_error entries j=Some x -> fee_lookup_sorted entries ->
  Forall (fun y=>length(fee_entry_key y)=length key) entries ->
  fee_lookup_value key entries=match bytes_cmp key (fee_entry_key x) with
    | Eq=>fee_entry_amount x
    | Lt=>fee_lookup_value key (firstn j entries)
    | Gt=>fee_lookup_value key (skipn (S j) entries) end.
Proof.
  intros At Sorted Lengths.
  destruct (fee_lookup_pivot_order entries j x Sorted At) as (Before & After).
  pose proof (proj1 (Forall_forall _ _) Lengths x (nth_error_In _ _ At)) as XLen.
  destruct (bytes_cmp key (fee_entry_key x)) eqn:Which.
  - assert (Equal : key=fee_entry_key x) by (apply bytes_cmp_eq;[symmetry;exact XLen|exact Which]).
    assert (Absent : Forall (fun y=>key<>fee_entry_key y) (firstn j entries)).
    { apply Forall_forall;intros y Y EqY.
      pose proof (proj1 (Forall_forall _ _) Before y Y) as Order.
      cbv beta in Order.
      rewrite <-EqY,Which in Order;discriminate. }
    unfold fee_lookup_value;rewrite (fee_split_at j entries x At) at 1.
    rewrite fee_lookup_find_app,(fee_lookup_find_absent key _ Absent),fee_lookup_find_head by exact Equal;reflexivity.
  - assert (Absent : Forall (fun y=>key<>fee_entry_key y) (x::skipn (S j) entries)).
    { constructor.
      - intro Equal;rewrite Equal,bytes_cmp_refl in Which;discriminate.
      - apply Forall_forall;intros y Y EqY.
        pose proof (proj1 (Forall_forall _ _) After y Y) as Order.
        cbv beta in Order.
        pose proof (bytes_cmp_antisym (fee_entry_key x) (fee_entry_key y)) as Opposite.
        rewrite Order,<-EqY,Which in Opposite;discriminate. }
    unfold fee_lookup_value;rewrite (fee_split_at j entries x At) at 1.
    rewrite fee_lookup_find_app,(fee_lookup_find_absent key _ Absent).
    destruct (fee_lookup_find key (firstn j entries));reflexivity.
  - assert (Absent : Forall (fun y=>key<>fee_entry_key y) (firstn j entries)).
    { apply Forall_forall;intros y Y EqY.
      pose proof (proj1 (Forall_forall _ _) Before y Y) as Order.
      cbv beta in Order.
      rewrite <-EqY,Which in Order;discriminate. }
    assert (Different : key<>fee_entry_key x) by (intro Equal;rewrite Equal,bytes_cmp_refl in Which;discriminate).
    unfold fee_lookup_value;rewrite (fee_split_at j entries x At) at 1.
    rewrite fee_lookup_find_app,(fee_lookup_find_absent key _ Absent);cbn [fee_lookup_find].
    destruct (list_eq_dec Int.eq_dec key (fee_entry_key x));[contradiction|reflexivity].
Qed.

Theorem fee_lookup_answer_sorted fuel key entries : (length entries<=fuel)%nat -> fee_lookup_sorted entries ->
  Forall (fun y=>length(fee_entry_key y)=length key) entries ->
  fee_lookup_answer fuel key entries=fee_lookup_value key entries.
Proof.
  induction fuel as [|fuel IH] in entries|-*;intros Fuel Sorted Lengths.
  - destruct entries;[reflexivity|cbn in Fuel;lia].
  - destruct entries as [|head tail];[reflexivity|].
    set (entries:=head::tail) in *.
    assert (Nonempty : entries<>[]) by (unfold entries;discriminate).
    assert (Mid : (length entries/2<length entries)%nat) by
      (apply Nat.div_lt;[unfold entries;cbn;lia|lia]).
    destruct (nth_error entries (length entries/2)) as [x|] eqn:At.
    2: { apply nth_error_None in At;lia. }
    assert (Part : forall high,fee_lookup_answer fuel key (fee_search_part high entries)=
      fee_lookup_value key (fee_search_part high entries)).
    { intro high;apply IH.
      - pose proof (fee_search_part_small high entries Nonempty);lia.
      - apply fee_lookup_sorted_part;exact Sorted.
      - apply Forall_forall;intros y Y;apply (proj1 (Forall_forall _ _) Lengths y).
        exact (fee_search_part_in high entries y Y). }
    cbn [fee_lookup_answer];rewrite At,(fee_lookup_partition key entries _ x At Sorted Lengths).
    destruct (bytes_cmp key (fee_entry_key x));[reflexivity|exact (Part false)|exact (Part true)].
Qed.

Lemma fee_lookup_storage_lengths m keyval tableval key entries : fee_lookup_storage m keyval tableval key entries ->
  Forall (fun x=>length(fee_entry_key x)=length key) entries.
Proof.
  intros [Empty|(bk & keybase & bt & base & KeyVal & TableVal & (_ & _ & KeyLen & _) & (_ & _ & Rows))].
  - subst entries;constructor.
  - apply Forall_forall;intros x X;apply In_nth_error in X as [j At].
    destruct (Rows j x At) as (_ & _ & _ & EntryLen & _);congruence.
Qed.

Theorem eval_fee_lookup_sorted (Model : memcmp_model) m keyval tableval key entries :
  fee_lookup_storage m keyval tableval key entries -> fee_lookup_sorted entries ->
  Clight2.eval_funcall elements_ge m (Internal f_lookup_fee)
    [keyval;tableval;Vlong(Int64.repr(Z.of_nat(length entries)))] E0 m (Vlong(fee_lookup_value key entries)).
Proof.
  intros Storage Sorted.
  rewrite <-(fee_lookup_answer_sorted (length entries) key entries ltac:(lia) Sorted
    (fee_lookup_storage_lengths m keyval tableval key entries Storage)).
  apply (eval_fee_lookup_table Model);exact Storage.
Qed.

Lemma fee_lookup_key_unique entries i j x y : fee_lookup_sorted entries ->
  nth_error entries i=Some x -> nth_error entries j=Some y -> fee_entry_key x=fee_entry_key y -> x=y.
Proof.
  intros Sorted X Y Equal;destruct (Nat.lt_trichotomy i j) as [IJ|[Same|JI]].
  - pose proof (Sorted i j x y IJ X Y) as Order;rewrite Equal,bytes_cmp_refl in Order;discriminate.
  - subst j;congruence.
  - pose proof (Sorted j i y x JI Y X) as Order;rewrite Equal,bytes_cmp_refl in Order;discriminate.
Qed.

Lemma fee_lookup_find_present key entries x : fee_lookup_sorted entries -> In x entries ->
  key=fee_entry_key x -> fee_lookup_find key entries=Some(fee_entry_amount x).
Proof.
  induction entries as [|head tail IH];intros Sorted Present Equal;[contradiction|].
  cbn [fee_lookup_find];destruct (list_eq_dec Int.eq_dec key (fee_entry_key head)) as [HeadKey|Other].
  - assert (Same : head=x).
    { apply In_nth_error in Present as [j At];eapply (fee_lookup_key_unique (head::tail) 0%nat j head x);
        [exact Sorted|reflexivity|exact At|congruence]. }
    now subst head.
  - destruct Present as [Same|InTail];[subst head;contradiction|].
    apply IH;[change (fee_lookup_sorted (skipn 1 (head::tail)));apply fee_lookup_sorted_skipn;exact Sorted|
      exact InTail|exact Equal].
Qed.

Corollary eval_fee_lookup_present (Model : memcmp_model) m keyval tableval key entries x :
  fee_lookup_storage m keyval tableval key entries -> fee_lookup_sorted entries ->
  In x entries -> key=fee_entry_key x ->
  Clight2.eval_funcall elements_ge m (Internal f_lookup_fee)
    [keyval;tableval;Vlong(Int64.repr(Z.of_nat(length entries)))] E0 m (Vlong(fee_entry_amount x)).
Proof.
  intros Storage Sorted Present Equal.
  pose proof (eval_fee_lookup_sorted Model m keyval tableval key entries Storage Sorted) as Call.
  unfold fee_lookup_value in Call;rewrite (fee_lookup_find_present key entries x Sorted Present Equal) in Call;exact Call.
Qed.

Corollary eval_fee_lookup_absent (Model : memcmp_model) m keyval tableval key entries :
  fee_lookup_storage m keyval tableval key entries -> fee_lookup_sorted entries ->
  Forall (fun x=>key<>fee_entry_key x) entries ->
  Clight2.eval_funcall elements_ge m (Internal f_lookup_fee)
    [keyval;tableval;Vlong(Int64.repr(Z.of_nat(length entries)))] E0 m (Vlong Int64.zero).
Proof.
  intros Storage Sorted Absent.
  pose proof (eval_fee_lookup_sorted Model m keyval tableval key entries Storage Sorted) as Call.
  unfold fee_lookup_value in Call;rewrite (fee_lookup_find_absent key entries Absent) in Call;exact Call.
Qed.
