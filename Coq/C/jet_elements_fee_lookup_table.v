(** Read-only storage for the real fee search, with the original bytewise
    comparison keys. Empty searches do not require a nonnull table pointer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values.
Require Import C.jet_memcmp_model C.jet_elements_fee_lookup_branches.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Record fee_entry := mk_fee_entry {
  fee_entry_block : block;
  fee_entry_offset : Z;
  fee_entry_key : list int;
  fee_entry_amount : int64
}.
Definition fee_entry_at m x :=
  0<=fee_entry_offset x /\ fee_entry_offset x+224<=Ptrofs.max_unsigned+1 /\
  length(fee_entry_key x)=32%nat /\
  bytes_at m (fee_entry_block x) (fee_entry_offset x) (fee_entry_key x) /\
  Mem.load Mint64 m (fee_entry_block x) (fee_entry_offset x+216)=Some(Vlong(fee_entry_amount x)).
Definition fee_key_at m bk base key :=
  0<=base /\ base+32<=Ptrofs.max_unsigned+1 /\ length key=32%nat /\ bytes_at m bk base key.
Definition fee_table_at m bt base entries :=
  0<=base /\ base+8*Z.of_nat(length entries)<=Ptrofs.max_unsigned /\
  (forall j x,nth_error entries j=Some x ->
    Mem.load Mptr m bt (base+8*Z.of_nat j)=Some(Vptr(fee_entry_block x)(Ptrofs.repr(fee_entry_offset x))) /\
    fee_entry_at m x).
Definition fee_lookup_storage m keyval tableval key entries :=
  entries=[] \/ exists bk keybase bt base,
    keyval=Vptr bk (Ptrofs.repr keybase) /\ tableval=Vptr bt (Ptrofs.repr base) /\
    fee_key_at m bk keybase key /\ fee_table_at m bt base entries.

Lemma fee_firstn_entry {A} k (xs : list A) j x :
  nth_error (firstn k xs) j=Some x -> nth_error xs j=Some x.
Proof.
  induction k as [|k IH] in xs,j|-*;destruct xs,j;cbn;try discriminate;auto.
Qed.
Lemma fee_skipn_entry {A} k (xs : list A) j : nth_error (skipn k xs) j=nth_error xs (k+j)%nat.
Proof.
  induction k as [|k IH] in xs|-*;[reflexivity|].
  destruct xs as [|x xs];cbn;[destruct j;reflexivity|apply IH].
Qed.

Lemma fee_table_firstn m bt base entries k : fee_table_at m bt base entries ->
  fee_table_at m bt base (firstn k entries).
Proof.
  intros (Base & Max & Rows);split;[exact Base|];split.
  - assert (N : Z.of_nat(length(firstn k entries))<=Z.of_nat(length entries)).
    { rewrite firstn_length;lia. }
    lia.
  - intros j x At;apply Rows;exact (fee_firstn_entry k entries j x At).
Qed.

Lemma fee_table_skipn m bt base entries k : (k<=length entries)%nat -> fee_table_at m bt base entries ->
  fee_table_at m bt (base+8*Z.of_nat k) (skipn k entries).
Proof.
  intros K (Base & Max & Rows);split;[pose proof (Nat2Z.is_nonneg k);lia|];split.
  - rewrite skipn_length,Nat2Z.inj_sub by exact K;lia.
  - intros j x At;rewrite fee_skipn_entry in At.
    destruct (Rows (k+j)%nat x At) as (Load & Entry);split;[|exact Entry].
    rewrite Nat2Z.inj_add in Load.
    replace (base+8*Z.of_nat k+8*Z.of_nat j) with (base+8*(Z.of_nat k+Z.of_nat j)) by ring;exact Load.
Qed.

Definition fee_search_part (high : bool) (entries : list fee_entry) :=
  if high then skipn (S(length entries/2)) entries else firstn (length entries/2) entries.
Lemma fee_search_part_length high entries : entries<>[] ->
  Z.of_nat(length(fee_search_part high entries))=fee_lookup_next_length high (Z.of_nat(length entries)).
Proof.
  intro Nonempty.
  assert (Less : (S(length entries/2)<=length entries)%nat).
  { apply Nat.div_lt;[destruct entries;cbn in *;[congruence|lia]|lia]. }
  assert (Half : (length entries/2<=length entries)%nat) by lia.
  destruct high;unfold fee_search_part,fee_lookup_next_length.
  - rewrite skipn_length,Nat2Z.inj_sub by exact Less;rewrite Nat2Z.inj_succ,Nat2Z.inj_div;reflexivity.
  - rewrite firstn_length_le by exact Half;rewrite Nat2Z.inj_div;reflexivity.
Qed.

Lemma fee_search_part_small high entries : entries<>[] ->
  (length(fee_search_part high entries)<length entries)%nat.
Proof.
  intro Nonempty;destruct entries as [|x entries];[contradiction|].
  pose proof (Nat.div_lt (length(x::entries)) 2 ltac:(cbn;lia) ltac:(lia)) as Half.
  destruct high;unfold fee_search_part;[rewrite skipn_length|rewrite firstn_length_le by lia];lia.
Qed.

Lemma fee_search_part_in high entries x : In x (fee_search_part high entries) -> In x entries.
Proof.
  intro InPart;destruct high;unfold fee_search_part in InPart.
  - rewrite <-(firstn_skipn (S(length entries/2)) entries);apply in_or_app;right;exact InPart.
  - rewrite <-(firstn_skipn (length entries/2) entries);apply in_or_app;left;exact InPart.
Qed.

Lemma fee_table_part high m bt base entries : entries<>[] -> fee_table_at m bt base entries ->
  fee_table_at m bt (fee_lookup_next_base high base (Z.of_nat(length entries))) (fee_search_part high entries).
Proof.
  intros Nonempty Table;destruct high;unfold fee_lookup_next_base,fee_search_part.
  - assert (Half : Z.of_nat(length entries)/2=Z.of_nat(length entries/2))
      by (symmetry;apply Nat2Z.inj_div).
    rewrite Half.
    replace (Z.of_nat(length entries/2)+1) with (Z.of_nat(S(length entries/2))) by lia.
    apply fee_table_skipn;[|exact Table].
    apply Nat.div_lt;[destruct entries;cbn in *;[congruence|lia]|lia].
  - apply fee_table_firstn;exact Table.
Qed.
