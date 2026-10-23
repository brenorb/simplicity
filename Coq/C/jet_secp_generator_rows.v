(** Traverse the frozen initializer once in eight-word rows. Alignment and
    indexed correspondence are proved; no partial row may disappear silently. *)
From Coq Require Import List Lia.
Import ListNotations.
Set Default Timeout 10.
Fixpoint generator_chunks8 {A : Type} (ds : list A) : list (list A) :=
 match ds with
 | a::b::c::d::e::f::g::h::tail => [a;b;c;d;e;f;g;h]::generator_chunks8 tail
 | _ => []
 end.
Lemma generator_chunks8_exact {A : Type} n (ds : list A) :
 length ds=8*n -> concat (generator_chunks8 ds)=ds /\ length (generator_chunks8 ds)=n.
Proof.
 revert ds;induction n as [|n IH];intros ds Size.
 - assert (ds=[]) by (apply length_zero_iff_nil;lia);subst ds;split;reflexivity.
 - destruct ds as [|a [|b [|c [|d [|e [|f [|g [|h tail]]]]]]]];
     cbn [length] in Size;try lia.
   destruct (IH tail ltac:(lia)) as [Payload Count].
   cbn [generator_chunks8 concat length app];rewrite Payload,Count;split;reflexivity.
Qed.

Theorem generator_chunks8_word {A : Type} n (ds : list A) default :
 length ds=8*n -> forall i j,i<n -> j<8 ->
 nth (8*i+j) ds default=nth j (nth i (generator_chunks8 ds) []) default.
Proof.
 revert ds;induction n as [|n IH];intros ds Size i j Index Cell;[lia|].
 destruct ds as [|a [|b [|c [|d [|e [|f [|g [|h tail]]]]]]]];
   cbn [length] in Size;try lia.
 destruct i as [|i].
 - change (nth j (a::b::c::d::e::f::g::h::tail) default=nth j [a;b;c;d;e;f;g;h] default).
   destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];[reflexivity..|lia].
 - replace (8*S i+j) with (8+(8*i+j)) by lia.
   change (nth (8*i+j) tail default=nth j (nth i (generator_chunks8 tail) []) default).
   apply IH;lia.
Qed.

From Coq Require Import ZArith.
From compcert Require Import AST Integers.
Require Import C.jet_secp_generator_globals C.jet_secp_generator_table_samples
 C.jet_secp_storage_numeric.
Local Open Scope Z_scope.

Definition generator_table_rows high := generator_chunks8 (generator_table_init high).
Definition generator_row_word (row : list init_data) i := init_word64 (nth i row (Init_int64 Int64.zero)).
Definition generator_row_numeric row :=
 (field_storage_value (generator_row_word row),field_storage_value (fun i=>generator_row_word row (4+i)%nat)).
Definition generator_row_signed_numeric row (neg : bool) :=
 let '(x,y):=generator_row_numeric row in (x,if neg then (C.jet_secp_fe_math.feP-y) mod C.jet_secp_fe_math.feP else y).
Definition generator_table_signed_rows high (neg : bool) :=
 let rows:=map (fun row=>generator_row_signed_numeric row neg) (generator_table_rows high) in
 if neg then rev rows else rows.

Lemma generator_table_chunk_size high :
 length (generator_table_init high)=(8*Z.to_nat 8192)%nat.
Proof.
 apply Nat2Z.inj;rewrite Nat2Z.inj_mul,Z2Nat.id by lia.
 change (Z.of_nat 8) with 8;rewrite generator_table_length;reflexivity.
Qed.

Theorem generator_table_rows_exact high :
 concat (generator_table_rows high)=generator_table_init high /\
 Z.of_nat (length (generator_table_rows high))=8192.
Proof.
 destruct (generator_chunks8_exact (Z.to_nat 8192) (generator_table_init high)
   (generator_table_chunk_size high)) as [Payload Count].
 split;[exact Payload|unfold generator_table_rows;rewrite Count,Z2Nat.id by lia;reflexivity].
Qed.

Theorem generator_table_row_word high index j :
 Z.of_nat index<8192 -> (j<8)%nat ->
 generator_row_word (nth index (generator_table_rows high) []) j=generator_entry_words high index j.
Proof.
 intros Index Cell.
 unfold generator_row_word,generator_table_rows,generator_entry_words,generator_table_word.
 f_equal;symmetry;apply (generator_chunks8_word (Z.to_nat 8192));
   [apply generator_table_chunk_size| |exact Cell].
 apply Nat2Z.inj_lt;rewrite Z2Nat.id by lia;exact Index.
Qed.
Theorem generator_table_row_numeric high index : Z.of_nat index<8192 ->
 generator_row_numeric (nth index (generator_table_rows high) [])=generator_entry_numeric high index.
Proof.
 intro Index;unfold generator_row_numeric,generator_entry_numeric,field_storage_value.
 repeat rewrite generator_table_row_word by lia;reflexivity.
Qed.
Theorem generator_table_row_signed_numeric high index neg : Z.of_nat index<8192 ->
 generator_row_signed_numeric (nth index (generator_table_rows high) []) neg=
 generator_entry_signed_numeric high index neg.
Proof.
 intro Index;unfold generator_row_signed_numeric,generator_entry_signed_numeric;
   rewrite generator_table_row_numeric by exact Index;reflexivity.
Qed.
