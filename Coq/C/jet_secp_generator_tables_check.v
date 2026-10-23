(** Complete signed-table checker and its connection to the fixed literal
    Word16 programs. The closed certificates are a separate obligation. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_toZ C.jet_secp_generate_literal C.jet_secp_generate_numeric
 C.jet_secp_generator_bits C.jet_secp_generator_prefix C.jet_secp_generator_rows
 C.jet_secp_generator_table_samples C.jet_secp_generator_fast_points C.jet_secp_generator_fast_check.
Require Import C.jet_secp_table_index C.jet_secp_wnaf_literal_mask C.jet_secp_generator_digit_shape.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition generator_tables_seed high (neg : bool) :=
 generator_bits_fast (literal_affine_denote (literal_generator_base_word high)) [neg;neg].
Definition generator_tables_check high neg :=
 generator_prefix_fast_check 13 (literal_affine_denote (literal_generator_base_word high))
   (generator_tables_seed high neg) (generator_table_signed_rows high neg).

Lemma generator_tables_seed_literal high neg : generator_tables_seed high neg=
 literal_generate_bits (literal_affine_denote (literal_generator_base_word high)) [neg;neg].
Proof. apply generator_bits_fast_matches. Qed.
Theorem generator_tables_check_values high neg : generator_tables_check high neg=Some [] ->
 generator_table_signed_rows high neg=generator_prefix_values 13
   (literal_affine_denote (literal_generator_base_word high))
   (literal_generate_bits (literal_affine_denote (literal_generator_base_word high)) [neg;neg]).
Proof.
 unfold generator_tables_check;intro Check;apply generator_prefix_fast_check_consumed in Check.
 rewrite generator_tables_seed_literal in Check;exact Check.
Qed.
Lemma literal_generate_bits_append base prefix suffix : prefix<>[] ->
 literal_generate_bits base (prefix++suffix)=
 fold_left (literal_generate_bit base) suffix (literal_generate_bits base prefix).
Proof.
 destruct prefix as [|sign tail];[contradiction|].
 intro Nonempty;cbn [app literal_generate_bits];rewrite fold_left_app;reflexivity.
Qed.

Theorem generator_tables_check_numeric high neg (word : Ty.tySem (Word 4)) bits :
 generator_tables_check high neg=Some [] -> length bits=13%nat ->
 literal_generator_bits 4 word=[neg;neg]++bits++[true] ->
 literal_generate_small_fast high word=
 nth (generator_path_index bits) (generator_table_signed_rows high neg) (0,0).
Proof.
 intros Check Length Bits.
 unfold literal_generate_small_fast;rewrite literal_generate_signed_numeric_bits,Bits.
 rewrite (literal_generate_bits_append _ [neg;neg] (bits++[true])) by discriminate.
 rewrite fold_left_app;cbn [fold_left].
 rewrite (generator_tables_check_values high neg Check).
 symmetry;apply generator_prefix_values_lookup;exact Length.
Qed.
Theorem generator_tables_check_literal high neg (word : Ty.tySem (Word 4)) bits :
 generator_tables_check high neg=Some [] -> length bits=13%nat ->
 literal_generator_bits 4 word=[neg;neg]++bits++[true] ->
 let expected:=nth (generator_path_index bits) (generator_table_signed_rows high neg) (0,0) in
 @literal_generate_small high Alg.CoreFunSem word=
 (@fromZ (WordToZ 8) (fst expected),@fromZ (WordToZ 8) (snd expected)).
Proof.
 intros Check Length Bits;cbn zeta.
 rewrite literal_generate_small_fast_word,(generator_tables_check_numeric _ _ _ _ Check Length Bits);reflexivity.
Qed.

Theorem generator_table_signed_rows_lookup high (neg : bool) index default : Z.of_nat index<8192 ->
 nth index (generator_table_signed_rows high neg) default=
 generator_entry_signed_numeric high (if neg then Z.to_nat (8191-Z.of_nat index) else index) neg.
Proof.
 intro Index;pose proof (proj2 (generator_table_rows_exact high)) as RowsLength.
 assert (InRange : (index<length (generator_table_rows high))%nat) by lia.
 unfold generator_table_signed_rows;destruct neg.
 - rewrite rev_nth by (rewrite map_length;exact InRange).
   rewrite map_length.
   assert (Reverse : (length (generator_table_rows high)-S index)%nat=Z.to_nat (8191-Z.of_nat index)).
   { apply Nat2Z.inj;rewrite Nat2Z.inj_sub by lia.
     rewrite RowsLength,Nat2Z.inj_succ,Z2Nat.id by lia;lia. }
   rewrite Reverse.
   rewrite (@nth_indep (Z*Z) _ _ default (generator_row_signed_numeric [] true))
     by (rewrite map_length;rewrite <-Reverse;lia).
   rewrite (@map_nth _ _ (fun row=>generator_row_signed_numeric row true)
     (generator_table_rows high) [] (Z.to_nat (8191-Z.of_nat index))).
   apply generator_table_row_signed_numeric;rewrite Z2Nat.id by lia;lia.
 - rewrite (@nth_indep (Z*Z) _ _ default (generator_row_signed_numeric [] false)) by (rewrite map_length;exact InRange).
   rewrite (@map_nth _ _ (fun row=>generator_row_signed_numeric row false) (generator_table_rows high) [] index).
   apply generator_table_row_signed_numeric;exact Index.
Qed.

Lemma generator_signed_table_index (neg : bool) k n : 0<=k<8192 ->
 n=(if neg then 2*k-16383 else 2*k+1) ->
 table_storage_index n=(if neg then 8191-k else k) /\ negb (0<?n)=neg.
Proof.
 intros K Value;subst n;destruct neg;unfold table_storage_index.
 - rewrite Z.abs_neq by lia.
   replace (- (2*k-16383)-1) with ((8191-k)*2) by ring.
   rewrite Z.div_mul by lia.
   rewrite (proj2 (Z.ltb_ge 0 (2*k-16383))) by lia;split;reflexivity.
 - rewrite Z.abs_eq by lia.
   replace (2*k+1-1) with (k*2) by ring;rewrite Z.div_mul by lia.
   rewrite (proj2 (Z.ltb_lt 0 (2*k+1))) by lia;split;reflexivity.
Qed.

Theorem generator_tables_match_digit high (word : Ty.tySem (Word 4)) :
 (forall neg,generator_tables_check high neg=Some []) ->
 literal_wnaf_signed16 word mod 2=1 -> -16384<literal_wnaf_signed16 word<16384 ->
 let n:=literal_wnaf_signed16 word in
 let expected:=generator_entry_signed_numeric high (Z.to_nat (table_storage_index n)) (negb (0<?n)) in
 @literal_generate_small high Alg.CoreFunSem word=
 (@fromZ (WordToZ 8) (fst expected),@fromZ (WordToZ 8) (snd expected)).
Proof.
 intros Checked Odd Range;cbn zeta.
 destruct (generator_wnaf_digit_decomposition word Odd Range) as (neg & bits & Length & Bits & Value).
 pose proof (generator_path_index_bound bits) as Bound;rewrite Length in Bound.
 apply Nat2Z.inj_lt in Bound;rewrite Nat2Z.inj_pow in Bound.
 change (Z.of_nat (generator_path_index bits)<8192) in Bound.
 assert (K : 0<=Z.of_nat (generator_path_index bits)<8192) by
   (pose proof (Nat2Z.is_nonneg (generator_path_index bits));lia).
 pose proof (generator_tables_check_literal high neg word bits (Checked neg) Length Bits) as Result.
 rewrite generator_table_signed_rows_lookup in Result by exact Bound.
 destruct (generator_signed_table_index neg _ _ K Value) as [Index Sign].
 rewrite Sign,Index;destruct neg;[exact Result|rewrite Nat2Z.id;exact Result].
Qed.
