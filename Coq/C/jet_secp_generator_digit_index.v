(** Recover raw literal digits from the already-proved C wNAF array,
    including exact integer loads and the prefix omitted by C's return. *)
From Coq Require Import ZArith Lia List.
From compcert Require Import Integers AST Memory Values.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_sx_mem C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_array C.jet_secp_wnaf_literal_values
 C.jet_secp_wnaf_loop C.jet_secp_wnaf_return_length C.jet_secp_generator_program.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wnaf_literal_digit_at (word : Ty.tySem (Word 7)) (i : Z) : Ty.tySem literal_wnaf_digit :=
 nth (Z.to_nat i) (rev (literal_wnaf15_digits (Bit.zero,word))) (inl tt).

Theorem wnaf_literal_digit_at_valid word i : 0<=i<129 -> wnaf_literal_valid (wnaf_literal_digit_at word i).
Proof.
 intro Range;assert (Index : (Z.to_nat i<129)%nat) by
   (apply Nat2Z.inj_lt;rewrite Z2Nat.id by lia;lia).
 unfold wnaf_literal_digit_at;rewrite rev_nth by (rewrite literal_wnaf15_digits_length;exact Index).
 apply (proj1 (Forall_nth _ _) (literal_wnaf15_values word)).
 rewrite !literal_wnaf15_digits_length;lia.
Qed.

Lemma generator_nth_map_seq (f : nat->Z) count i : (i<count)%nat ->
 nth i (map f (seq 0 count)) 0=f i.
Proof.
 intro Index;rewrite (@nth_indep Z (map f (seq 0 count)) i 0 (f 0%nat)) by
   (rewrite map_length,seq_length;exact Index).
 rewrite map_nth,seq_nth by exact Index;reflexivity.
Qed.

Theorem wnaf_literal_digit_at_value word digits i : 0<=i<129 ->
 map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,word))=
   rev (map (fun j=>digits (Z.of_nat j)) (seq 0 129)) ->
 wnaf_literal_value (wnaf_literal_digit_at word i)=digits i.
Proof.
 intros Range Literal;assert (Index : (Z.to_nat i<129)%nat) by
   (apply Nat2Z.inj_lt;rewrite Z2Nat.id by lia;lia).
 pose proof (f_equal (fun xs : list Z=>nth (Z.to_nat i) (rev xs) 0) Literal) as At.
 cbn beta in At.
 rewrite rev_involutive,generator_nth_map_seq in At by exact Index.
 rewrite Z2Nat.id in At by lia.
 transitivity (nth (Z.to_nat i) (rev (map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,word)))) 0).
 - symmetry;rewrite <-map_rev;unfold wnaf_literal_digit_at.
   exact (map_nth wnaf_literal_value (rev (literal_wnaf15_digits (Bit.zero,word))) (inl tt) (Z.to_nat i)).
 - exact At.
Qed.

Theorem wnaf_literal_array_for_generator m b base word digits last :
 wnaf_array_state m b base 129 15 1 129 last digits ->
 map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,word))=
   rev (map (fun j=>digits (Z.of_nat j)) (seq 0 129)) ->
 0<=last+1<=129 /\ forall i,0<=i<129 ->
 wnaf_literal_valid (wnaf_literal_digit_at word i) /\
 Mem.load Mint32 m b (base+4*i)=Some (Vint (Int.repr (wnaf_literal_value (wnaf_literal_digit_at word i)))) /\
 (last+1<=i -> wnaf_literal_digit_at word i=inl tt).
Proof.
 intros Array Literal;pose proof (wnaf_array_last _ _ _ _ _ _ _ _ _ Array) as Last.
 split;[destruct Last as [Bound _];lia|].
 intros i Range;pose proof (wnaf_literal_digit_at_valid word i Range) as Valid;split;[exact Valid|].
 pose proof (wnaf_literal_digit_at_value word digits i Range Literal) as Value;split.
 - rewrite Value;pose proof (wnaf_array_load _ _ _ _ _ _ _ _ _ Array i Range) as Load.
   rewrite Z.mul_1_l in Load;exact Load.
 - intro Above;apply (proj1 (wnaf_literal_zero_iff _ Valid));rewrite Value.
   eapply wnaf_above_last_zero;[exact Last|lia|exact Range].
Qed.

Lemma generator_enumerate_nth A (xs : list A) d :
 map (fun i=>nth i xs d) (seq 0 (length xs))=xs.
Proof.
 induction xs as [|x xs IH];[reflexivity|].
 cbn [length seq map];rewrite <-seq_shift,map_map.
 change (x::map (fun i=>nth i xs d) (seq 0 (length xs))=x::xs).
 rewrite IH;reflexivity.
Qed.

Lemma generator_combine_map A B C (f : A->B) (g : A->C) xs :
 combine (map f xs) (map g xs)=map (fun x=>(f x,g x)) xs.
Proof. induction xs;cbn [map combine];[reflexivity|rewrite IHxs;reflexivity]. Qed.

Lemma generator_combine_rev A B (xs : list A) (ys : list B) : length xs=length ys ->
 combine (rev xs) (rev ys)=rev (combine xs ys).
Proof.
 revert ys;induction xs as [|x xs IH];intros [|y ys] Length;
   cbn in Length|-*;try discriminate;[reflexivity|].
 rewrite generator_combine_app by (rewrite !rev_length;lia).
 rewrite IH by lia;reflexivity.
Qed.

Theorem generator_pair_enumerate_reverse A B (xs : list A) (ys : list B) da db n :
 length xs=n -> length ys=n ->
 map (fun j=>(nth j (rev xs) da,nth j (rev ys) db)) (rev (seq 0 n))=combine xs ys.
Proof.
 intros LX LY;rewrite map_rev.
 pose proof (generator_enumerate_nth _ (rev xs) da) as EX;rewrite rev_length,LX in EX.
 pose proof (generator_enumerate_nth _ (rev ys) db) as EY;rewrite rev_length,LY in EY.
 rewrite <-(generator_combine_map _ _ _ (fun j=>nth j (rev xs) da) (fun j=>nth j (rev ys) db) (seq 0 n)),EX,EY.
 rewrite generator_combine_rev by lia;rewrite rev_involutive;reflexivity.
Qed.

Theorem wnaf_literal_digit_at_pair word1 word128 :
 map (fun j=>(wnaf_literal_digit_at word1 (Z.of_nat j),wnaf_literal_digit_at word128 (Z.of_nat j)))
   (rev (seq 0 129))=
 combine (literal_wnaf15_digits (Bit.zero,word1)) (literal_wnaf15_digits (Bit.zero,word128)).
Proof.
 transitivity (map (fun j=>
   (nth j (rev (literal_wnaf15_digits (Bit.zero,word1))) (inl tt),
    nth j (rev (literal_wnaf15_digits (Bit.zero,word128))) (inl tt))) (rev (seq 0 129))).
 - apply map_ext;intro j;unfold wnaf_literal_digit_at;rewrite !Nat2Z.id;reflexivity.
 - apply generator_pair_enumerate_reverse;apply literal_wnaf15_digits_length.
Qed.

Theorem wnaf_literal_digit_at_vectors word1 word128 :
 map (fun j=>(wnaf_literal_digit_at word1 (Z.of_nat j),wnaf_literal_digit_at word128 (Z.of_nat j)))
   (rev (seq 0 129))=
 let '(head1,tail1):=@literal_wnaf15 Alg.CoreFunSem (Bit.zero,word1) in
 let '(head128,tail128):=@literal_wnaf15 Alg.CoreFunSem (Bit.zero,word128) in
 (head1,head128)::combine (literal_wnaf_flatten 7 tail1) (literal_wnaf_flatten 7 tail128).
Proof.
 rewrite wnaf_literal_digit_at_pair;unfold literal_wnaf15_digits.
 destruct (@literal_wnaf15 Alg.CoreFunSem (Bit.zero,word1)),(@literal_wnaf15 Alg.CoreFunSem (Bit.zero,word128));reflexivity.
Qed.

Theorem wnaf_129_array_lframe m mf b base w sign bit last digits P :
 wnaf_array_state m b base 129 w sign bit last digits ->
 lframe P m mf -> (forall pos,P b pos) ->
 wnaf_array_state mf b base 129 w sign bit last digits.
Proof.
 intros Array Frame Outside.
 assert (Valid : Mem.valid_block m b).
 { eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
     [exact (wnaf_array_access _ _ _ _ _ _ _ _ _ Array 0 ltac:(lia))|constructor]. }
 constructor.
 - intros i Range;destruct (wnaf_array_access _ _ _ _ _ _ _ _ _ Array i Range) as [Access Align];split;[|exact Align].
   intros pos Bounds;apply (proj1 (proj2 Frame));[exact Valid|apply Outside|apply Access;exact Bounds].
 - intros i Range;rewrite (proj1 Frame Mint32 b (base+4*i) Valid ltac:(intros;apply Outside)).
   exact (wnaf_array_load _ _ _ _ _ _ _ _ _ Array i Range).
 - exact (wnaf_array_suffix _ _ _ _ _ _ _ _ _ Array).
 - exact (wnaf_array_digits _ _ _ _ _ _ _ _ _ Array).
 - exact (wnaf_array_last _ _ _ _ _ _ _ _ _ Array).
Qed.
