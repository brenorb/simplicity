(** Recover literal window-5 digits from the original signed C arrays. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Values.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf5_literal
 C.jet_secp_wnaf5_signed_array C.jet_secp_wnaf_loop C.jet_secp_wnaf_return_length
 C.jet_secp_generator_digit_index C.jet_secp_strauss_digit_guard.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition strauss_wnaf5_digit_at (state:Ty.tySem literal_wnaf_state) (i:Z) : Ty.tySem literal_wnaf5_digit :=
 nth (Z.to_nat i) (rev (literal_wnaf5_digits state)) (inl tt).

Lemma strauss_wnaf5_zero_iff (digit:Ty.tySem literal_wnaf5_digit) :
 wnaf5_literal_value digit=0 <-> digit=inl tt.
Proof.
 destruct digit as [[]|nib];[split;reflexivity|].
 split;[|discriminate].
 intro Zero;exfalso;apply (strauss_wnaf5_int_nonzero nib).
 change (Int.repr (wnaf5_literal_value (inr nib))=Int.zero).
 exact (f_equal Int.repr Zero).
Qed.

Theorem strauss_wnaf5_digit_at_value state digits sign i : 0<=i<129 ->
 map wnaf5_literal_value (literal_wnaf5_digits state)=
 rev (map (fun j=>sign*digits (Z.of_nat j)) (seq 0 129)) ->
 wnaf5_literal_value (strauss_wnaf5_digit_at state i)=sign*digits i.
Proof.
 intros Range Literal;assert (Index:(Z.to_nat i<129)%nat) by
  (apply Nat2Z.inj_lt;rewrite Z2Nat.id by lia;lia).
 pose proof (f_equal (fun xs:list Z=>nth (Z.to_nat i) (rev xs) 0) Literal) as At.
 cbn beta in At;rewrite rev_involutive,generator_nth_map_seq in At by exact Index.
 rewrite Z2Nat.id in At by lia.
 transitivity (nth (Z.to_nat i) (rev (map wnaf5_literal_value (literal_wnaf5_digits state))) 0).
 - symmetry;rewrite <-map_rev;unfold strauss_wnaf5_digit_at.
   exact (map_nth wnaf5_literal_value (rev (literal_wnaf5_digits state)) (inl tt) (Z.to_nat i)).
 - exact At.
Qed.

Theorem strauss_wnaf5_array_for_loop m b base state digits sign last :
 wnaf_array_state m b base 129 5 sign 129 last digits ->
 map wnaf5_literal_value (literal_wnaf5_digits state)=
 rev (map (fun j=>sign*digits (Z.of_nat j)) (seq 0 129)) ->
 0<=last+1<=129 /\ forall i,0<=i<129 ->
 Mem.load Mint32 m b (base+4*i)=Some (Vint (Int.repr (wnaf5_literal_value (strauss_wnaf5_digit_at state i)))) /\
 (last+1<=i -> strauss_wnaf5_digit_at state i=inl tt).
Proof.
 intros Array Literal;pose proof (wnaf_array_last _ _ _ _ _ _ _ _ _ Array) as Last.
 split;[destruct Last as [Bound _];lia|].
 intros i Range;pose proof (strauss_wnaf5_digit_at_value state digits sign i Range Literal) as Value;split.
 - rewrite Value;exact (wnaf_array_load _ _ _ _ _ _ _ _ _ Array i Range).
 - intro Above;apply (proj1 (strauss_wnaf5_zero_iff _));rewrite Value.
   assert (DigitZero:digits i=0) by (eapply wnaf_above_last_zero;[exact Last|lia|exact Range]).
   rewrite DigitZero,Z.mul_0_r;reflexivity.
Qed.

Theorem strauss_wnaf5_digit_at_vectors state1 statelam :
 map (fun j=>(strauss_wnaf5_digit_at state1 (Z.of_nat j),strauss_wnaf5_digit_at statelam (Z.of_nat j)))
  (rev (seq 0 129))=
 let '(h1,t1):=@literal_wnaf5 Simplicity.Alg.CoreFunSem state1 in
 let '(hlam,tlam):=@literal_wnaf5 Simplicity.Alg.CoreFunSem statelam in
 (h1,hlam)::combine (literal_wnaf5_flatten 7 t1) (literal_wnaf5_flatten 7 tlam).
Proof.
 transitivity (combine (literal_wnaf5_digits state1) (literal_wnaf5_digits statelam)).
 - transitivity (map (fun j=>
   (nth j (rev (literal_wnaf5_digits state1)) (inl tt),
    nth j (rev (literal_wnaf5_digits statelam)) (inl tt))) (rev (seq 0 129))).
   + apply map_ext;intro j;unfold strauss_wnaf5_digit_at;rewrite !Nat2Z.id;reflexivity.
   + apply generator_pair_enumerate_reverse;apply literal_wnaf5_digits_length.
 - unfold literal_wnaf5_digits.
   destruct (@literal_wnaf5 Simplicity.Alg.CoreFunSem state1),
    (@literal_wnaf5 Simplicity.Alg.CoreFunSem statelam);reflexivity.
Qed.
