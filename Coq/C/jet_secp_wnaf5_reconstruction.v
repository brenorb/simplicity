(** Reconstruction of the exact signed window-5 digit stream. *)
From Coq Require Import ZArith Lia List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_literal_next C.jet_secp_wnaf5_signed
 C.jet_secp_wnaf5_signed_windows C.jet_secp_wnaf5_signed_array C.jet_secp_wnaf_literal_signed
 C.jet_secp_wnaf_literal C.jet_secp_wnaf_digit C.jet_predicate_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_wnaf5_step literal_wnaf_signed_value.
Lemma secp_wnaf5_low_bit (sb:Ty.tySem Bit) (word:Ty.tySem (Word 7)):
 literal_wnaf_signed_value sb word mod 2=
 @toZ BitToZ (@Word.rightmost Bit 7 Alg.CoreFunSem word).
Proof.
 pose proof (Z.mod_pos_bound (literal_wnaf_signed_value sb word) 2 ltac:(lia)) as Range.
 destruct (Z.eq_dec (literal_wnaf_signed_value sb word mod 2) 0) as [Even|NotEven].
 - rewrite (literal_wnaf_signed_even sb word Even);exact Even.
 - assert (Odd:literal_wnaf_signed_value sb word mod 2=1) by lia.
   rewrite (literal_wnaf_signed_odd sb word Odd);exact Odd.
Qed.
Theorem secp_wnaf5_step_balance (sb:Ty.tySem Bit) (word:Ty.tySem (Word 7)):
 let '(next,digit):=@literal_wnaf5_step Alg.CoreFunSem (sb,word) in
 literal_wnaf_signed_value sb word=
  2*literal_wnaf_signed_value (fst next) (snd next)+wnaf5_literal_value digit.
Proof.
 pose proof (secp_wnaf5_low_bit sb word) as Parity.
 pose proof (Z.div_mod (literal_wnaf_signed_value sb word) 2 ltac:(lia)) as Division.
 destruct (@Word.rightmost Bit 7 Alg.CoreFunSem word) as [u|u] eqn:Low;destruct u.
 - change (literal_wnaf_signed_value sb word mod 2=0) in Parity.
   destruct (literal_wnaf5_even_signed sb word Low) as [Step Next].
   refine (eq_ind_r (fun result=>let '(state,digit):=result in
    literal_wnaf_signed_value sb word=2*literal_wnaf_signed_value (fst state) (snd state)+wnaf5_literal_value digit) _ Step).
   cbn [fst snd wnaf5_literal_value];rewrite Next;lia.
 - change (literal_wnaf_signed_value sb word mod 2=1) in Parity.
   destruct (literal_wnaf5_odd_signed sb word Low) as (sbn & next & nib & Step & Digit & Next).
   refine (eq_ind_r (fun result=>let '(state,digit):=result in
    literal_wnaf_signed_value sb word=2*literal_wnaf_signed_value (fst state) (snd state)+wnaf5_literal_value digit) _ Step).
   cbn [fst snd wnaf5_literal_value];rewrite Next.
   assert (Quotient:(literal_wnaf_signed_value sb word-literal_wnaf5_value nib)/2=
    literal_wnaf_signed_value sb word/2-literal_wnaf_signed4 nib).
   { symmetry;apply Z.div_unique with (r:=0);[lia|unfold literal_wnaf5_value;lia]. }
   rewrite Quotient;unfold literal_wnaf5_value;lia.
Qed.
Definition secp_wnaf5_next (q:Z):=
 if q mod 2 =? 0 then q/2 else (q-wnaf_digit (q mod 32) 5)/2.
Lemma secp_wnaf5_small_digit q:-16<q<16 ->wnaf_digit (q mod 32) 5=q.
Proof.
 intro Small;change (q mod 32-q mod 32/16*32=q).
 destruct (Z_le_dec 0 q) as [Nonnegative|Negative].
 - rewrite Z.mod_small by lia;rewrite Z.div_small by lia;ring.
 - assert (Remainder:q mod 32=q+32).
   { symmetry;apply Z.mod_unique with (q:= -1);[left;lia|ring]. }
   rewrite Remainder.
   assert (Quotient:(q+32)/16=1).
   { symmetry;apply Z.div_unique with (r:=q+16);[left;lia|ring]. }
   rewrite Quotient;ring.
Qed.
Lemma secp_wnaf5_next_bound (k:nat) q:
 -2^Z.of_nat (S k)<=q<=2^Z.of_nat (S k) ->
 -2^Z.of_nat k<=secp_wnaf5_next q<=2^Z.of_nat k.
Proof.
 intro Bound;unfold secp_wnaf5_next;destruct (q mod 2 =? 0) eqn:Even.
 - assert (Power:2^Z.of_nat (S k)=2*2^Z.of_nat k).
   { rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia;ring. }
   rewrite Power in Bound;split;[apply Z.div_le_lower_bound|apply Z.div_le_upper_bound];lia.
 - apply Z.eqb_neq in Even.
   assert (Odd:q mod 2=1) by (pose proof (Z.mod_pos_bound q 2 ltac:(lia));lia).
   destruct (Nat.lt_ge_cases k 4) as [SmallK|LargeK].
   + assert (Power:2^Z.of_nat (S k)<=16).
     { change 16 with (2^4);apply Z.pow_le_mono_r;lia. }
     assert (Small:-16<q<16).
     { assert (Lower:q<> -16) by (intro E;rewrite E in Odd;discriminate).
       assert (Upper:q<>16) by (intro E;rewrite E in Odd;discriminate).
       lia. }
     rewrite secp_wnaf5_small_digit by exact Small;rewrite Z.sub_diag,Z.div_0_l by lia.
     pose proof (Z.pow_nonneg 2 (Z.of_nat k) ltac:(lia));lia.
   + set (u:=2^(Z.of_nat k-4)).
     assert (Power:2^Z.of_nat k=16*u).
     { unfold u;replace (Z.of_nat k) with (4+(Z.of_nat k-4)) at 1 by lia.
       rewrite Z.pow_add_r by lia;reflexivity. }
     assert (PowerNext:2^Z.of_nat (S k)=32*u).
     { rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia;rewrite Power;ring. }
     rewrite PowerNext in Bound.
     pose proof (Z.div_mod q 32 ltac:(lia)) as Division.
     pose proof (Z.mod_pos_bound q 32 ltac:(lia)) as Remainder.
     pose proof (Z.div_mod (q mod 32) 16 ltac:(lia)) as CarryDivision.
     pose proof (Z.mod_pos_bound (q mod 32) 16 ltac:(lia)) as CarryRemainder.
     assert (Carry:0<=q mod 32/16<=1).
     { lia. }
     assert (Quotient:(q-wnaf_digit (q mod 32) 5)/2=16*(q/32+q mod 32/16)).
     { change ((q-(q mod 32-q mod 32/16*32))/2=16*(q/32+q mod 32/16)).
       symmetry;apply Z.div_unique with (r:=0);[left;lia|nia]. }
     rewrite Quotient,Power;lia.
Qed.
Definition secp_wnaf5_state_value (state:Ty.tySem literal_wnaf_state):=
 literal_wnaf_signed_value (fst state) (snd state).
Lemma secp_wnaf5_step_next (state:Ty.tySem literal_wnaf_state):
 secp_wnaf5_state_value (fst (@literal_wnaf5_step Alg.CoreFunSem state))=
 secp_wnaf5_next (secp_wnaf5_state_value state).
Proof.
 destruct state as [sb word];unfold secp_wnaf5_state_value;cbn [fst snd].
 pose proof (secp_wnaf5_low_bit sb word) as Parity.
 unfold secp_wnaf5_next.
 destruct (@Word.rightmost Bit 7 Alg.CoreFunSem word) as [u|u] eqn:Low;destruct u.
 - change (literal_wnaf_signed_value sb word mod 2=0) in Parity;rewrite Parity.
   destruct (literal_wnaf5_even_signed sb word Low) as [Step Next].
   transitivity (literal_wnaf_signed_value sb (@literal_wnaf_shift128 Alg.CoreFunSem (sb,word))).
   + exact (f_equal (fun result=>literal_wnaf_signed_value (fst (fst result)) (snd (fst result))) Step).
   + exact Next.
 - change (literal_wnaf_signed_value sb word mod 2=1) in Parity;rewrite Parity.
   destruct (literal_wnaf5_odd_signed sb word Low) as (sbn & next & nib & Step & Digit & Next).
   transitivity (literal_wnaf_signed_value sbn next).
   + exact (f_equal (fun result=>literal_wnaf_signed_value (fst (fst result)) (snd (fst result))) Step).
   + rewrite Next,Digit;reflexivity.
Qed.
Lemma secp_wnaf5_run_succ_final count (state:Ty.tySem literal_wnaf_state):
 fst (literal_wnaf5_run (S count) state)=
 fst (literal_wnaf5_run count (fst (@literal_wnaf5_step Alg.CoreFunSem state))).
Proof.
 cbn [literal_wnaf5_run];destruct (@literal_wnaf5_step Alg.CoreFunSem state) as [next digit];cbn [fst].
 destruct (literal_wnaf5_run count next);reflexivity.
Qed.
Lemma secp_wnaf5_run_add_final n m (state:Ty.tySem literal_wnaf_state):
 fst (literal_wnaf5_run (n+m)%nat state)=
 fst (literal_wnaf5_run m (fst (literal_wnaf5_run n state))).
Proof.
 rewrite literal_wnaf5_run_add;destruct (literal_wnaf5_run n state) as [next left];cbn [fst].
 destruct (literal_wnaf5_run m next);reflexivity.
Qed.
Lemma secp_wnaf5_run_bound count (state:Ty.tySem literal_wnaf_state):
 -2^Z.of_nat count<=secp_wnaf5_state_value state<=2^Z.of_nat count ->
 -1<=secp_wnaf5_state_value (fst (literal_wnaf5_run count state))<=1.
Proof.
 revert state;induction count as [|count IH];intros state Bound.
 - exact Bound.
 - rewrite secp_wnaf5_run_succ_final;apply IH.
   rewrite secp_wnaf5_step_next;apply secp_wnaf5_next_bound;exact Bound.
Qed.
Lemma secp_wnaf5_next_small_zero q:-1<=q<=1 ->secp_wnaf5_next q=0.
Proof.
 intro Range;assert (Cases:q= -1 \/ q=0 \/ q=1) by lia.
 destruct Cases as [EqLeft | [EqZero | EqRight]];subst q;reflexivity.
Qed.
Theorem secp_wnaf5_run129_zero (state:Ty.tySem literal_wnaf_state):
 secp_wnaf5_state_value (fst (literal_wnaf5_run 129 state))=0.
Proof.
 change (secp_wnaf5_state_value (fst (literal_wnaf5_run (128+1)%nat state))=0).
 rewrite secp_wnaf5_run_add_final,secp_wnaf5_run_succ_final.
 change (secp_wnaf5_state_value
  (fst (@literal_wnaf5_step Alg.CoreFunSem (fst (literal_wnaf5_run 128 state))))=0).
 rewrite secp_wnaf5_step_next;apply secp_wnaf5_next_small_zero;apply secp_wnaf5_run_bound.
 destruct state as [sb word];pose proof (literal_wnaf_signed_range sb word) as Range.
 exact (conj (proj1 Range) (Z.lt_le_incl _ _ (proj2 Range))).
Qed.
Definition secp_wnaf5_digit_fold (a:Z) (digit:Ty.tySem literal_wnaf5_digit):=
 2*a+wnaf5_literal_value digit.
Lemma secp_wnaf5_run_balance count (state:Ty.tySem literal_wnaf_state):
 secp_wnaf5_state_value state=
 fold_left secp_wnaf5_digit_fold (snd (literal_wnaf5_run count state))
  (secp_wnaf5_state_value (fst (literal_wnaf5_run count state))).
Proof.
 revert state;induction count as [|count IH];intro state;[reflexivity|].
 destruct state as [sb word];pose proof (secp_wnaf5_step_balance sb word) as Balance.
 cbn [literal_wnaf5_run].
 destruct (@literal_wnaf5_step Alg.CoreFunSem (sb,word)) as [next digit] eqn:Step.
 pose proof (IH next) as Tail.
 destruct (literal_wnaf5_run count next) as [final digits] eqn:Rest.
 cbn [fst snd] in Tail|-*;rewrite fold_left_app;cbn [fold_left secp_wnaf5_digit_fold].
 rewrite <-Tail.
 exact Balance.
Qed.
Theorem secp_wnaf5_digits_reconstruct (state:Ty.tySem literal_wnaf_state):
 fold_left secp_wnaf5_digit_fold (literal_wnaf5_digits state) 0=secp_wnaf5_state_value state.
Proof.
 pose proof (secp_wnaf5_run_balance 129 state) as Balance.
 rewrite secp_wnaf5_run129_zero,literal_wnaf5_digits_order in Balance;symmetry;exact Balance.
Qed.
