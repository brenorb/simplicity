(** Quantitative termination of the remainder pair in the literal EEA run. *)
From Coq Require Import ZArith Lia.
Require Import C.jet_secp_eea_numeric C.jet_secp_eea_fast C.jet_division_value.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition eea_remainders (s : ((Z*Z)*Z)*((Z*Z)*Z)) := (snd (fst s),snd (snd s)).
Definition eea_pair_step (v : Z*Z) :=
 let '(c,f):=v in if f<?c then (c mod f,f) else (c,f mod c).
Definition eea_pair_min (v : Z*Z) := Z.min (fst v) (snd v).

Lemma eea_remainder_value a b : division_numeric Datatypes.true a b=a mod b.
Proof.
 unfold division_numeric;destruct (Z.eqb_spec b 0);[subst b;rewrite Zmod_0_r;reflexivity|reflexivity].
Qed.
Lemma eea_remainders_step modulus s :
 eea_remainders (eea_step_numeric modulus s)=eea_pair_step (eea_remainders s).
Proof.
 destruct s as [[[a b] c] [[d e] f]];unfold eea_step_numeric,eea_remainders,eea_pair_step;
   cbn [fst snd];destruct (f<?c);unfold eea_row_step_numeric;
   cbn [fst snd];rewrite eea_remainder_value;reflexivity.
Qed.
Lemma eea_pair_step_nonnegative c f : 0<=c -> 0<=f ->
 0<=fst (eea_pair_step (c,f)) /\ 0<=snd (eea_pair_step (c,f)).
Proof.
 intros C F;unfold eea_pair_step;destruct (f<?c);cbn [fst snd];split;try assumption.
 - destruct (Z.eq_dec f 0);[subst f;rewrite Zmod_0_r;exact C|].
   pose proof (Z.mod_pos_bound c f ltac:(lia));lia.
 - destruct (Z.eq_dec c 0);[subst c;rewrite Zmod_0_r;exact F|].
   pose proof (Z.mod_pos_bound f c ltac:(lia));lia.
Qed.

Lemma eea_pair_step_zero c f : 0<=c -> 0<=f ->
 eea_pair_min (c,f)=0 -> eea_pair_step (c,f)=(c,f).
Proof.
 intros C F Zero;unfold eea_pair_min in Zero;cbn [fst snd] in Zero.
 assert (c=0 \/ f=0) by (destruct (Z_le_dec c f);[rewrite Z.min_l in Zero by lia|rewrite Z.min_r in Zero by lia];lia).
 destruct H as [ZeroC|ZeroF];unfold eea_pair_step.
 - subst c;rewrite (proj2 (Z.ltb_ge f 0)) by lia;rewrite Zmod_0_r;reflexivity.
 - subst f;destruct (Z.ltb_spec 0 c).
   + rewrite Zmod_0_r;reflexivity.
   + assert (c=0) by lia;subst c;reflexivity.
Qed.

Lemma eea_pair_step_positive c f : 0<c -> 0<f ->
 eea_pair_min (eea_pair_step (c,f))=Z.max c f mod Z.min c f /\
 Z.max (fst (eea_pair_step (c,f))) (snd (eea_pair_step (c,f)))=Z.min c f.
Proof.
 intros C F;unfold eea_pair_step;destruct (Z.ltb_spec f c);unfold eea_pair_min;cbn [fst snd].
 - pose proof (Z.mod_pos_bound c f F) as Rem.
   rewrite (Z.min_r c f),(Z.max_l c f),(Z.min_l (c mod f) f),(Z.max_r (c mod f) f) by lia.
   split;reflexivity.
 - pose proof (Z.mod_pos_bound f c C) as Rem.
   rewrite (Z.min_l c f),(Z.max_r c f),(Z.min_r c (f mod c)),(Z.max_l c (f mod c)) by lia.
   split;reflexivity.
Qed.

Lemma eea_small_mod_halves b r : 0<r<b -> 2*(b mod r)<=b.
Proof.
 intros Range;pose proof (Z.mod_pos_bound b r ltac:(lia)) as Rem.
 destruct (Z_le_dec (2*r) b);[lia|].
 assert (Small : b mod r=b-r).
 { symmetry;apply (Z.mod_unique b r 1 (b-r));[left;lia|ring]. }
 rewrite Small;lia.
Qed.

Theorem eea_pair_two_halves c f : 0<=c -> 0<=f ->
 2*eea_pair_min (eea_pair_step (eea_pair_step (c,f)))<=eea_pair_min (c,f).
Proof.
 intros C F;destruct (Z.eq_dec (eea_pair_min (c,f)) 0) as [Zero|Nonzero].
 - rewrite (eea_pair_step_zero c f C F Zero).
   rewrite (eea_pair_step_zero c f C F Zero),Zero;lia.
 - assert (CP : 0<c) by (unfold eea_pair_min in Nonzero;cbn [fst snd] in Nonzero;
     destruct (Z_le_dec c f);[rewrite Z.min_l in Nonzero by lia|rewrite Z.min_r in Nonzero by lia];lia).
   assert (FP : 0<f) by (unfold eea_pair_min in Nonzero;cbn [fst snd] in Nonzero;
     destruct (Z_le_dec c f);[rewrite Z.min_l in Nonzero by lia|rewrite Z.min_r in Nonzero by lia];lia).
   pose proof (eea_pair_step_positive c f CP FP) as [Min1 Max1].
   pose proof (eea_pair_step_nonnegative c f C F) as [C1 F1].
   destruct (eea_pair_step (c,f)) as [c1 f1] eqn:Step;cbn [fst snd] in Max1,C1,F1.
   destruct (Z.eq_dec (eea_pair_min (c1,f1)) 0) as [Zero|Nonzero1].
   + rewrite (eea_pair_step_zero c1 f1 C1 F1 Zero),Zero.
     unfold eea_pair_min;cbn [fst snd];pose proof (Z.min_glb c f 0 C F);lia.
   + assert (C1P : 0<c1) by (unfold eea_pair_min in Nonzero1;cbn [fst snd] in Nonzero1;
       destruct (Z_le_dec c1 f1);[rewrite Z.min_l in Nonzero1 by lia|rewrite Z.min_r in Nonzero1 by lia];lia).
     assert (F1P : 0<f1) by (unfold eea_pair_min in Nonzero1;cbn [fst snd] in Nonzero1;
       destruct (Z_le_dec c1 f1);[rewrite Z.min_l in Nonzero1 by lia|rewrite Z.min_r in Nonzero1 by lia];lia).
     rewrite (proj1 (eea_pair_step_positive c1 f1 C1P F1P)),Max1.
     apply eea_small_mod_halves.
     split;[apply Z.min_glb_lt;assumption|].
     unfold eea_pair_min in Min1;cbn [fst snd] in Min1;rewrite Min1.
     apply Z.mod_pos_bound;apply Z.min_glb_lt;assumption.
Qed.

Definition eea_remainders_nonnegative s := 0<=fst (eea_remainders s) /\ 0<=snd (eea_remainders s).
Definition eea_minimum s := eea_pair_min (eea_remainders s).
Definition eea_remainder_gcd s := Z.gcd (fst (eea_remainders s)) (snd (eea_remainders s)).

Lemma eea_remainders_step_nonnegative modulus s : eea_remainders_nonnegative s ->
 eea_remainders_nonnegative (eea_step_numeric modulus s).
Proof.
 unfold eea_remainders_nonnegative;rewrite eea_remainders_step.
 destruct (eea_remainders s) as [c f];cbn [fst snd];intros [C F];apply eea_pair_step_nonnegative;assumption.
Qed.
Lemma eea_remainders_run_nonnegative modulus count s : eea_remainders_nonnegative s ->
 eea_remainders_nonnegative (eea_run_numeric modulus count s).
Proof.
 revert s;induction count as [|count IH];intros s Nonnegative;[exact Nonnegative|].
 cbn [eea_run_numeric];apply IH;apply eea_remainders_step_nonnegative;assumption.
Qed.

Lemma eea_minimum_two_halves modulus s : eea_remainders_nonnegative s ->
 2*eea_minimum (eea_step_numeric modulus (eea_step_numeric modulus s))<=eea_minimum s.
Proof.
 unfold eea_minimum;rewrite !eea_remainders_step.
 unfold eea_remainders_nonnegative;destruct (eea_remainders s) as [c f];
   cbn [fst snd];intros [C F];apply eea_pair_two_halves;assumption.
Qed.

Theorem eea_minimum_run_bound modulus bits s : eea_remainders_nonnegative s ->
 2^Z.of_nat bits*eea_minimum (eea_run_numeric modulus (2*bits) s)<=eea_minimum s.
Proof.
 revert s;induction bits as [|bits IH];intros s Nonnegative.
 - cbn [Nat.mul eea_run_numeric];change (1*eea_minimum s<=eea_minimum s);lia.
 - replace (2*S bits)%nat with (S (S (2*bits))) by lia.
   cbn [eea_run_numeric].
   pose proof (eea_minimum_two_halves modulus s Nonnegative) as Half.
   pose proof (eea_remainders_step_nonnegative modulus s Nonnegative) as Positive1.
   pose proof (eea_remainders_step_nonnegative modulus _ Positive1) as Positive2.
   pose proof (IH _ Positive2) as Bound.
   rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia;nia.
Qed.

Lemma eea_minimum_finished s : eea_remainders_nonnegative s ->
 eea_minimum s=0 -> eea_finished s=Datatypes.true.
Proof.
 destruct s as [[[a b] c] [[d e] f]];
   unfold eea_remainders_nonnegative,eea_minimum,eea_pair_min,eea_remainders,eea_finished;
   cbn [fst snd];intros [C F] Zero.
 apply Bool.orb_true_iff;destruct (Z_le_dec c f).
 - left;apply Z.eqb_eq;rewrite Z.min_l in Zero by lia;exact Zero.
 - right;apply Z.eqb_eq;rewrite Z.min_r in Zero by lia;exact Zero.
Qed.

Theorem eea_run_finishes modulus bits s : eea_remainders_nonnegative s ->
 eea_minimum s<2^Z.of_nat bits -> eea_finished (eea_run_numeric modulus (2*bits) s)=Datatypes.true.
Proof.
 intros Nonnegative Initial.
 pose proof (eea_minimum_run_bound modulus bits s Nonnegative) as Bound.
 pose proof (eea_remainders_run_nonnegative modulus (2*bits) s Nonnegative) as Final.
 apply eea_minimum_finished;[exact Final|].
 assert (0<=eea_minimum (eea_run_numeric modulus (2*bits) s)) as Lower.
 { unfold eea_minimum,eea_pair_min;apply Z.min_glb;apply Final. }
 assert (0<2^Z.of_nat bits) by (apply Z.pow_pos_nonneg;lia).
 nia.
Qed.

Lemma eea_pair_step_gcd c f :
 Z.gcd (fst (eea_pair_step (c,f))) (snd (eea_pair_step (c,f)))=Z.gcd c f.
Proof.
 unfold eea_pair_step;destruct (f<?c);cbn [fst snd].
 - destruct (Z.eq_dec f 0) as [Zero|Nonzero];[subst f;rewrite Zmod_0_r;reflexivity|].
   rewrite Z.gcd_mod by exact Nonzero;apply Z.gcd_comm.
 - destruct (Z.eq_dec c 0) as [Zero|Nonzero];[subst c;rewrite Zmod_0_r;reflexivity|].
   rewrite (Z.gcd_comm c (f mod c)),Z.gcd_mod by exact Nonzero;reflexivity.
Qed.
Lemma eea_remainder_step_gcd modulus s :
 eea_remainder_gcd (eea_step_numeric modulus s)=eea_remainder_gcd s.
Proof.
 unfold eea_remainder_gcd;rewrite eea_remainders_step.
 destruct (eea_remainders s) as [c f];apply eea_pair_step_gcd.
Qed.
Theorem eea_remainder_run_gcd modulus count s :
 eea_remainder_gcd (eea_run_numeric modulus count s)=eea_remainder_gcd s.
Proof.
 revert s;induction count as [|count IH];intro s;[reflexivity|].
 cbn [eea_run_numeric];rewrite IH;apply eea_remainder_step_gcd.
Qed.
