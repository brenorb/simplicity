(** Termination preparation for production modular inversion. These phase
    lemmas use the existing integer divstep, without an exhaustive certificate. *)
From Coq Require Import ZArith Lia Arith.Wf_nat.
Require Import C.divstep.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma inv_stepN_start n st :
 fst (stepN (S n) st)=fst (stepN n (fst (step st))).
Proof.
 replace (S n) with (n+1)%nat by lia.
 rewrite stepN_app_fst;cbn [stepN];destruct (step st);reflexivity.
Qed.

Lemma inv_equal_g_step st : g st=f st ->
 (0<delta st -> g (fst (step st))=0) /\
 (delta st<=0 -> f (fst (step st))=f st /\
    g (fst (step st))=f st /\ delta (fst (step st))=1+delta st).
Proof.
 intro Equal;destruct (spec st);unfold INC;cbn in *;split;intros;try lia.
Qed.

Theorem inv_equal_g_terminates : forall st,g st=f st ->
 exists n,g (fst (stepN n st))=0.
Proof.
 intro start;pattern start.
 apply (well_founded_induction (well_founded_ltof State
   (fun st=>Z.to_nat (Z.max 0 (1-delta st))))).
 clear start;intros st IH Equal.
 destruct (inv_equal_g_step st Equal) as [Positive Nonpositive].
 destruct (Z_lt_dec 0 (delta st)) as [DP|DN].
 - exists 1%nat;cbn [stepN];destruct (step st) eqn:E;cbn in *;apply Positive;exact DP.
 - destruct (Nonpositive ltac:(lia)) as (F & G & D).
   assert (Less : ltof State (fun s=>Z.to_nat (Z.max 0 (1-delta s)))
      (fst (step st)) st).
   { unfold ltof;apply Nat2Z.inj_lt;rewrite !Z2Nat.id by lia;rewrite D;lia. }
   destruct (IH (fst (step st)) Less ltac:(congruence)) as [n Zero].
   exists (S n);rewrite inv_stepN_start;exact Zero.
Qed.

Lemma inv_even_values st : Zeven (g st) ->
 f (fst (step st))=f st /\ delta (fst (step st))=1+delta st /\
 g (fst (step st))=g st/2.
Proof.
 intro HE;unfold step;destruct (Zeven_odd_dec (g st)) as [E|O].
 - cbn;unfold INC;auto.
 - exfalso;exact (Zeven_not_Zodd _ HE O).
Qed.

Lemma inv_even_half_abs a : Zeven a -> a<>0 -> Z.abs (a/2)<Z.abs a.
Proof.
 intros Even NZ.
 pose proof (Zeven_div2 a Even) as E.
 set (h:=Z.div2 a) in *.
 assert (D : a/2=h).
 { rewrite E,Z.mul_comm,Z.div_mul by lia;reflexivity. }
 rewrite D,E,Z.abs_mul;change (Z.abs 2) with 2.
 assert (HN : h<>0) by (intro H;rewrite H in E;lia).
 pose proof (proj2 (Z.abs_pos h) HN);lia.
Qed.

Theorem inv_positive_odd_phase : forall st,0<delta st -> exists n,
 f (fst (stepN n st))=f st /\ 0<delta (fst (stepN n st)) /\
 (g (fst (stepN n st))=0 \/ Zodd (g (fst (stepN n st)))).
Proof.
 intro start;pattern start.
 apply (well_founded_induction (well_founded_ltof State (fun st=>Z.to_nat (Z.abs (g st))))).
 clear start.
 intros st IH Positive.
 destruct (Z.eq_dec (g st) 0) as [Zero|Nonzero].
 - exists 0%nat;split;[reflexivity|];split;[exact Positive|left;exact Zero].
 - destruct (Zeven_odd_dec (g st)) as [Even|Odd].
   + destruct (inv_even_values st Even) as (F & Delta & G).
     assert (Less : ltof State (fun s=>Z.to_nat (Z.abs (g s))) (fst (step st)) st).
     { unfold ltof;apply Nat2Z.inj_lt;rewrite !Z2Nat.id by apply Z.abs_nonneg.
       rewrite G;apply inv_even_half_abs;assumption. }
     destruct (IH (fst (step st)) Less ltac:(lia)) as (n & FN & DN & Result).
     exists (S n);rewrite inv_stepN_start;split;[congruence|];split;assumption.
   + exists 0%nat;split;[reflexivity|];split;[exact Positive|right;exact Odd].
Qed.

Lemma inv_nonpositive_f st n : 0<=eta st -> Z.of_nat n<=1+eta st ->
 f (fst (stepN n st))=f st.
Proof.
 intro HEta;induction n;intro HN;[reflexivity|].
 pose proof (IHn ltac:(lia)) as F.
 pose proof (etaSs n st HEta ltac:(lia)) as Eta.
 cbn [stepN];destruct (stepN n st) as [s tags] eqn:Run.
 destruct (spec s);unfold eta,INC in *;cbn in F,Eta |- *;lia.
Qed.

Lemma inv_positive_start st : exists n,
 f (fst (stepN n st))=f st /\ 0<delta (fst (stepN n st)).
Proof.
 destruct (Z_lt_dec 0 (delta st)) as [Positive|Nonpositive].
 - exists 0%nat;split;[reflexivity|exact Positive].
 - assert (HEta : 0<=eta st) by (unfold eta;lia).
   set (n:=Z.to_nat (1+eta st)).
   assert (N : Z.of_nat n=1+eta st) by (unfold n;rewrite Z2Nat.id by lia;reflexivity).
   pose proof (etaSs n st HEta ltac:(lia)) as E.
   exists n;split;[apply inv_nonpositive_f;lia|].
   rewrite N in E;unfold eta in E;lia.
Qed.

Theorem inv_odd_phase st : exists n,
 f (fst (stepN n st))=f st /\ 0<delta (fst (stepN n st)) /\
 (g (fst (stepN n st))=0 \/ Zodd (g (fst (stepN n st)))).
Proof.
 destruct (inv_positive_start st) as (a & F & D).
 destruct (inv_positive_odd_phase (fst (stepN a st)) D) as (b & F' & D' & Result).
 exists (b+a)%nat;rewrite stepN_app_fst;split;[congruence|];split;assumption.
Qed.

Lemma inv_opposite_g_step st : g st= -f st ->
 (delta st<=0 -> g (fst (step st))=0) /\
 (0<delta st -> g (fst (step st))=f (fst (step st))).
Proof.
 intro Opposite;destruct (spec st);unfold INC;cbn in *;split;intros;lia.
Qed.

Theorem inv_balanced_terminates st : Z.abs (f st)=Z.abs (g st) ->
 exists n,g (fst (stepN n st))=0.
Proof.
 intro Equal.
 assert (Cases : g st=f st \/ g st= -f st) by lia.
 destruct Cases as [Same|Opposite];[apply inv_equal_g_terminates;exact Same|].
 destruct (inv_opposite_g_step st Opposite) as [Nonpositive Positive].
 destruct (Z_lt_dec 0 (delta st)) as [DP|DN].
 - destruct (inv_equal_g_terminates (fst (step st)) (Positive DP)) as [n Zero].
   exists (S n);rewrite inv_stepN_start;exact Zero.
 - exists 1%nat;cbn [stepN];destruct (step st) eqn:E;cbn in *;apply Nonpositive;lia.
Qed.

Definition inv_phase_rank st := 2*Z.max (Z.abs (f st)) (Z.abs (g st))+
 if Z.abs (f st) <? Z.abs (g st) then 1 else 0.

(** Reaching a positive-delta odd-g phase leaves f unchanged. Unless the
    magnitudes coincide (handled separately), its following swap either
    decreases the maximum magnitude or moves a strict maximum from g to f.
    The extra bit in the rank detects that latter decrease. *)

Lemma inv_phase_rank_nonneg st : 0<=inv_phase_rank st.
Proof.
 unfold inv_phase_rank;pose proof (Z.abs_nonneg (f st));
 pose proof (Z.abs_nonneg (g st));destruct (_ <? _);lia.
Qed.

Lemma inv_positive_odd_f st : 0<delta st -> Zodd (g st) ->
 f (fst (step st))=g st.
Proof.
 intros DP Odd;unfold step;destruct (Zeven_odd_dec (g st)) as [Even|O].
 - exfalso;exact (Zeven_not_Zodd _ Even Odd).
 - rewrite (proj2 (Z.ltb_lt 0 (delta st)) DP);reflexivity.
Qed.

Lemma inv_phase_rank_drop st u :
 f u=f st -> Z.abs (g u)<=Z.max (Z.abs (f st)) (Z.abs (g st)) ->
 (Z.abs (g st)<Z.abs (f st) -> Z.abs (g u)<Z.abs (f st)) ->
 Z.abs (f u)<>Z.abs (g u) -> 0<delta u -> Zodd (g u) ->
 inv_phase_rank (fst (step u))<inv_phase_rank st.
Proof.
 intros F G Strict Unequal Positive Odd.
 pose proof (gStepBounds u) as Bound.
 pose proof (inv_positive_odd_f u Positive Odd) as FNext.
 unfold inv_phase_rank;rewrite FNext,F in *.
 destruct (Z.ltb_spec (Z.abs (g u)) (Z.abs (g (fst (step u))))) as [NewLT|NewGE];
 destruct (Z.ltb_spec (Z.abs (f st)) (Z.abs (g st))) as [OldLT|OldGE];lia.
Qed.

(** Every integer divstep trajectory with odd f reaches g=0. This is a
    termination theorem for the existing arithmetic transition, not yet a
    production C execution theorem or a bound on its machine temporaries. *)
Theorem inv_divstep_terminates : forall st,exists n,g (fst (stepN n st))=0.
Proof.
 intro start;pattern start.
 apply (well_founded_induction (well_founded_ltof State
   (fun st=>Z.to_nat (inv_phase_rank st)))).
 clear start;intros st IH.
 destruct (inv_odd_phase st) as (a & F & Positive & [Zero|Odd]).
 - exists a;exact Zero.
 - set (u:=fst (stepN a st)) in *.
   destruct (Z.eq_dec (Z.abs (f u)) (Z.abs (g u))) as [Equal|Unequal].
   + destruct (inv_balanced_terminates u Equal) as [b Done].
     exists (b+a)%nat;rewrite stepN_app_fst;exact Done.
   + destruct (fgBounds st a) as [FB GB].
     change (Z.abs (g u)<=Z.max (Z.abs (f st)) (Z.abs (g st))) in GB.
     assert (Strict : Z.abs (g st)<Z.abs (f st) -> Z.abs (g u)<Z.abs (f st)).
     { intro H;destruct (fgBoundsStrict st a H) as [_ GStrict].
       change (Z.abs (g u)<Z.max (Z.abs (f st)) (Z.abs (g st))) in GStrict;lia. }
     pose proof (inv_phase_rank_drop st u F GB Strict Unequal Positive Odd) as Drop.
     assert (Less : ltof State (fun s=>Z.to_nat (inv_phase_rank s)) (fst (step u)) st).
     { unfold ltof;apply Nat2Z.inj_lt;rewrite !Z2Nat.id by apply inv_phase_rank_nonneg;exact Drop. }
     destruct (IH (fst (step u)) Less) as [b Done].
     exists (S b+a)%nat;rewrite stepN_app_fst,inv_stepN_start;exact Done.
Qed.

Corollary inv_divstep_batches_terminate st : exists batches,
 g (fst (stepN (62*batches)%nat st))=0.
Proof.
 destruct (inv_divstep_terminates st) as [n Done].
 exists n.
 replace (62*n)%nat with (61*n+n)%nat by lia.
 rewrite stepN_app_fst;apply fixed_g;exact Done.
Qed.

