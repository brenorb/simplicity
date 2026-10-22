(** Arithmetic bounds for the production variable-time divstep loop.
    No fixed iteration certificate is used. *)
From Coq Require Import ZArith Lia.
Require Import C.divstep C.jet_secp_divstep_termination.
Local Open Scope Z_scope.
Set Default Timeout 10.

(** While g is nonzero, each halving trades a bit of g for one unit of
    positive delta; a swap resets delta to nonpositive. Track that trade
    rather than bounding delta by the total number of iterations. *)
Definition inv_live_delta_bound B st :=
 -B<=delta st /\ delta st+Z.log2 (Z.abs (g st))<=B+1.

Lemma inv_log2_abs_double a : a<>0 ->
 Z.log2 (Z.abs (2*a))=1+Z.log2 (Z.abs a).
Proof.
 intro NZ;rewrite Z.abs_mul;change (Z.abs 2) with 2.
 rewrite Z.log2_double by (apply (proj2 (Z.abs_pos a));exact NZ);lia.
Qed.

Lemma inv_live_eta_range B st : inv_live_delta_bound B st ->
 -B-1<=eta st<=B.
Proof.
 intros [Lower Upper];pose proof (Z.log2_nonneg (Z.abs (g st))).
 unfold eta;lia.
Qed.

Lemma inv_live_batch_eta B st k : inv_live_delta_bound B st ->
 (k<=62)%nat ->
 -(B+64)<=eta (fst (stepN k st))<B+64.
Proof.
 intros Bound Steps;pose proof (inv_live_eta_range B st Bound) as Range.
 pose proof (etaBounds (B+2) k st ltac:(lia)) as Result.
 apply Nat2Z.inj_le in Steps;change (Z.of_nat 62) with 62 in Steps;lia.
Qed.

Lemma inv_initial_delta_bound B st : 0<=B -> delta st=1 ->
 Z.abs (g st)<=2^B -> inv_live_delta_bound B st.
Proof.
 intros BN Delta BG.
 pose proof (Z.log2_le_mono (Z.abs (g st)) (2^B) BG) as Bound.
 rewrite Z.log2_pow2 in Bound by exact BN.
 unfold inv_live_delta_bound;rewrite Delta;split;lia.
Qed.

Lemma inv_live_delta_step B st : 0<=B ->
 Z.abs (f st)<=2^B -> Z.abs (g st)<=2^B ->
 inv_live_delta_bound B st -> g (fst (step st))<>0 ->
 inv_live_delta_bound B (fst (step st)).
Proof.
 intros BN BF BG (Lower & Upper) Live.
 assert (LogBound : Z.log2 (Z.abs (g (fst (step st))))<=B).
 { pose proof (gStepBounds st) as GN.
   pose proof (Z.log2_le_mono (Z.abs (g (fst (step st)))) (2^B) ltac:(lia)) as Log.
   rewrite Z.log2_pow2 in Log by exact BN;exact Log. }
 pose proof (Z.log2_nonneg (Z.abs (g st))) as OldNonneg.
 unfold inv_live_delta_bound.
 destruct (spec st);unfold INC;cbn [fst f g delta] in *.
 - rewrite inv_log2_abs_double in Upper by exact Live;split;lia.
 - split;lia.
 - split;lia.
Qed.

Theorem inv_live_delta_trajectory B st n : 0<=B ->
 Z.abs (f st)<=2^B -> Z.abs (g st)<=2^B ->
 inv_live_delta_bound B st -> g (fst (stepN n st))<>0 ->
 inv_live_delta_bound B (fst (stepN n st)).
Proof.
 intros BN BF BG Initial;induction n;intro Live;[exact Initial|].
 assert (Previous : g (fst (stepN n st))<>0).
 { intro Zero;pose proof (fixed_g (fst (stepN n st)) 1 Zero) as Z.
   rewrite inv_stepN_start in Z;cbn [stepN] in Z.
   cbn [stepN] in Live;destruct (stepN n st) as [s tags];cbn in *.
   destruct (step s);cbn in *;contradiction. }
 pose proof (IHn Previous) as Bound.
 destruct (fgBounds st n) as [FN GN].
 pose proof (inv_live_delta_step B (fst (stepN n st)) BN
   ltac:(lia) ltac:(lia) Bound) as Next.
 cbn [stepN] in Live |- *;destruct (stepN n st) as [s tags] eqn:Run;cbn in *.
 destruct (step s);cbn in *;apply Next;exact Live.
Qed.

(** The first batch is run even on zero input; every subsequent batch is run
    only while g is nonzero. Thus this bound includes the actual zero-input
    control-flow case and the trailing steps after g becomes zero in a batch. *)
Theorem inv_256_batch_eta_safe st n k : delta st=1 ->
 Z.abs (f st)<=2^256 -> Z.abs (g st)<=2^256 ->
 (n=0%nat \/ g (fst (stepN n st))<>0) -> (k<=62)%nat ->
 -320<=eta (fst (stepN k (fst (stepN n st))))<320.
Proof.
 intros Delta BF BG Run Steps.
 assert (Initial : inv_live_delta_bound 256 st)
   by (apply inv_initial_delta_bound;[lia|exact Delta|exact BG]).
 apply (inv_live_batch_eta 256 (fst (stepN n st)) k);[|exact Steps].
 destruct Run as [First|Live].
 - subst n;exact Initial.
 - apply inv_live_delta_trajectory;[lia|exact BF|exact BG|exact Initial|exact Live].
Qed.

