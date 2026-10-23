(** Early return only after a proved fixed point of the exact numeric EEA.
    This optimization does not change a Simplicity term or iteration count. *)
From Coq Require Import ZArith Lia.
Require Import C.jet_secp_eea_numeric C.jet_division_value C.jet_secp_invert_literal
 C.jet_secp_canonical_normalize C.jet_secp_fe_math.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition eea_row_valid modulus (r : (Z*Z)*Z) :=
 let '((a,b),c):=r in 0<=a<modulus /\ 0<=b<modulus /\ 0<=c.
Definition eea_state_valid modulus (s : ((Z*Z)*Z)*((Z*Z)*Z)) :=
 eea_row_valid modulus (fst s) /\ eea_row_valid modulus (snd s).
Definition eea_finished (s : ((Z*Z)*Z)*((Z*Z)*Z)) :=
 orb (Z.eqb (snd (fst s)) 0) (Z.eqb (snd (snd s)) 0).

Lemma eea_row_step_valid modulus r t :
 0<modulus -> eea_row_valid modulus r -> eea_row_valid modulus t ->
 eea_row_valid modulus (eea_row_step_numeric modulus r t).
Proof.
 destruct r as [[a b] c],t as [[d e] f];intros Modulus [_ [_ C]] [_ [_ F]].
 unfold eea_row_step_numeric,eea_row_valid;repeat split;try (apply Z.mod_pos_bound;exact Modulus).
 unfold division_numeric;destruct (Z.eqb_spec f 0);[exact C|].
 pose proof (Z.mod_pos_bound c f ltac:(lia));lia.
Qed.
Lemma eea_step_valid modulus s :
 0<modulus -> eea_state_valid modulus s -> eea_state_valid modulus (eea_step_numeric modulus s).
Proof.
 destruct s as [r t];intros Modulus [R T];unfold eea_step_numeric.
 destruct (snd t <? snd r);split;first [assumption|apply eea_row_step_valid;assumption].
Qed.

Lemma eea_finished_step modulus s :
 eea_state_valid modulus s -> eea_finished s=Datatypes.true -> eea_step_numeric modulus s=s.
Proof.
 destruct s as [[[a b] c] [[d e] f]];intros [[A [B C]] [D [E F]]] Done.
 unfold eea_finished in Done;cbn [fst snd] in Done.
 apply Bool.orb_true_iff in Done;destruct Done as [Done|Done];apply Z.eqb_eq in Done.
 - subst c;unfold eea_step_numeric;cbn [fst snd].
   rewrite (proj2 (Z.ltb_ge f 0)) by lia.
   unfold eea_row_step_numeric;cbn [division_numeric].
   rewrite !Z.mul_0_l,!Z.add_0_r,!Z.mod_small by lia;reflexivity.
 - subst f;unfold eea_step_numeric;cbn [fst snd].
   destruct (Z.ltb_spec 0 c).
   + unfold eea_row_step_numeric;cbn [division_numeric].
     rewrite !Z.mul_0_l,!Z.add_0_r,!Z.mod_small by lia;reflexivity.
   + assert (c=0) by lia;subst c.
     unfold eea_row_step_numeric;cbn [division_numeric].
     rewrite !Z.mul_0_l,!Z.add_0_r,!Z.mod_small by lia;reflexivity.
Qed.
Lemma eea_run_fixed modulus count s : eea_step_numeric modulus s=s -> eea_run_numeric modulus count s=s.
Proof. intro Fixed;induction count;[reflexivity|cbn [eea_run_numeric];rewrite Fixed;exact IHcount]. Qed.

Fixpoint eea_run_fast modulus count s :=
 match count with
 | Datatypes.O => s
 | Datatypes.S k => if eea_finished s then s else eea_run_fast modulus k (eea_step_numeric modulus s)
 end.
Theorem eea_run_fast_matches modulus count s :
 0<modulus -> eea_state_valid modulus s ->
 eea_run_fast modulus count s=eea_run_numeric modulus count s.
Proof.
 intros Modulus;revert s;induction count as [|count IH];intros s Valid;[reflexivity|].
 cbn [eea_run_fast];destruct (eea_finished s) eqn:Done.
 - symmetry;apply eea_run_fixed;apply eea_finished_step;assumption.
 - cbn [eea_run_numeric];apply IH;apply eea_step_valid;assumption.
Qed.

Definition literal_invert_fast x :=
 match eea_bezout_numeric (eea_run_fast (2^256) 512
   (((1,0),canonical_field_order),((0,1),x))) with
 | inl (_,b) => (canonical_field_order-b) mod canonical_field_order
 | inr (_,e) => e
 end.
Lemma literal_invert_fast_matches x : 0<=x -> literal_invert_fast x=literal_invert_numeric x.
Proof.
 intro X;unfold literal_invert_fast,literal_invert_numeric.
 rewrite eea_run_fast_matches;[reflexivity|vm_compute;reflexivity|].
 unfold eea_state_valid,eea_row_valid;cbn [fst snd];rewrite canonical_field_order_matches_limb_model.
 assert (0<feP) by (unfold feP,feR;lia).
 assert (1<2^256) by (vm_compute;reflexivity).
 repeat split;lia.
Qed.
