(** Algebraic invariants of the exact numeric simulation of Arith.bezout.
    In particular the actual low-word coefficients never wrap on these
    positive inputs. These facts support literal normalization certificates;
    they are not a public C inversion-jet equivalence theorem. *)
From Coq Require Import ZArith Lia.
Require Import C.jet_secp_eea_numeric C.jet_secp_eea_fast C.jet_division_value.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition eea_coefficients x y (s : ((Z*Z)*Z)*((Z*Z)*Z)) :=
 let '(((a,b),c),((d,e),f)):=s in
 0<=a<=y /\ 0<=b<=x /\ 0<=d<=y /\ 0<=e<=x /\
 0<=c /\ 0<=f /\ a*x-b*y=c /\ d*x-e*y= -f /\
 a*f+d*c=y /\ b*f+e*c=x.

Lemma eea_coefficients_initial x y : 0<x -> 0<y ->
 eea_coefficients x y (((1,0),x),((0,1),y)).
Proof. intros X Y;unfold eea_coefficients;repeat split;lia. Qed.

Lemma eea_coefficients_valid modulus x y s :
 x<modulus -> y<modulus -> eea_coefficients x y s -> eea_state_valid modulus s.
Proof.
 destruct s as [[[a b] c] [[d e] f]];unfold eea_coefficients,eea_state_valid,eea_row_valid;
   cbn [fst snd];intros X Y Invariant;decompose [and] Invariant;repeat split;lia.
Qed.

Lemma eea_coefficient_update modulus limit a d c f :
 0<=a -> 0<=d -> 0<=c -> 0<f -> limit<modulus -> a*f+d*c=limit ->
 0<=a+(c/f)*d<=limit /\
 (a+(c/f)*d) mod modulus=a+(c/f)*d /\
 (a+(c/f)*d)*f+d*(c mod f)=limit.
Proof.
 intros A D C F Limit Sum.
 pose proof (Z.div_pos c f C ltac:(lia)) as Quotient.
 pose proof (Z.mod_pos_bound c f F) as Remainder.
 pose proof (Z.div_mod c f ltac:(lia)) as Division.
 assert (Conserved : (a+(c/f)*d)*f+d*(c mod f)=limit).
 { replace ((a+(c/f)*d)*f+d*(c mod f)) with (a*f+d*(f*(c/f)+c mod f)) by ring.
   rewrite <-Division;exact Sum. }
 assert (Bound : 0<=a+(c/f)*d<=limit) by nia.
 split;[exact Bound|];split;[apply Z.mod_small;lia|exact Conserved].
Qed.

Lemma eea_coefficients_left modulus x y a b c d e f :
 x<modulus -> y<modulus -> 0<f ->
 eea_coefficients x y (((a,b),c),((d,e),f)) ->
 eea_coefficients x y (eea_row_step_numeric modulus ((a,b),c) ((d,e),f),((d,e),f)).
Proof.
 intros X Y F (A & B & D & E & C & F0 & Left & Right & SumY & SumX).
 destruct (eea_coefficient_update modulus y a d c f ltac:(lia) ltac:(lia) C F Y SumY)
   as (AB & AM & SY).
 destruct (eea_coefficient_update modulus x b e c f ltac:(lia) ltac:(lia) C F X SumX)
   as (BB & BM & SX).
 assert (Linear : (a+(c/f)*d)*x-(b+(c/f)*e)*y=c mod f).
 { replace ((a+(c/f)*d)*x-(b+(c/f)*e)*y) with ((a*x-b*y)+(c/f)*(d*x-e*y)) by ring.
   rewrite Left,Right;pose proof (Z.div_mod c f ltac:(lia));nia. }
 pose proof (Z.mod_pos_bound c f F) as Remainder.
 unfold eea_row_step_numeric,division_numeric.
 rewrite (proj2 (Z.eqb_neq f 0)) by lia.
 cbn;rewrite AM,BM.
 unfold eea_coefficients;repeat split;try lia.
Qed.

Lemma eea_coefficients_right modulus x y a b c d e f :
 x<modulus -> y<modulus -> 0<c ->
 eea_coefficients x y (((a,b),c),((d,e),f)) ->
 eea_coefficients x y (((a,b),c),eea_row_step_numeric modulus ((d,e),f) ((a,b),c)).
Proof.
 intros X Y C (A & B & D & E & C0 & F & Left & Right & SumY & SumX).
 destruct (eea_coefficient_update modulus y d a f c ltac:(lia) ltac:(lia) F C Y ltac:(nia))
   as (DB & DM & SY).
 destruct (eea_coefficient_update modulus x e b f c ltac:(lia) ltac:(lia) F C X ltac:(nia))
   as (EB & EM & SX).
 assert (Linear : (d+(f/c)*a)*x-(e+(f/c)*b)*y= -(f mod c)).
 { replace ((d+(f/c)*a)*x-(e+(f/c)*b)*y) with ((d*x-e*y)+(f/c)*(a*x-b*y)) by ring.
   rewrite Right,Left;pose proof (Z.div_mod f c ltac:(lia));nia. }
 pose proof (Z.mod_pos_bound f c C) as Remainder.
 unfold eea_row_step_numeric,division_numeric.
 rewrite (proj2 (Z.eqb_neq c 0)) by lia.
 cbn;rewrite DM,EM.
 unfold eea_coefficients;repeat split;try nia.
Qed.

Theorem eea_coefficients_step modulus x y s :
 x<modulus -> y<modulus -> eea_coefficients x y s ->
 eea_coefficients x y (eea_step_numeric modulus s).
Proof.
 intros X Y Invariant.
 pose proof (eea_coefficients_valid modulus x y s X Y Invariant) as Valid.
 destruct s as [[[a b] c] [[d e] f]].
 pose proof Invariant as (_ & _ & _ & _ & C & F & _).
 destruct (Z.eq_dec c 0) as [Zero|NonzeroC].
 - rewrite (eea_finished_step modulus _ Valid);
     [exact Invariant|unfold eea_finished;cbn [fst snd];rewrite Zero;reflexivity].
 - destruct (Z.eq_dec f 0) as [Zero|NonzeroF].
   + rewrite (eea_finished_step modulus _ Valid);
       [exact Invariant|unfold eea_finished;cbn [fst snd];rewrite Zero,Bool.orb_true_r;reflexivity].
   + unfold eea_step_numeric;cbn [fst snd];destruct (f<?c).
     * apply eea_coefficients_left;try assumption;lia.
     * apply eea_coefficients_right;try assumption;lia.
Qed.

Theorem eea_coefficients_run modulus count x y s :
 x<modulus -> y<modulus -> eea_coefficients x y s ->
 eea_coefficients x y (eea_run_numeric modulus count s).
Proof.
 intros X Y;revert s;induction count as [|count IH];intros s Invariant;[exact Invariant|].
 cbn [eea_run_numeric];apply IH;apply eea_coefficients_step;assumption.
Qed.
