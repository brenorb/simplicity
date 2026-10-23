(** Algebra of the original C signed 32-bit partial-product schedule. *)
From Coq Require Import ZArith Lia.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma smul128_limb_balance B a b : 1<B ->
 let ll := (a mod B)*(b mod B) in
 let lh := (a mod B)*(b/B) in
 let hl := (a/B)*(b mod B) in
 let hh := (a/B)*(b/B) in
 let mid := ll/B+lh mod B+hl mod B in
 let hi := hh+lh/B+hl/B+mid/B in
 let lo := (mid mod B)*B+ll mod B in
 0<=ll<B*B /\ 0<=mid<3*B /\ 0<=lo<B*B /\
 a*b=hi*(B*B)+lo /\ hi=(a*b)/(B*B) /\ lo=(a*b) mod (B*B).
Proof.
 intros Bpos ll lh hl hh mid hi lo.
 pose proof (Z.mod_pos_bound a B ltac:(lia)) as AL.
 pose proof (Z.mod_pos_bound b B ltac:(lia)) as BL.
 assert (LL : 0<=ll<B*B) by (unfold ll;nia).
 assert (LQ : 0<=ll/B<B) by (split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;nia]).
 pose proof (Z.mod_pos_bound lh B ltac:(lia)) as LHM.
 pose proof (Z.mod_pos_bound hl B ltac:(lia)) as HLM.
 assert (MID : 0<=mid<3*B) by (unfold mid;lia).
 pose proof (Z.mod_pos_bound mid B ltac:(lia)) as MM.
 pose proof (Z.mod_pos_bound ll B ltac:(lia)) as LM.
 assert (LO : 0<=lo<B*B) by (unfold lo;nia).
 assert (Split : a*b=hh*(B*B)+(lh+hl)*B+ll).
 { unfold hh,lh,hl,ll;rewrite (Z.div_mod a B ltac:(lia)) at 1;
   rewrite (Z.div_mod b B ltac:(lia)) at 1;ring. }
 assert (Balance : a*b=hi*(B*B)+lo).
 { rewrite Split;unfold hi,lo.
   pose proof (Z.div_mod ll B ltac:(lia)).
   pose proof (Z.div_mod lh B ltac:(lia)).
   pose proof (Z.div_mod hl B ltac:(lia)).
   pose proof (Z.div_mod mid B ltac:(lia)).
   assert (M : mid=ll/B+lh mod B+hl mod B) by reflexivity.
   nia. }
 split;[exact LL|];split;[exact MID|];split;[exact LO|];split;[exact Balance|];split.
 - apply Z.div_unique with lo;[left;exact LO|nia].
 - apply Z.mod_unique with hi;[left;exact LO|nia].
Qed.

Lemma smul128_half_bounds a : -2^63<=a<2^63 ->
 0<=a mod 2^32<2^32 /\ -2^31<=a/2^32<2^31.
Proof.
 intro Range;split;[apply Z.mod_pos_bound;lia|];split.
 - apply Z.div_le_lower_bound;lia.
 - apply Z.div_lt_upper_bound;lia.
Qed.

Lemma smul128_low_high_product x y : 0<=x<2^32 -> -2^31<=y<2^31 ->
 -2^63<=x*y<2^63.
Proof.
 intros X Y.
 assert (AX : Z.abs x<=2^32-1) by (apply Z.abs_le;lia).
 assert (AY : Z.abs y<=2^31) by (apply Z.abs_le;lia).
 pose proof (Z.mul_le_mono_nonneg _ _ _ _ (Z.abs_nonneg x) AX (Z.abs_nonneg y) AY) as Bound.
 rewrite <-Z.abs_mul in Bound;apply Z.abs_le in Bound;lia.
Qed.

Lemma smul128_high_high_product x y : -2^31<=x<2^31 -> -2^31<=y<2^31 ->
 -2^62<=x*y<=2^62.
Proof.
 intros X Y.
 assert (AX : Z.abs x<=2^31) by (apply Z.abs_le;lia).
 assert (AY : Z.abs y<=2^31) by (apply Z.abs_le;lia).
 pose proof (Z.mul_le_mono_nonneg _ _ _ _ (Z.abs_nonneg x) AX (Z.abs_nonneg y) AY) as Bound.
 rewrite <-Z.abs_mul in Bound;apply Z.abs_le in Bound;lia.
Qed.
