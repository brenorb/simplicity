(** Range facts for the original f/g update and shortening expressions.
    Keep inactive stored slots bounded as well as the active integer values. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import C.jet_secp_signed62_ranges C.jet_secp_modinv_normalize62_words.
Require Import C.jet_secp_modinv_var_fg C.jet_secp_modinv_var_tail C.jet_secp_modinv_var_post.
Require Import C.jet_secp_modinv_var_zero C.jet_secp_modinv_var_shorten.
Require Import C.jet_secp_modinv_fg_start C.jet_secp_modinv_fg_body C.jet_secp_modinv_fg_loop_numeric.
Require Import C.jet_secp_modinv_fg_finish_numeric.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition inv_fg_limb_bounds (rho : nat->int64) := forall (high : bool) j,(j<5)%nat ->
  Z.abs (Int64.signed (rho ((if high then 20 else 15)+j)%nat))<=2^62.
Definition inv_fg_value_capacity len rho := forall high,
  Z.abs (inv_fg_active_value len rho high)<=2^(62*Z.of_nat len).

Lemma inv_fg_limb_array len rho high j : (j<5)%nat ->
  fg_array_word (inv_fg_rho len rho) high j=rho ((if high then 20 else 15)+j)%nat.
Proof. destruct high;destruct j as [|[|[|[|[|j]]]]];intro J;try lia;reflexivity. Qed.

Lemma inv_fg_body_nontop len rho high j : (0<len<=5)%nat -> fg_input_bounds rho ->
  (j<5)%nat -> j<>(len-1)%nat -> Z.abs (Int64.signed (fg_body_word len rho high j))<=2^62.
Proof.
  intros Len Bounds J NotTop.
  pose proof (proj2 (fg_loop_numeric (len-1) (fg_start_rho rho) high 1 ltac:(lia) ltac:(lia)
    (fg_start_state_bounds rho Bounds))) as BodyBounds.
  unfold fg_body_word,fg_finished_word;rewrite (proj2 (Nat.eqb_neq j (len-1)) NotTop).
  exact (proj2 BodyBounds high j J).
Qed.

Lemma inv_fg_next_ranges len rho : (0<len<=5)%nat -> fg_input_bounds (inv_fg_rho len rho) ->
  inv_fg_value_capacity len (inv_fg_next_rho len rho) -> inv_fg_limb_bounds (inv_fg_next_rho len rho).
Proof.
  intros Len Bounds Capacity high j J;rewrite inv_fg_next_word by exact J.
  destruct (Nat.eq_dec j (len-1)) as [->|NotTop].
  - apply (s62_value_top_bound (len-1) (fun i=>Int64.signed (fg_body_word len (inv_fg_rho len rho) high i))).
    + intros i I;apply inv_fg_body_lower;lia.
    + replace (S (len-1)) with len by lia.
      specialize (Capacity high);unfold inv_fg_active_value in Capacity.
      replace (norm62_value_z (len-1) (fun i=>Int64.signed (fg_body_word len (inv_fg_rho len rho) high i)))
        with (norm62_value_z (len-1) (fun i=>Int64.signed (inv_fg_next_rho len rho ((if high then 20 else 15)+i)%nat)));
        [exact Capacity|].
      apply norm62_value_ext;intros i I;rewrite inv_fg_next_word by lia;reflexivity.
  - apply inv_fg_body_nontop;assumption.
Qed.

Lemma inv_fg_next_low len rho : (0<len<=5)%nat -> inv_tail_low_bounds len (inv_fg_next_rho len rho).
Proof. intros Len high j J;rewrite inv_fg_next_word by lia;apply inv_fg_body_lower;assumption. Qed.

Lemma inv_shorten_all_bounds len w : (2<=len<=5)%nat -> inv_active_low_bounds len w ->
  inv_sign_word (w (len-1)%nat) -> (forall j,(j<5)%nat -> Z.abs (Int64.signed (w j))<=2^62) ->
  forall j,(j<5)%nat -> Z.abs (Int64.signed (inv_shorten_words len w j))<=2^62.
Proof.
  intros Len Low Top Bounds j J;unfold inv_shorten_words;destruct (Nat.eqb j (len-2)) eqn:At.
  - apply Nat.eqb_eq in At;subst j;rewrite inv_shorten_limb_signed by (first [exact Top|apply Low;lia]).
    pose proof (Low (len-2)%nat ltac:(lia)) as Digit;apply Z.abs_le.
    destruct Top as [Zero|Mone];[rewrite Zero,Int64.signed_zero|rewrite Mone,Int64.signed_mone];lia.
  - apply Bounds;exact J.
Qed.

Lemma inv_top_sign_capacity len w : (0<len<=5)%nat -> inv_active_low_bounds len w ->
  inv_sign_word (w (len-1)%nat) -> Z.abs (inv_active_value len w)<=2^(62*Z.of_nat (len-1)).
Proof.
  intros Len Low Top;apply s62_unit_top_capacity.
  - intros i I;apply Low;lia.
  - destruct Top as [Zero|Mone];[left;rewrite Zero|right;rewrite Mone];reflexivity.
Qed.

Lemma inv_post_length_valid len rho : (0<len<=5)%nat -> (0<inv_post_length len rho<=5)%nat.
Proof.
  intro Len;unfold inv_post_length;destruct (inv_control_stops len rho);[exact Len|].
  unfold inv_shortened_length;destruct (inv_control_shrink len rho) eqn:Shrink;[|exact Len].
  pose proof (proj1 (inv_shorten_guard_correct len _ _ Len) Shrink) as (Two & _);lia.
Qed.

Lemma inv_post_ranges len rho : (0<len<=5)%nat ->
  (forall high,inv_active_low_bounds len (inv_control_word rho high)) ->
  (forall high j,(j<5)%nat -> Z.abs (Int64.signed (inv_control_word rho high j))<=2^62) ->
  (forall high,Z.abs (inv_active_value len (inv_control_word rho high))<=2^(62*Z.of_nat len)) ->
  (forall high j,(j<5)%nat -> Z.abs (Int64.signed (inv_post_word len rho high j))<=2^62) /\
  (forall high,Z.abs (inv_active_value (inv_post_length len rho) (inv_post_word len rho high))<=
    2^(62*Z.of_nat (inv_post_length len rho))).
Proof.
  intros Len Low Bounds Capacity;unfold inv_post_word,inv_post_length;
    destruct (inv_control_stops len rho);[split;assumption|].
  unfold inv_control_short_word,inv_shortened_length;destruct (inv_control_shrink len rho) eqn:Shrink;
    [|split;assumption].
  destruct (proj1 (inv_shorten_guard_correct len _ _ Len) Shrink) as (Two & F & G);split.
  - intro high;apply inv_shorten_all_bounds;[lia|apply Low|destruct high;assumption|apply Bounds].
  - intro high;rewrite inv_shorten_preserves_value by
      (try lia;try apply Low;destruct high;assumption).
    apply inv_top_sign_capacity;[exact Len|apply Low|destruct high;assumption].
Qed.

Lemma inv_tail_value_preserved len rho high : (0<len<=5)%nat -> inv_tail_low_bounds len rho ->
  inv_fg_active_value (inv_tail_length len rho) (inv_tail_next_rho len rho) high=
    inv_fg_active_value len rho high.
Proof.
  intros Len Low;assert (Next : (0<inv_tail_length len rho<=5)%nat) by (apply inv_post_length_valid;exact Len).
  rewrite inv_tail_next_value by exact Next;unfold inv_tail_length.
  rewrite (inv_post_next_value len (inv_control_view rho) high Next).
  rewrite (proj1 (inv_post_numeric len (inv_control_view rho) high Len
    ltac:(intros i I;rewrite inv_control_view_word by lia;apply Low;exact I))).
  apply inv_control_view_value;exact Len.
Qed.

Theorem inv_tail_ranges len rho : (0<len<=5)%nat -> inv_tail_low_bounds len rho ->
  inv_fg_limb_bounds rho -> inv_fg_value_capacity len rho ->
  inv_fg_limb_bounds (inv_tail_next_rho len rho) /\
  inv_fg_value_capacity (inv_tail_length len rho) (inv_tail_next_rho len rho).
Proof.
  intros Len Low Bounds Capacity.
  destruct (inv_post_ranges len (inv_control_view rho) Len) as (Words & Values).
  - intros high i I;rewrite inv_control_view_word by lia;apply Low;exact I.
  - intros high j J;rewrite inv_control_view_word by exact J;apply Bounds;exact J.
  - intro high;rewrite inv_control_view_value by exact Len;apply Capacity.
  - split.
    + intros high j J;rewrite inv_tail_next_word,inv_post_next_word by exact J;apply Words;exact J.
    + intro high;rewrite inv_tail_next_value by (apply inv_post_length_valid;exact Len).
      unfold inv_tail_length;rewrite inv_post_next_value by (apply inv_post_length_valid;exact Len).
      apply Values.
Qed.
