(** Arithmetic invariants for the actual div_mod_96_64 correction loop.
    These support its forthcoming memory-aware Clight execution proof;
    they do not count as a public C jet correctness theorem. *)
From Coq Require Import ZArith Lia.
Require Import C.jet_division_approx_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition divmod96_estimate B ah bh := Z.min (ah / bh) (B - 1).

Lemma divmod96_initial_bounds B ah al D bh bl :
  2 <= B -> 0 <= ah < D -> 0 <= al < B ->
  0 < bh < B -> 0 <= bl < B -> D = bh * B + bl -> B * B <= 2 * D ->
  let q := divmod96_estimate B ah bh in
  0 <= q < B /\ 0 <= ah - q * bh <= ah /\ 0 <= q * bl < B * B /\
  -2 * D <= (ah * B + al) - q * D < D.
Proof.
  intros HB HA HAL HBH HBL HD Hnorm. cbn zeta.
  set (q := divmod96_estimate B ah bh).
  pose proof (Z.div_mod ah bh ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound ah bh ltac:(lia)) as Hmod.
  assert (He : 0 <= ah / bh) by (apply Z.div_pos; lia).
  assert (Hq : 0 <= q < B).
  { unfold q, divmod96_estimate. split.
    - apply Z.min_glb; lia.
    - pose proof (Z.le_min_r (ah / bh) (B - 1)). lia. }
  assert (Hqe : q <= ah / bh) by (unfold q, divmod96_estimate; apply Z.le_min_l).
  assert (Hrh : 0 <= ah - q * bh <= ah) by nia.
  assert (Hd : 0 <= q * bl < B * B) by nia.
  assert (Hcase : ah - q * bh < bh \/ q = B - 1).
  { destruct (Z_le_gt_dec (ah / bh) (B - 1)) as [Hsmall|Hlarge].
    - left. unfold q, divmod96_estimate. rewrite Z.min_l by exact Hsmall. nia.
    - right. unfold q, divmod96_estimate. rewrite Z.min_r by lia. reflexivity. }
  split; [exact Hq|]. split; [exact Hrh|]. split; [exact Hd|].
  apply (division_approx_residual_bounds B ah (ah * B + al) D al bh bl q (ah - q * bh)).
  - exact HB.
  - exact HAL.
  - lia.
  - exact HBL.
  - exact Hnorm.
  - exact HD.
  - reflexivity.
  - assert (Hmul : ah * B <= (D - 1) * B).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    replace ((D - 1) * B) with (D * B - B) in Hmul by ring. lia.
  - exact Hq.
  - exact (proj1 Hrh).
  - ring.
  - exact Hcase.
Qed.

Lemma divmod96_guard_exact B rh al d :
  2 <= B -> 0 <= rh -> 0 <= al < B -> 0 <= d < B * B ->
  (rh <= B - 1 /\ B * rh + al < d) <-> B * rh + al - d < 0.
Proof. intros HB HR HA HD. split; [lia|]. intros Hneg. split; [nia|lia]. Qed.

Lemma divmod96_compare_no_wrap B rh al :
  2 <= B -> 0 <= rh <= B - 1 -> 0 <= al < B ->
  0 <= B * rh + al < B * B.
Proof. intros; nia. Qed.

Lemma divmod96_correction_step B ah al D bh bl q rh d delta :
  2 <= B -> 0 <= ah -> 0 <= al < B ->
  0 < bh < B -> 0 <= bl < B -> D = bh * B + bl ->
  0 <= q < B -> 0 <= rh -> ah = q * bh + rh -> d = q * bl ->
  delta = B * rh + al - d -> delta < 0 ->
  0 <= q - 1 < B /\
  0 <= rh + bh <= ah /\ ah = (q - 1) * bh + (rh + bh) /\
  0 <= d - bl < B * B /\ d - bl = (q - 1) * bl /\
  B * (rh + bh) + al - (d - bl) = delta + D /\ delta + D < D.
Proof.
  intros HB HA HAL HBH HBL HD HQ HR Hah Hd Hdelta Hneg.
  assert (Hpositive : 1 <= q) by nia.
  repeat split; nia.
Qed.

Lemma divmod96_two_corrections_suffice D delta0 i :
  0 < D -> -2 * D <= delta0 -> 2 <= i -> 0 <= delta0 + i * D.
Proof. intros; nia. Qed.

Lemma divmod96_exit_balance B ah al D q rh d :
  0 < D -> ah * B + al = q * D + (B * rh + al - d) ->
  B * rh + al - d < D ->
  ~ (rh <= B - 1 /\ B * rh + al < d) ->
  2 <= B -> 0 <= rh -> 0 <= al < B -> 0 <= d < B * B ->
  q * D + (B * rh + al - d) = ah * B + al /\
  0 <= B * rh + al - d < D.
Proof.
  intros HD Hbalance Hupper Hexit HB HR HAL Hdbound. split; [lia|]. split; [|exact Hupper].
  destruct (Z_lt_ge_dec (B * rh + al - d) 0) as [Hnegative|Hnonnegative]; [|lia].
  exfalso. apply Hexit. apply (proj2 (divmod96_guard_exact B rh al d HB HR HAL Hdbound)); exact Hnegative.
Qed.
