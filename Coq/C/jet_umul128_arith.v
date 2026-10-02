(** Integer observation of the actual 32-bit-limb secp256k1_umul128 algorithm.
    This supports its C execution proof; it is not public jet coverage. *)
From Coq Require Import ZArith Lia.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem umul128_limb_algorithm B a b :
  1 < B -> 0 <= a < B * B -> 0 <= b < B * B ->
  let ll := (a mod B) * (b mod B) in
  let lh := (a mod B) * (b / B) in
  let hl := (a / B) * (b mod B) in
  let hh := (a / B) * (b / B) in
  let mid := ll / B + lh mod B + hl mod B in
  let hi := hh + lh / B + hl / B + mid / B in
  let lo := (mid mod B) * B + ll mod B in
  0 <= ll < B * B /\ 0 <= lh < B * B /\ 0 <= hl < B * B /\ 0 <= hh < B * B /\
  0 <= mid < 3 * B /\ 0 <= hi < B * B /\ 0 <= lo < B * B /\
  a * b = hi * (B * B) + lo /\ hi = (a * b) / (B * B) /\ lo = (a * b) mod (B * B).
Proof.
  intros HB Ha Hb ll lh hl hh mid hi lo.
  pose proof (Z.mod_pos_bound a B ltac:(lia)) as Hal.
  pose proof (Z.mod_pos_bound b B ltac:(lia)) as Hbl.
  assert (Hah : 0 <= a / B < B).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; nia]. }
  assert (Hbh : 0 <= b / B < B).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; nia]. }
  assert (Hll : 0 <= ll < B * B) by (unfold ll; nia).
  assert (Hlh : 0 <= lh < B * B) by (unfold lh; nia).
  assert (Hhl : 0 <= hl < B * B) by (unfold hl; nia).
  assert (Hhh : 0 <= hh < B * B) by (unfold hh; nia).
  assert (Hlld : 0 <= ll / B < B).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; nia]. }
  pose proof (Z.mod_pos_bound ll B ltac:(lia)) as Hllm.
  pose proof (Z.mod_pos_bound lh B ltac:(lia)) as Hlhm.
  pose proof (Z.mod_pos_bound hl B ltac:(lia)) as Hhlm.
  assert (Hmid : 0 <= mid < 3 * B) by (unfold mid; lia).
  pose proof (Z.mod_pos_bound mid B ltac:(lia)) as Hmm.
  assert (Hlo : 0 <= lo < B * B) by (unfold lo; nia).
  assert (Hhi0 : 0 <= hi).
  { unfold hi. pose proof (Z.div_pos lh B ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos hl B ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos mid B ltac:(lia) ltac:(lia)). lia. }
  assert (Hsplit : a * b = hh * (B * B) + (lh + hl) * B + ll).
  { unfold hh, lh, hl, ll.
    rewrite (Z.div_mod a B ltac:(lia)) at 1.
    rewrite (Z.div_mod b B ltac:(lia)) at 1. ring. }
  assert (Hbalance : a * b = hi * (B * B) + lo).
  { rewrite Hsplit. unfold hi, lo.
    pose proof (Z.div_mod ll B ltac:(lia)) as ELL.
    pose proof (Z.div_mod lh B ltac:(lia)) as ELH.
    pose proof (Z.div_mod hl B ltac:(lia)) as EHL.
    pose proof (Z.div_mod mid B ltac:(lia)) as EMID.
    assert (EM : mid = ll / B + lh mod B + hl mod B) by reflexivity.
    nia. }
  assert (Hproduct : a * b < (B * B) * (B * B)).
  { clear - HB Ha Hb. nia. }
  assert (Hhi : hi < B * B).
  { clearbody hi lo. clear - HB Hbalance Hproduct Hlo Hhi0. nia. }
  do 7 (split; [first [assumption | split; assumption]|]). split; [exact Hbalance|]. split.
  - apply Z.div_unique with lo; [left; exact Hlo|]. nia.
  - apply Z.mod_unique with hi; [left; exact Hlo|]. nia.
Qed.
