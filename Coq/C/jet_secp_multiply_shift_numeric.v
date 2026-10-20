(** Exact two-limb value bridge for the original field multiplier's shift. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Values Memory Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_multiply_shift_shift.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma two_limb_division M D S H L :
  0 < D -> 0 < S -> M = D * S -> 0 <= H < M -> 0 <= L < M ->
  (H / D) * M + (H * S + L / D) mod M = (H * M + L) / D.
Proof.
  intros HD HS HM HH HL.
  pose proof (Z.div_mod H D ltac:(lia)) as Hh.
  pose proof (Z.div_mod L D ltac:(lia)) as Hl.
  pose proof (Z.mod_pos_bound H D HD) as Hr.
  pose proof (Z.mod_pos_bound L D HD) as Lr.
  assert (Lq : 0 <= L / D < S).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; nia]. }
  assert (HE : (H * S + L / D) mod M = (H mod D) * S + L / D).
  { symmetry; apply Z.mod_unique with (H / D); [left; nia|nia]. }
  rewrite HE. apply Z.div_unique with (L mod D); [left; lia|nia].
Qed.

Lemma shru52_unsigned value :
  Int64.unsigned (Int64.shru value (Int64.repr 52)) = Int64.unsigned value / 4503599627370496.
Proof.
  rewrite Int64.shru_div_two_p.
  change (Int64.unsigned (Int64.repr (Int64.unsigned value / 4503599627370496)) =
    Int64.unsigned value / 4503599627370496).
  apply Int64.unsigned_repr.
  pose proof (Int64.unsigned_range value) as HB.
  change (0 <= Int64.unsigned value < 18446744073709551616) in HB.
  change (0 <= Int64.unsigned value / 4503599627370496 <= 18446744073709551615).
  split; [apply Z.div_pos; lia|].
  assert (Int64.unsigned value / 4503599627370496 < 4096).
  { apply Z.div_lt_upper_bound; lia. }
  lia.
Qed.

Lemma shift52_low_unsigned lo hi :
  Int64.unsigned (shift52_low lo hi) =
    (Int64.unsigned hi * 4096 + Int64.unsigned lo / 4503599627370496) mod Int64.modulus.
Proof.
  unfold shift52_low. rewrite Int64.mul_commut, Int64.mul_one.
  rewrite Int64.shifted_or_is_add.
  - rewrite Int64.unsigned_repr_eq, shru52_unsigned. reflexivity.
  - change (0 <= 12 < 64); lia.
  - rewrite shru52_unsigned. change (Int64.unsigned lo / 4503599627370496 < 4096).
    apply Z.div_lt_upper_bound; [lia|].
    pose proof (Int64.unsigned_range lo) as HB.
    change (0 <= Int64.unsigned lo < 18446744073709551616) in HB; lia.
Qed.

Theorem shift52_numeric lo hi :
  Int64.unsigned (shift52_high hi) * Int64.modulus + Int64.unsigned (shift52_low lo hi) =
    (Int64.unsigned hi * Int64.modulus + Int64.unsigned lo) / 4503599627370496.
Proof.
  unfold shift52_high. rewrite shru52_unsigned, shift52_low_unsigned.
  apply (two_limb_division Int64.modulus 4503599627370496 4096);
    try apply Int64.unsigned_range; reflexivity || lia.
Qed.

Theorem eval_u128_shift52_exact m b lo hi :
  Mem.range_perm m b 0 16 Cur Writable ->
  Mem.load Mint64 m b 0 = Some (Vlong lo) -> Mem.load Mint64 m b 8 = Some (Vlong hi) ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_u128_rshift)
      (Vptr b Ptrofs.zero :: Vint (Int.repr 52) :: nil) E0 mf Vundef /\
    Mem.load Mint64 mf b 0 = Some (Vlong (shift52_low lo hi)) /\
    Mem.load Mint64 mf b 8 = Some (Vlong (shift52_high hi)) /\
    Int64.unsigned (shift52_high hi) * Int64.modulus + Int64.unsigned (shift52_low lo hi) =
      (Int64.unsigned hi * Int64.modulus + Int64.unsigned lo) / 4503599627370496 /\
    (forall bb ofs k p, Mem.perm m bb ofs k p -> Mem.perm mf bb ofs k p) /\
    lframe (fun bb ofs => ~ (bb = b /\ 0 <= ofs < 16)) m mf.
Proof.
  intros HP HL HH.
  destruct (eval_u128_shift52 m b lo hi HP HL HH) as (mf & HC & HLo & HHi & HPerm & HFrame).
  exists mf; split; [exact HC|]; split; [exact HLo|]; split; [exact HHi|];
    split; [apply shift52_numeric|]; split; assumption.
Qed.
