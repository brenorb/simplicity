(** Numeric observation of the actual multiply-accumulate, allowing wrap.
    Reuses the original product and wrapped-carry observations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_u64_carry.
Require Import C.jet_secp_umul128_exec C.jet_secp_umul128_numeric.
Require Import C.jet_secp_u128_accum_mul_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition accum_mul_lo_machine rho :=
  Int64.add (rho 2%nat) (umul128_lo_machine (rho 0%nat) (rho 1%nat)).
Definition accum_mul_hi_machine rho :=
  Int64.add (rho 3%nat)
    (Int64.add (umul128_hi_machine (rho 0%nat) (rho 1%nat))
      (Int64.repr (Int.signed
        (if Int64.ltu (accum_mul_lo_machine rho) (umul128_lo_machine (rho 0%nat) (rho 1%nat))
         then Int.one else Int.zero)))).

Lemma accum_mul_lo_den rho layout :
  den rho layout accum_mul_lo = Vlong (accum_mul_lo_machine rho).
Proof. reflexivity. Qed.
Lemma accum_mul_hi_den rho layout :
  den rho layout accum_mul_hi = Vlong (accum_mul_hi_machine rho).
Proof. reflexivity. Qed.

Lemma accum_mul_unsigned_outputs rho :
  let product := Int64.unsigned (rho 0%nat) * Int64.unsigned (rho 1%nat) in
  Int64.unsigned (accum_mul_lo_machine rho) =
    (Int64.unsigned (rho 2%nat) + product mod Int64.modulus) mod Int64.modulus /\
  Int64.unsigned (accum_mul_hi_machine rho) =
    (Int64.unsigned (rho 3%nat) + product / Int64.modulus +
      (Int64.unsigned (rho 2%nat) + product mod Int64.modulus) / Int64.modulus) mod Int64.modulus.
Proof.
  intros product.
  destruct (umul128_unsigned_outputs (rho 0%nat) (rho 1%nat)) as [HH HL].
  split.
  - unfold accum_mul_lo_machine.
    rewrite Int64.add_unsigned, Int64.unsigned_repr_eq, HL; reflexivity.
  - unfold accum_mul_hi_machine, accum_mul_lo_machine.
    rewrite Int64.add_unsigned, Int64.unsigned_repr_eq.
    rewrite Int64.add_unsigned, Int64.unsigned_repr_eq.
    rewrite u64_add_carry_bit_right, HH, HL.
    rewrite Z.add_mod_idemp_r by (pose proof Int64.modulus_pos; lia).
    unfold product; rewrite Z.add_assoc; reflexivity.
Qed.

Lemma accum_mul_two_limb_mod M H L P :
  0 < M ->
  ((H + P / M + (L + P mod M) / M) mod M) * M + (L + P mod M) mod M =
    (H * M + L + P) mod (M * M).
Proof.
  intros HM.
  set (Q := H + P / M + (L + P mod M) / M).
  pose proof (Z.div_mod P M ltac:(lia)) as HP.
  pose proof (Z.div_mod (L + P mod M) M ltac:(lia)) as HL.
  pose proof (Z.div_mod Q M ltac:(lia)) as HQ.
  pose proof (Z.mod_pos_bound Q M HM) as HBH.
  pose proof (Z.mod_pos_bound (L + P mod M) M HM) as HBL.
  apply Z.mod_unique with (Q / M).
  - left; nia.
  - unfold Q in *; nia.
Qed.

Lemma accum_mul_numeric_value rho :
  Int64.unsigned (accum_mul_hi_machine rho) * Int64.modulus +
    Int64.unsigned (accum_mul_lo_machine rho) =
  (Int64.unsigned (rho 3%nat) * Int64.modulus + Int64.unsigned (rho 2%nat) +
    Int64.unsigned (rho 0%nat) * Int64.unsigned (rho 1%nat)) mod (Int64.modulus * Int64.modulus).
Proof.
  destruct (accum_mul_unsigned_outputs rho) as [HL HH].
  rewrite HL, HH. apply accum_mul_two_limb_mod; pose proof Int64.modulus_pos; lia.
Qed.

Theorem eval_u128_accum_mul_owned_product rho layout m :
  rep rho layout u128_accum_mul_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_u128_accum_mul)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vlong (rho 0%nat); Vlong (rho 1%nat)] E0 mf Vundef /\
    Mem.load Mint64 mf (blk layout 0) (bas layout 0) = Some (Vlong (accum_mul_lo_machine rho)) /\
    Mem.load Mint64 mf (blk layout 0) (bas layout 0 + 8) = Some (Vlong (accum_mul_hi_machine rho)) /\
    Int64.unsigned (accum_mul_hi_machine rho) * Int64.modulus +
      Int64.unsigned (accum_mul_lo_machine rho) =
      (Int64.unsigned (rho 3%nat) * Int64.modulus + Int64.unsigned (rho 2%nat) +
        Int64.unsigned (rho 0%nat) * Int64.unsigned (rho 1%nat)) mod (Int64.modulus * Int64.modulus) /\
    rep rho layout [mkreg (u64_cells 0 [accum_mul_lo; accum_mul_hi]) true (Some 16)] mf /\
    lframe (fun b ofs => ~ foot layout (map rshape u128_accum_mul_initial_regs) b ofs) m mf.
Proof.
  intro HRep.
  destruct (eval_u128_accum_mul_owned rho layout m HRep) as (mf & HCall & HFinal & HFrame).
  pose proof (rep_region rho layout _ mf 0 _ HFinal eq_refl) as HRegion.
  pose proof (region_load rho layout mf 0 _ 0 Mint64 accum_mul_lo HRegion
    ltac:(cbn [rcells u64_cells]; left; reflexivity)) as HLow.
  pose proof (region_load rho layout mf 0 _ 8 Mint64 accum_mul_hi HRegion
    ltac:(cbn [rcells u64_cells]; right; left; reflexivity)) as HHigh.
  rewrite Z.add_0_r, accum_mul_lo_den in HLow.
  rewrite accum_mul_hi_den in HHigh.
  exists mf; split; [exact HCall|]; split; [exact HLow|]; split; [exact HHigh|];
    split; [apply accum_mul_numeric_value|]; split; [exact HFinal|exact HFrame].
Qed.
