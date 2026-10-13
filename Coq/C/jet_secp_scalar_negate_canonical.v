(** Relate the actual helper to the literal multiplication/mod512 program;
    public reader/caller and return/free composition remain separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_frame.
Require Import C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage.
Require Import C.jet_secp_scalar_overflow_numeric C.jet_secp_canonical_scalar.
Require Import C.jet_secp_scalar_writer_run.
Require Import C.jet_secp_scalar_negate_run C.jet_secp_scalar_negate_exec.
Require Import C.jet_secp_scalar_negate_numeric C.jet_secp_scalar_negate_storage.
Require Import C.jet_secp_canonical_scalar_negate.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma scalar_limb_rho_value value :
  0 <= value < 2 ^ 256 -> scalar_limb_value (scalar_limb_rho value) = value.
Proof.
  intro HV; unfold scalar_limb_value.
  rewrite !scalar_limb_rho_unsigned by exact HV.
  cbn [scalar_limbs_of nth].
  pose proof (Z.div_mod value (2 ^ 64) ltac:(lia)) as H0.
  pose proof (Z.div_mod (value / 2 ^ 64) (2 ^ 64) ltac:(lia)) as H1.
  pose proof (Z.div_mod (value / 2 ^ 128) (2 ^ 64) ltac:(lia)) as H2.
  rewrite Z.div_div in H1, H2 by lia.
  change (value / 2 ^ 64 = 2 ^ 64 * (value / 2 ^ 128) + (value / 2 ^ 64) mod 2 ^ 64) in H1.
  change (value / 2 ^ 128 = 2 ^ 64 * (value / 2 ^ 192) + (value / 2 ^ 128) mod 2 ^ 64) in H2.
  change (2 ^ 64) with 18446744073709551616 in *.
  change (2 ^ 128) with 340282366920938463463374607431768211456 in *.
  change (2 ^ 192) with 6277101735386680763835789423207666416102355444464034512896 in *.
  lia.
Qed.

Lemma scalar_negate_normalize_range (value : Ty.tySem (Word 8)) :
  0 <= @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value) < canonical_group_order.
Proof.
  rewrite canonical_scalar_normalize_numeric.
  apply Z.mod_pos_bound; pose proof canonical_group_order_range; lia.
Qed.

Lemma scalar_negate_output_canonical rho layout (value : Ty.tySem (Word 8)) :
  scalar_limb_value rho = @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value) ->
  scalar_negate_output_value rho layout = @toZ (WordToZ 8) (@canonical_scalar_negate Alg.CoreFunSem value).
Proof.
  intro HValue.
  assert (HRange : 0 <= scalar_limb_value rho < canonical_group_order).
  { rewrite HValue; apply scalar_negate_normalize_range. }
  rewrite scalar_negate_normalized_value by exact HRange.
  rewrite HValue; apply canonical_scalar_negate_normalize_value.
Qed.

Local Opaque secp_ge canonical_scalar_normalize canonical_scalar_negate.
Theorem eval_scalar_negate_canonical_owned rho layout m (value : Ty.tySem (Word 8)) :
  rep rho layout scalar_writer_initial_regs m ->
  scalar_limb_value rho = @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value) ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_negate)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf Vundef /\
    scalar_at mf (blk layout 0) (bas layout 0)
      (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) (@canonical_scalar_negate Alg.CoreFunSem value)))) /\
    rep (scalar_limb_rho (@toZ (WordToZ 8) (@canonical_scalar_negate Alg.CoreFunSem value)))
      [(blk layout 0, bas layout 0)] scalar_writer_initial_regs mf /\
    Mem.range_perm mf (blk layout 0) 0 32 Cur Freeable /\
    lframe (fun b ofs => ~ foot layout (map rshape scalar_writer_initial_regs) b ofs) m mf.
Proof.
  intros HRep HValue.
  destruct (eval_scalar_negate_from_owned_region rho layout m HRep) as [mf [HCall [HFinal HFrame]]].
  destruct (scalar_negate_output_scalar_at rho layout mf HFinal) as [HStorage HFree].
  pose proof (scalar_writer_initial_rep_from_negate rho layout mf HFinal) as HWriter.
  rewrite (scalar_negate_output_canonical rho (lay layout) value HValue) in HStorage, HWriter.
  exists mf; split; [exact HCall|]; split; [exact HStorage|]; split; [exact HWriter|]; split; assumption.
Qed.
