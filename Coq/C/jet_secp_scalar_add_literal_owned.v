(** Compose actual scalar-add helper execution with the literal Core result.
    Reader value equalities are internal bridge inputs, not public premises:
    the two-reader caller still must derive them for every Word256 pair. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_frame.
Require Import C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage.
Require Import C.jet_secp_scalar_overflow_numeric C.jet_secp_canonical_scalar.
Require Import C.jet_secp_scalar_writer_run.
Require Import C.jet_secp_scalar_add_run C.jet_secp_scalar_add_exec.
Require Import C.jet_secp_scalar_add_numeric C.jet_secp_scalar_add_reduced.
Require Import C.jet_secp_scalar_add_numeric_exec C.jet_secp_scalar_add_storage.
Require Import C.jet_secp_canonical_scalar_add C.jet_secp_canonical_scalar_add_numeric.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_scalar_add_literal_owned rho layout m (a b : Ty.tySem (Word 8)) :
  rep rho layout scalar_add_initial_regs m ->
  scalar_limb_value rho = @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem a) ->
  scalar_limb_value (scalar_add_second_rho rho) =
    @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem b) ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_add)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))] E0 mf
      (Vint (b2i (Z.leb canonical_group_order (scalar_add_input_value rho)))) /\
    rep (scalar_limb_rho (@toZ (WordToZ 8) (@canonical_scalar_add Alg.CoreFunSem (a,b))))
      [(blk layout 0, bas layout 0)] scalar_writer_initial_regs mf /\
    Mem.range_perm mf (blk layout 0) 0 32 Cur Freeable /\
    Mem.range_perm mf (blk layout 1) 0 32 Cur Freeable /\
    lframe (fun block ofs => ~ foot layout (map rshape scalar_add_initial_regs) block ofs) m mf.
Proof.
  intros HRep HA HB.
  assert (HS : 0 <= scalar_add_input_value rho < 2 * canonical_group_order).
  { unfold scalar_add_input_value; rewrite HA, HB.
    apply canonical_scalar_add_normalized_inputs_range. }
  destruct (eval_scalar_add_mod_group_owned rho layout m HRep HS)
    as [mf [HCall [HFinal [HOwn0 [HOwn1 [HLoads [HValue HFrame]]]]]]].
  assert (HLiteral : scalar_add_output_value rho (lay layout) =
    @toZ (WordToZ 8) (@canonical_scalar_add Alg.CoreFunSem (a,b))).
  { rewrite HValue; unfold scalar_add_input_value; rewrite HA, HB.
    apply canonical_scalar_add_normalize_value. }
  pose proof (scalar_writer_initial_rep_from_add rho layout mf HFinal) as HWriter.
  rewrite HLiteral in HWriter.
  exists mf; split; [exact HCall|]; split; [exact HWriter|];
    split; [exact (proj2 HOwn0)|]; split; [exact (proj2 HOwn1)|exact HFrame].
Qed.
