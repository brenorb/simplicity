(** Original C function call with derived integer values and bounds. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math.
Require Import C.jet_secp_modinv_de_exec C.jet_secp_modinv_de_recurrence_words.
Require Import C.jet_secp_modinv_de_correction_numeric C.jet_secp_modinv_normalize62_numeric.
Require Import C.jet_secp_modinv_de_numeric.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_de_transition rho beta m : rep rho beta de62_regs m ->
 (forall high,de62_row_bound rho high) -> de62_state_bounds rho -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_update_de_62)
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
   Vptr (blk beta 2) (Ptrofs.repr (bas beta 2));Vptr (blk beta 3) (Ptrofs.repr (bas beta 3))] E0 mf Vundef /\
 (forall (high : bool) i,(i<5)%nat -> Mem.load Mint64 mf (blk beta (if high then 1 else 0))
  (bas beta (if high then 1 else 0)+8*Z.of_nat i)=Some (Vlong (de62_recurrence_word rho high i))) /\
 (forall high,
   2^62*de62_output_value rho high=de62_matrix_value rho high+feP*de62_correction_value rho high /\
   de62_output_value rho high=(de62_matrix_value rho high+feP*de62_correction_value rho high)/2^62 /\
   (2^62*de62_output_value rho high-de62_matrix_value rho high) mod feP=0 /\
   norm62_limb_bounds (de62_recurrence_word rho high) /\
   -2*feP<de62_output_value rho high<feP) /\
 rep rho beta (sregs de62_state) mf /\
 lframe (fun b ofs=>~foot beta (map rshape de62_regs) b ofs) m mf.
Proof.
 intros Rep Rows Bounds.
 pose proof (de62_state_input_bound rho Bounds) as Inputs.
 destruct (eval_de_recurrence rho beta m Rep) as (mf & Call & Words & Out & Frame).
 exists mf;split;[exact Call|];split;[exact Words|];split.
 - intro high;split;[apply de62_scaled_value;[apply Rows|exact Inputs]|];
   split;[apply de62_quotient_value;[apply Rows|exact Inputs]|];
   split;[apply de62_modular_value;[apply Rows|exact Inputs]|];
   split;[apply de62_output_limb_bounds|apply de62_output_range];[apply Rows|exact Bounds|apply Rows|exact Bounds].
 - split;assumption.
Qed.
