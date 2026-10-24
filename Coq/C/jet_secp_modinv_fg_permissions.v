(** The actual variable transition keeps a caller's matrix Freeable. *)
From Coq Require Import ZArith List Bool Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Maps Integers Values Memory Events Globalenvs.
Require Import C.jet_clight_internal_frame C.jet_secp_linkage C.jets_secp C.jet_secp_fns.
Require Import C.jet_secp_modinv_fg_call C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_start.
Require Import C.jet_secp_modinv_fg_body C.jet_secp_modinv_fg_finish_numeric.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem.
Require Import C.jet_clight_internal_permissions.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fg_internal_table :=
 [(_secp256k1_mul128,f_secp256k1_mul128);
  (_secp256k1_i128_mul,f_secp256k1_i128_mul);
  (_secp256k1_i128_accum_mul,f_secp256k1_i128_accum_mul);
  (_secp256k1_i128_rshift,f_secp256k1_i128_rshift);
  (_secp256k1_i128_to_u64,f_secp256k1_i128_to_u64);
  (_secp256k1_i128_to_i64,f_secp256k1_i128_to_i64);
  (_secp256k1_modinv64_update_fg_62_var,f_secp256k1_modinv64_update_fg_62_var)].
Lemma fg_internal_subset id fd : In (id,fd) fg_internal_table -> In (id,fd) secp_pure.
Proof.
 intro Member;cbn [fg_internal_table In] in Member.
 destruct Member as [Eq|[Eq|[Eq|[Eq|[Eq|[Eq|[Eq|Empty]]]]]]];try contradiction.
 all: injection Eq as <- <-;unfold secp_pure;repeat first [left;reflexivity|right].
Qed.
Definition fg_internal_checks := forallb (fun p=>closed_stmtb fg_internal_table (fn_body (snd p)) &&
 forallb (fun it=>nonfunction_type (snd it)) (fn_vars (snd p))) fg_internal_table.
Lemma fg_internal_checks_true : fg_internal_checks=true.
Proof. vm_compute;reflexivity. Qed.
Lemma fg_internal_table_ok : internal_table_ok secp_ge fg_internal_table.
Proof.
 intros id fd Lookup;pose proof (internal_lookup_in _ _ _ Lookup) as Member.
 split;[apply secp_pure_ok;apply fg_internal_subset;exact Member|].
 pose proof fg_internal_checks_true as Checks;unfold fg_internal_checks in Checks.
 rewrite forallb_forall in Checks;specialize (Checks (id,fd) Member);apply andb_true_iff in Checks;exact Checks.
Qed.
Lemma fg_internal_allowed : allowed_call fg_internal_table (Internal f_secp256k1_modinv64_update_fg_62_var).
Proof. exists _secp256k1_modinv64_update_fg_62_var,f_secp256k1_modinv64_update_fg_62_var;split;reflexivity. Qed.

Theorem eval_fg_transition_matrix_permissions len rho beta m : (0<len<=5)%nat ->
 Int64.loword (rho 14%nat)=Int.repr (Z.of_nat len) -> fg_input_bounds rho -> rep rho beta fg_regs m ->
 Mem.range_perm m (blk beta 2) 0 32 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_update_fg_62_var)
  [Vint (Int.repr (Z.of_nat len));Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef /\
 Mem.range_perm mf (blk beta 2) 0 32 Cur Freeable /\
 (forall (high : bool) j,(j<len)%nat -> Mem.load Mint64 mf (blk beta (if high then 1 else 0))
  (bas beta (if high then 1 else 0)+8*Z.of_nat j)=Some (Vlong (fg_body_word len rho high j))) /\
 (forall high,fg_body_value len rho high=fg_matrix_value rho high len/2^62) /\
 rep (fg_body_rho len rho) beta (fg_call_out len) mf /\
 lframe (fun b ofs=>~foot beta (map rshape fg_regs) b ofs) m mf.
Proof.
 intros Bound Len Bounds Rep Matrix.
 destruct (eval_fg_transition len rho beta m Bound Len Bounds Rep) as (mf & Call & Words & Numeric & Out & Frame).
 pose proof (proj2 (internal_exec_keeps_permissions secp_ge fg_internal_table fg_internal_table_ok)
  _ _ _ _ _ _ Call fg_internal_allowed) as Keep.
 exists mf;split;[exact Call|];split.
 - intros ofs InRange;apply Keep,Matrix;exact InRange.
 - split;[exact Words|];split;[exact Numeric|];split;assumption.
Qed.
