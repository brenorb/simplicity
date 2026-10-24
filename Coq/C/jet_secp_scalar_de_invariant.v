(** Connect the actual scalar coefficient update to canonical divsteps.
    The loop must establish the incoming matrix/state relation and execute
    its f/g update; neither fact is assumed as a completed jet result. *)
From Coq Require Import ZArith Znumtheory List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_scalar_de_exec C.jet_secp_scalar_de_numeric
 C.jet_secp_scalar_de_ranges C.jet_secp_scalar_de_revalue C.jet_secp_canonical_scalar
 C.jet_secp_modinv_de_numeric C.jet_secp_modinv_de_correction_numeric
 C.jet_secp_modinv_var_invariant C.divstep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma scalar_inv_batch_coprime : rel_prime canonical_group_order (2^62).
Proof. apply Zgcd_1_rel_prime;vm_compute;reflexivity. Qed.
Lemma scalar_inv_modulus_nonzero : canonical_group_order<>0.
Proof. unfold canonical_group_order;lia. Qed.

Definition scalar_de62_matrix_u (rho : nat->int64) (high : bool) :=
 Int64.signed(rho(if high then 12%nat else 10%nat)).
Definition scalar_de62_matrix_v (rho : nat->int64) (high : bool) :=
 Int64.signed(rho(if high then 13%nat else 11%nat)).
Definition scalar_de62_matrix_matches rho st :=
 scalar_de62_matrix_u rho false=Trans.u(Trans.transN 62 st) /\
 scalar_de62_matrix_v rho false=Trans.v(Trans.transN 62 st) /\
 scalar_de62_matrix_u rho true=Trans.q(Trans.transN 62 st) /\
 scalar_de62_matrix_v rho true=Trans.r(Trans.transN 62 st).
Definition scalar_de62_coefficient_link value rho st := forall high,
 (value*de62_input_value rho high) mod canonical_group_order=
 (if high then g st else f st) mod canonical_group_order.

Lemma scalar_de62_matrix_row_bounds rho st : scalar_de62_matrix_matches rho st ->
 forall high,de62_row_bound rho high.
Proof.
 intros(U & V & Q & R) high.
 pose proof(Trans.bounded_transN 62 st) as Bound;unfold Trans.bounded in Bound.
 change(Z.of_nat 62) with 62 in Bound.
 change(Z.abs(scalar_de62_matrix_u rho high)+Z.abs(scalar_de62_matrix_v rho high)<=2^62).
 destruct high;[rewrite Q,R|rewrite U,V];lia.
Qed.

Lemma scalar_de62_matrix_scaled_state rho st (high : bool) : scalar_de62_matrix_matches rho st ->
 2^62*(if high then g(fst(stepN 62 st)) else f(fst(stepN 62 st)))=
 scalar_de62_matrix_u rho high*f st+scalar_de62_matrix_v rho high*g st.
Proof.
 intros(U & V & Q & R);destruct high.
 - rewrite Q,R;pose proof(f_equal Trans.y (Trans.transN_step 62 st)) as Row;exact Row.
 - rewrite U,V;pose proof(f_equal Trans.x (Trans.transN_step 62 st)) as Row;exact Row.
Qed.

Lemma scalar_de62_next_coefficient_link value rho st : scalar_de62_matrix_matches rho st ->
 scalar_de62_coefficient_link value rho st ->
 (forall high,2^62*de62_input_value (scalar_de62_next_rho rho) high=
   de62_matrix_value rho high+canonical_group_order*scalar_de62_correction_value rho high) ->
 scalar_de62_coefficient_link value (scalar_de62_next_rho rho) (fst(stepN 62 st)).
Proof.
 intros Matrix Link Numeric high.
 eapply inv_scaled_coefficient_modulus.
 - exact scalar_inv_modulus_nonzero.
 - exact scalar_inv_batch_coprime.
 - apply Numeric.
 - apply(scalar_de62_matrix_scaled_state rho st high Matrix).
 - change((value*(scalar_de62_matrix_u rho high*de62_input_value rho false+
     scalar_de62_matrix_v rho high*de62_input_value rho true)) mod canonical_group_order=
     (scalar_de62_matrix_u rho high*f st+scalar_de62_matrix_v rho high*g st) mod canonical_group_order).
   apply inv_linear_mod_modulus;[exact(Link false)|exact(Link true)].
Qed.

Lemma scalar_de62_zero_matrix_row rho st : g st=0 -> scalar_de62_matrix_matches rho st ->
 scalar_de62_matrix_u rho false=2^62 /\ scalar_de62_matrix_v rho false=0.
Proof.
 intros Zero(U & V & Q & R).
 pose proof(Trans.transHs 62 st ltac:(rewrite Zero;exists 0;ring)) as Matrix.
 rewrite Matrix in U,V;split;assumption.
Qed.

Lemma scalar_de62_zero_coefficient rho st : g st=0 -> scalar_de62_matrix_matches rho st ->
 2^62*de62_input_value (scalar_de62_next_rho rho) false=
   de62_matrix_value rho false+canonical_group_order*scalar_de62_correction_value rho false ->
 de62_input_value (scalar_de62_next_rho rho) false mod canonical_group_order=
   de62_input_value rho false mod canonical_group_order.
Proof.
 intros Zero Matrix Update.
 destruct(scalar_de62_zero_matrix_row rho st Zero Matrix) as(U & V).
 change(2^62*de62_input_value (scalar_de62_next_rho rho) false=
   scalar_de62_matrix_u rho false*de62_input_value rho false+
   scalar_de62_matrix_v rho false*de62_input_value rho true+
   canonical_group_order*scalar_de62_correction_value rho false) in Update.
 rewrite U,V,Z.mul_0_l,Z.add_0_r in Update.
 apply(inv_cancel_batch_modulus canonical_group_order _ _ scalar_inv_modulus_nonzero scalar_inv_batch_coprime).
 rewrite Update,(Z.mul_comm canonical_group_order (scalar_de62_correction_value rho false)).
 apply Z_mod_plus_full.
Qed.

(** The real call, next-state representation, bounds, coefficient link,
    zero-case preservation and frame are all conclusions. The matrix match
    remains an internal pre-state obligation of the actual divstep caller. *)
Theorem eval_scalar_de_invariant value rho st beta m : rep rho beta scalar_de62_regs m ->
 scalar_de62_state_bounds rho -> scalar_de62_matrix_matches rho st ->
 scalar_de62_coefficient_link value rho st -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_update_de_62)
  [Vptr (blk beta 0) (Ptrofs.repr(bas beta 0));Vptr (blk beta 1) (Ptrofs.repr(bas beta 1));
   Vptr (blk beta 2) (Ptrofs.repr(bas beta 2));Vptr (blk beta 3) (Ptrofs.repr(bas beta 3))] E0 mf Vundef /\
 rep (scalar_de62_next_rho rho) beta scalar_de62_regs mf /\
 scalar_de62_state_bounds (scalar_de62_next_rho rho) /\
 scalar_de62_coefficient_link value (scalar_de62_next_rho rho) (fst(stepN 62 st)) /\
 (g st=0 -> de62_input_value (scalar_de62_next_rho rho) false mod canonical_group_order=
   de62_input_value rho false mod canonical_group_order) /\
 (forall high,
  2^62*de62_input_value (scalar_de62_next_rho rho) high=
   de62_matrix_value rho high+canonical_group_order*scalar_de62_correction_value rho high /\
  (2^62*de62_input_value (scalar_de62_next_rho rho) high-de62_matrix_value rho high) mod canonical_group_order=0) /\
 lframe (fun b ofs=>~foot beta (map rshape scalar_de62_regs) b ofs) m mf.
Proof.
 intros Rep Bounds Matrix Link.
 destruct(eval_scalar_de_step rho beta m Rep (scalar_de62_matrix_row_bounds rho st Matrix) Bounds)
   as(mf & Call & Out & NextBounds & Numeric & Frame).
 exists mf;split;[exact Call|];split;[exact Out|];split;[exact NextBounds|];split.
 - eapply scalar_de62_next_coefficient_link;[exact Matrix|exact Link|intro high;exact(proj1(Numeric high))].
 - split;[|split;assumption]. intro Zero;eapply scalar_de62_zero_coefficient;
   [exact Zero|exact Matrix|exact(proj1(Numeric false))].
Qed.
