(** Four real output words after freeing the stack, with readable rhs retained. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Clight ClightBigstep Ctypes Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem
  C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar
  C.jet_secp_product_reduce_bridge C.jet_secp_reduce512_final_atomic
  C.jet_secp_reduce512_final_stage C.jet_secp_reduce512_body_numeric
  C.jet_secp_scalar_mul512_low C.jet_secp_scalar_mul512_accumulate
  C.jet_secp_scalar_mul_caller_function C.jet_secp_scalar_mul_caller_observed.
Require Import C.jet_secp_scalar_mul_borrowed_alloc C.jet_secp_scalar_mul_borrowed_function.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque product_reduce_rho reduce512_body_digits reduce512_body_carry reduce512_final_limbs.

Theorem eval_scalar_mul_borrowed_inplace_observed rho beta m :
  rep rho beta scalar_mul_borrowed_inputs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
    (forall i w, nth_error (scalar_mul_caller_words rho) i = Some w ->
      Mem.load Mint64 mf (blk beta 0) (bas beta 0 + 8 * Z.of_nat i) = Some (Vlong w)) /\
    column_words_value (scalar_mul_caller_words rho) =
      (scalar_mul512_input_value rho 0 * scalar_mul512_input_value rho 4) mod canonical_group_order /\
    rep (product_reduce_rho rho) [lay beta 0] (scalar_mul_caller_output rho) mf /\
    region_ok rho beta mf 1 scalar_mul_borrowed_rhs /\
    lframe (fun b ofs => ~ foot beta (map rshape scalar_mul_borrowed_inputs) b ofs) m mf.
Proof.
  intro HR. destruct (eval_scalar_mul_borrowed_inplace rho beta m HR) as (mf & HC & HP & HV & HBR & HF).
  pose proof (rep_region (product_reduce_rho rho) [lay beta 0]
    (scalar_mul_caller_output rho) mf 0 _ HP eq_refl) as Hregion.
  exists mf; split; [exact HC|]. split.
  - intros i w Hnth. unfold scalar_mul_caller_words in Hnth. rewrite nth_error_map in Hnth.
    destruct (nth_error (scalar_mul_caller_limbs rho) i) as [sy|] eqn:HX; [|discriminate].
    cbn [option_map] in Hnth. injection Hnth as Ew. subst w.
    pose proof (u64_cells_nth _ 0 i sy HX) as Hcell. rewrite Z.add_0_l in Hcell.
    fold (scalar_mul_caller_limbs rho) in Hregion.
    pose proof (region_load (product_reduce_rho rho) [lay beta 0] mf 0
      (mkreg (u64_cells 0 (scalar_mul_caller_limbs rho)) true (Some 32))
      (8 * Z.of_nat i) Mint64 sy Hregion Hcell) as Hload.
    destruct (scalar_mul_caller_output_location beta) as (EB & ES).
    rewrite EB,ES in Hload.
    assert (HK : isk KL sy = true).
    { pose proof (reduce512_final_limb_kinds
        (reduce512_body_digits (product_reduce_rho rho))
        (reduce512_body_carry (product_reduce_rho rho))) as HKs.
      rewrite forallb_forall in HKs. apply HKs.
      apply nth_error_In in HX. exact HX. }
    rewrite (den_KL _ _ _ HK) in Hload.
    rewrite (proj2 (den_proj_indep (product_reduce_rho rho) sy
      (lay [lay beta 0]) (lay []))) in Hload. exact Hload.
  - split.
    + unfold scalar_mul_caller_words,scalar_mul_caller_limbs.
      change (final_output_value (reduce512_body_digits (product_reduce_rho rho))
        (reduce512_body_carry (product_reduce_rho rho)) (product_reduce_rho rho) (lay []) =
        (scalar_mul512_input_value rho 0 * scalar_mul512_input_value rho 4) mod canonical_group_order).
      rewrite <- (scalar_mul_output_layout_indep
        (reduce512_body_digits (product_reduce_rho rho))
        (reduce512_body_carry (product_reduce_rho rho)) (product_reduce_rho rho)
        (lay [lay beta 0]) (lay [])).
      exact HV.
    + exact (conj HP (conj HBR HF)).
Qed.
