(** Reinterpret the real scalar coefficient-update result as the next
    complete represented state, retaining matrix, modulus and ownership. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_u64_transport C.jet_sx_mem.
Require Import C.jet_secp_scalar_de_exec C.jet_secp_scalar_de_recurrence
 C.jet_secp_scalar_de_numeric C.jet_secp_scalar_de_ranges.
Require Import C.jet_secp_modinv_de_numeric C.jet_secp_modinv_de_correction_numeric C.jet_secp_modinv_de_revalue
 C.jet_secp_modinv_normalize62_words C.jet_secp_modinfo_scalar_global
 C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_de62_next_rho (rho : nat->int64) n :=
 if (n <? 10)%nat then scalar_de62_recurrence_word rho (5 <=? n)%nat (n mod 5)%nat else rho n.
Lemma scalar_de62_next_array rho high i : (i<5)%nat ->
 de62_array (scalar_de62_next_rho rho) high i=scalar_de62_recurrence_word rho high i.
Proof. destruct high;destruct i as [|[|[|[|[|i]]]]];intro I;try lia;reflexivity. Qed.
Lemma scalar_de62_next_input_value rho high : de62_input_value (scalar_de62_next_rho rho) high=scalar_de62_output_value rho high.
Proof.
 unfold de62_input_value,scalar_de62_output_value;apply norm62_value_ext;intros i I.
 change (Int64.signed (de62_array (scalar_de62_next_rho rho) high i)=
   Int64.signed (scalar_de62_recurrence_word rho high i));rewrite scalar_de62_next_array by lia;reflexivity.
Qed.
Lemma scalar_de62_next_rows rho high : de62_row_bound (scalar_de62_next_rho rho) high=de62_row_bound rho high.
Proof. destruct high;reflexivity. Qed.
Lemma scalar_de62_state_bounds_next rho : (forall high,de62_row_bound rho high) -> scalar_de62_state_bounds rho ->
 scalar_de62_state_bounds (scalar_de62_next_rho rho).
Proof.
 intros Rows Bounds;split.
 - intros high i I;rewrite scalar_de62_next_array by exact I;apply scalar_de62_output_limb_bounds;[apply Rows|exact Bounds|exact I].
 - intro high;rewrite scalar_de62_next_input_value;apply scalar_de62_output_range;[apply Rows|exact Bounds].
Qed.

Lemma scalar_de62_next_limbs_den rho beta (high : bool) :
 map (den (scalar_de62_next_rho rho) beta) (map XLv (seq (if high then 5 else 0) 5))=
 map (den rho beta) (scalar_de62_limbs high).
Proof.
 apply nth_ext with (d:=Vlong Int64.zero) (d':=Vlong Int64.zero).
 - rewrite !map_length,(proj1 (scalar_de62_limbs_properties high));destruct high;reflexivity.
 - intros i I;assert (J : (i<5)%nat) by (rewrite map_length,map_length,seq_length in I;exact I).
   change (nth i (map (den (scalar_de62_next_rho rho) beta) (map XLv (seq (if high then 5 else 0) 5)))
     (den (scalar_de62_next_rho rho) beta (XLc Int64.zero))=
    nth i (map (den rho beta) (scalar_de62_limbs high)) (den rho beta (XLc Int64.zero))).
   rewrite !map_nth,scalar_de62_word_den by exact J;rewrite scalar_de62_word_recurrence by exact J.
   destruct high;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity.
Qed.

Lemma scalar_de62_call_shape : map rshape (sregs scalar_de62_state)=map rshape scalar_de62_regs.
Proof.
 rewrite scalar_de62_two_heads;cbn [map];rewrite !scalar_de62_out_shape,scalar_de62_tail;reflexivity.
Qed.

Local Opaque scalar_de62_state scalar_de62_limbs.
Lemma scalar_de62_revalue_array rho beta m (high : bool) :
 region_ok rho beta m (if high then 1 else 0)
  (mkreg (u64_cells 0 (scalar_de62_limbs high)) true (Some 40)) ->
 region_ok (scalar_de62_next_rho rho) beta m (if high then 1 else 0)
  (mkreg (u64_cells 0 (map XLv (seq (if high then 5 else 0) 5))) true (Some 40)).
Proof.
 intro Region;eapply region_u64_transport with (rho:=rho) (beta:=beta)
  (r:=if high then 1%nat else 0%nat) (xs:=scalar_de62_limbs high).
 - reflexivity.
 - rewrite (proj1 (scalar_de62_limbs_properties high));rewrite map_length,seq_length;reflexivity.
 - exact (scalar_de62_next_limbs_den rho (lay beta) high).
 - destruct high;reflexivity.
 - exact Region.
Qed.

Definition scalar_de62_result_regs :=
 [mkreg (u64_cells 0 (scalar_de62_limbs false)) true (Some 40);
  mkreg (u64_cells 0 (scalar_de62_limbs true)) true (Some 40);
  nth 2 scalar_de62_regs (mkreg [] false None);nth 3 scalar_de62_regs (mkreg [] false None)].
Lemma scalar_de62_result_regs_eq : sregs scalar_de62_state=scalar_de62_result_regs.
Proof. exact scalar_de62_output_regs. Qed.
Lemma scalar_de62_result_shape : map rshape scalar_de62_result_regs=map rshape scalar_de62_regs.
Proof. rewrite <-scalar_de62_result_regs_eq;apply scalar_de62_call_shape. Qed.

Lemma scalar_de62_revalue_matrix rho beta m :
 region_ok rho beta m 2 (nth 2 scalar_de62_regs (mkreg [] false None)) ->
 region_ok (scalar_de62_next_rho rho) beta m 2 (nth 2 scalar_de62_regs (mkreg [] false None)).
Proof.
 intro Region;eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=2%nat)
  (xs:=[XLv 10;XLv 11;XLv 12;XLv 13]) (ys:=[XLv 10;XLv 11;XLv 12;XLv 13]);
 try reflexivity;exact Region.
Qed.
Lemma scalar_de62_revalue_modinfo rho beta m :
 region_ok rho beta m 3 (nth 3 scalar_de62_regs (mkreg [] false None)) ->
 region_ok (scalar_de62_next_rho rho) beta m 3 (nth 3 scalar_de62_regs (mkreg [] false None)).
Proof.
 intro Region;eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=3%nat)
  (xs:=map XLc modinfo_scalar_words) (ys:=map XLc modinfo_scalar_words);
 try reflexivity;exact Region.
Qed.



Local Opaque scalar_de62_next_rho.
Lemma scalar_de62_revalue_result rho beta m : rep rho beta scalar_de62_result_regs m ->
 rep (scalar_de62_next_rho rho) beta scalar_de62_regs m.
Proof.
 intro Rep;destruct Rep as (Len & Sep & Regions).
 apply de62_rep_four.
 - change (length beta=4%nat) in Len;exact Len.
 - eapply (rsep_shape beta scalar_de62_result_regs scalar_de62_regs);[symmetry;apply scalar_de62_result_shape|exact Sep].
 - exact (scalar_de62_revalue_array rho beta m false (Regions 0%nat _ eq_refl)).
 - exact (scalar_de62_revalue_array rho beta m true (Regions 1%nat _ eq_refl)).
 - exact (scalar_de62_revalue_matrix rho beta m (Regions 2%nat _ eq_refl)).
 - exact (scalar_de62_revalue_modinfo rho beta m (Regions 3%nat _ eq_refl)).
Qed.

Theorem scalar_de62_revalue rho beta m : rep rho beta (sregs scalar_de62_state) m ->
 rep (scalar_de62_next_rho rho) beta scalar_de62_regs m.
Proof. rewrite scalar_de62_result_regs_eq;apply scalar_de62_revalue_result. Qed.

(** A state transformer usable by the original inverse caller: output
    representation and bounds are conclusions, not execution premises. *)
Theorem eval_scalar_de_step rho beta m : rep rho beta scalar_de62_regs m ->
 (forall high,de62_row_bound rho high) -> scalar_de62_state_bounds rho -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_update_de_62)
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
   Vptr (blk beta 2) (Ptrofs.repr (bas beta 2));Vptr (blk beta 3) (Ptrofs.repr (bas beta 3))] E0 mf Vundef /\
 rep (scalar_de62_next_rho rho) beta scalar_de62_regs mf /\
 scalar_de62_state_bounds (scalar_de62_next_rho rho) /\
 (forall high,
  2^62*de62_input_value (scalar_de62_next_rho rho) high=
   de62_matrix_value rho high+canonical_group_order*scalar_de62_correction_value rho high /\
  (2^62*de62_input_value (scalar_de62_next_rho rho) high-de62_matrix_value rho high) mod canonical_group_order=0) /\
 lframe (fun b ofs=>~foot beta (map rshape scalar_de62_regs) b ofs) m mf.
Proof.
 intros Rep Rows Bounds.
 destruct (eval_scalar_de_value rho beta m Rep Rows (scalar_de62_state_input_bound rho Bounds))
   as (mf & Call & Words & Numeric & Out & Frame).
 exists mf;split;[exact Call|];split;[apply scalar_de62_revalue;exact Out|];split.
 - apply scalar_de62_state_bounds_next;assumption.
 - split;[|exact Frame]. intro high;rewrite scalar_de62_next_input_value;exact(Numeric high).
Qed.
