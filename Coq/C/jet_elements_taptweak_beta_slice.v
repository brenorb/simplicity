(** Original fe_mul into a distinct field slice from a loose table coordinate
    and the actual initialized read-only beta global. No reader-shape or
    writable-global premise is imposed on the stored operands. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_toZ C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec
 C.jet_sx_mem C.jet_sx_rep C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_field_slice_product C.jet_secp_field_slice_borrowed C.jet_borrowed_region
 C.jet_secp_point_mul_run C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric
 C.jet_secp_field_mul_word_model C.jet_secp_u128_word_oracle C.jet_secp_square_columns
 C.jet_secp_field_add_initial C.jet_secp_fe_b32 C.jet_secp_b32_exec C.jet_secp_multiply_input_input
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_beta_global C.jet_secp_beta_spec C.jet_secp_beta_state
 C.jet_secp_rescale_literal C.jet_clight_internal_permissions C.jet_clight_internal_preserve
 C.jet_secp_closed_helpers C.jet_secp_slice_permissions C.jet_secp_multiply_borrowed_transport.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_beta_slice C.jet_elements_taptweak_pure C.jet_elements_taptweak_beta
 C.jet_elements_taptweak_curve_transport.
Lemma elements_taptweak_has_fe_mul:
 In(_secp256k1_fe_mul,f_secp256k1_fe_mul)elements_taptweak_curve_helpers.
Proof.
 assert(Found:find(fun it=>Pos.eqb(fst it)_secp256k1_fe_mul)elements_taptweak_curve_helpers=
 Some(_secp256k1_fe_mul,f_secp256k1_fe_mul))by(vm_compute;reflexivity).
 apply find_some in Found;exact(proj1 Found).
Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_beta_block rescale_field_output literal_fe_multiply_beta.
Lemma elements_taptweak_beta_slice_region a layout m r :
 lay layout r=(elements_taptweak_beta_block,0) -> elements_taptweak_beta_global_rep m ->
 region_ok (point_mul_valuation a beta_digits) layout m r
 (borrowed_region (fe_reg (vars5 5))).
Proof.
 intros Layout (Valid & Perm & Loads).
 assert (Block:blk layout r=elements_taptweak_beta_block) by (unfold blk;rewrite Layout;reflexivity).
 assert (Base:bas layout r=0) by (unfold bas;rewrite Layout;reflexivity).
 unfold borrowed_region;apply region_u64.
 - rewrite Base;lia.
 - rewrite Base;exists 0;reflexivity.
 - rewrite Base;change (40<=18446744073709551615);lia.
 - rewrite Block;exact Valid.
 - rewrite Block,Base;exact Perm.
 - intros i x Nth;rewrite Block,Base,Z.add_0_l.
   destruct (vars5_offset_nth 5 i x Nth) as [Bound ->];split;[|reflexivity].
   change (Mem.load Mint64 m elements_taptweak_beta_block (8*Z.of_nat i)=
    Some (Vlong (point_mul_valuation a beta_digits (5+i)%nat))).
   rewrite beta_slice_rho by exact Bound.
   apply Loads;apply nth_error_nth';rewrite beta_words_count;exact Bound.
Qed.

Lemma elements_taptweak_beta_slice_initial a m bo oo ba oa :
 field_slice_separated bo oo ba oa -> field_slice_separated bo oo elements_taptweak_beta_block 0 ->
 field_slice_separated ba oa elements_taptweak_beta_block 0 ->
 0<=oo -> (8|oo) -> oo+40<=Ptrofs.max_unsigned ->
 Mem.range_perm m bo oo (oo+40) Cur Writable -> fe_at m ba oa (words5 a) -> elements_taptweak_beta_global_rep m ->
 rep (point_mul_valuation a beta_digits) [(bo,oo);(ba,oa);(elements_taptweak_beta_block,0)] field_slice_borrowed_regs m.
Proof.
 intros OA OB AB Base Align Max Space A Global.
 assert (H0:region_ok (point_mul_valuation a beta_digits) [(bo,oo);(ba,oa);(elements_taptweak_beta_block,0)] m 0 fe_undef).
 { apply region_fe_undefined_from_storage;assumption. }
 assert (H1:region_ok (point_mul_valuation a beta_digits) [(bo,oo);(ba,oa);(elements_taptweak_beta_block,0)] m 1 (fe_reg (vars5 0))).
 { apply field_region_from_values;exact A. }
 assert (H2:region_ok (point_mul_valuation a beta_digits) [(bo,oo);(ba,oa);(elements_taptweak_beta_block,0)] m 2
   (borrowed_region (fe_reg (vars5 5)))).
 { apply elements_taptweak_beta_slice_region;[reflexivity|exact Global]. }
 split;[reflexivity|];split.
 - intros r1 r2 reg1 reg2 Different E1 E2.
   assert (B1:(r1<3)%nat) by (change (r1<length field_slice_borrowed_regs)%nat;apply nth_error_Some;congruence).
   assert (B2:(r2<3)%nat) by (change (r2<length field_slice_borrowed_regs)%nat;apply nth_error_Some;congruence).
   destruct r1 as [|[|[|r1]]],r2 as [|[|[|r2]]];try lia;
    cbn [field_slice_borrowed_regs borrow_at upd field_slice_product_regs nth_error] in E1,E2;
    injection E1 as <-;injection E2 as <-;
    apply field_slice_regions_separated;try reflexivity;
    try (repeat constructor;cbn;lia);
    cbn [blk bas lay nth fst snd];first [assumption|apply field_slice_separated_sym;assumption].
 - intros r reg Nth;destruct r as [|[|[|r]]];
    cbn [field_slice_borrowed_regs borrow_at upd field_slice_product_regs nth_error] in Nth;
    try (destruct r;discriminate);inversion Nth;subst reg;assumption.
Qed.

Theorem eval_elements_taptweak_beta_slice_product a m bo oo ba oa : square_input_bounds a ->
 field_slice_separated bo oo ba oa -> field_slice_separated bo oo elements_taptweak_beta_block 0 ->
 field_slice_separated ba oa elements_taptweak_beta_block 0 ->
 0<=oo -> (8|oo) -> oo+40<=Ptrofs.max_unsigned ->
 Mem.range_perm m bo oo (oo+40) Cur Writable -> fe_at m ba oa (words5 a) -> elements_taptweak_beta_initialized m ->
 exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_fe_mul)
  [Vptr bo (Ptrofs.repr oo);Vptr ba (Ptrofs.repr oa);Vptr elements_taptweak_beta_block Ptrofs.zero] E0 mf Vundef /\
 fe_at mf bo oo (words5 (point_mul_words a beta_digits)) /\ fe_at mf ba oa (words5 a) /\
 rescale_field_output (point_mul_words a beta_digits)=
  @literal_fe_multiply_beta Alg.CoreFunSem (rescale_field_output a) /\
 square_input_bounds (point_mul_words a beta_digits) /\ elements_taptweak_beta_initialized mf /\
 keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun bx pos=>(bx<>bo \/ pos<oo \/ oo+40<=pos) /\
  (bx<>ba \/ pos<oa \/ oa+40<=pos) /\ (bx<>elements_taptweak_beta_block \/ pos<0 \/ 40<=pos)) m mf.
Proof.
 intros Bound OA OB AB Base Align Max Space A Init.
 destruct (eval_field_slice_borrowed_symbolic (point_mul_valuation a beta_digits)
  [(bo,oo);(ba,oa);(elements_taptweak_beta_block,0)] m
  (elements_taptweak_beta_slice_initial a m bo oo ba oa OA OB AB Base Align Max Space A (proj1 Init))
  (fm_solves _ _ _ _ _ _ _ _ _ _)) as (mf & Call & Rep & Frame).
 assert (Out:fe_at mf bo oo (words5 (point_mul_words a beta_digits))).
 { eapply (field_slice_region_words (point_mul_valuation a beta_digits)
    [(bo,oo);(ba,oa);(elements_taptweak_beta_block,0)] mf 0 point_mul_out (point_mul_words a beta_digits));
   [exact (rep_region _ _ _ mf 0 _ Rep eq_refl)|reflexivity|apply point_mul_output_den]. }
 assert (AP:fe_at mf ba oa (words5 a)).
 { eapply (field_slice_region_words (point_mul_valuation a beta_digits)
    [(bo,oo);(ba,oa);(elements_taptweak_beta_block,0)] mf 1 (vars5 0) a);
   [exact (rep_region _ _ _ mf 1 _ Rep eq_refl)|reflexivity|reflexivity]. }
 assert (RO:readonly_preserved m mf).
 { eapply (secp_closed_function_preserved f_secp256k1_fe_mul);[reflexivity|reflexivity|exact Call]. }
 exists mf;split.
 { exact(elements_taptweak_curve_transport _ _ m _ _ mf _ elements_taptweak_has_fe_mul Call). }
 split;[exact Out|];split;[exact AP|];split.
 - apply beta_slice_literal;exact Bound.
 - split;[exact (proj2 (point_mul_value_and_bounds a beta_digits Bound beta_slice_bounds))|];split.
   + eapply elements_taptweak_beta_initialized_preserved;[exact Init|exact RO].
   + split.
     * eapply (secp_internal_keeps_permissions f_secp256k1_fe_mul);[reflexivity|reflexivity|exact Call].
     * split;[exact RO|].
       eapply lframe_implies;[exact Frame|].
       intros bx pos (NO & NA & NB) Valid Foot.
       apply (proj1 (foot_borrow [(bo,oo);(ba,oa);(elements_taptweak_beta_block,0)] 2 field_slice_product_regs bx pos)) in Foot.
       destruct (field_slice_product_foot [(bo,oo);(ba,oa);(elements_taptweak_beta_block,0)] bx pos Foot)
        as (r & Range & Same & Pos).
       destruct r as [|[|[|r]]];try lia;cbn [blk bas lay nth fst snd] in Same,Pos;subst bx.
       { destruct NO as[N|[L|H]];[apply N;reflexivity|lia|lia]. }
       { destruct NA as[N|[L|H]];[apply N;reflexivity|lia|lia]. }
       { destruct NB as[N|[L|H]];[apply N;reflexivity|lia|lia]. }
Qed.
