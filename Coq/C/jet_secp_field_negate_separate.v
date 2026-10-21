(** Actual magnitude-one fe_negate into a separate, initially uninitialized
    temporary.  This is the next call in gej_double, not a substituted copy. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_eval C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_sx_revalue_cells C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_local_regions C.jet_secp_field_add_initial C.jet_secp_b32_exec C.jet_secp_fe_b32
  C.jet_secp_multiply_normalize_bridge C.jet_secp_point_mul_storage
  C.jet_secp_field_negate_values C.jet_secp_curve_frame C.jet_secp_fe_math
  C.jet_secp_field_mul_small C.jet_secp_square_columns C.jet_secp_multiply_finish_product.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition negate_sep_regs := [free_region fe_undef 40;free_region (fe_reg (vars5 0)) 40].
Definition negate_sep_args := [XP 0 0;XP 1 0;XIc Int.one].
Definition negate_sep_expr i := XLb Bsub
  (XLb Bmul (XLb Bmul (XLc (Int64.repr (negate_mask i))) (XI2L Signed (XIc (Int.repr 2))))
    (XI2L Signed (XIb Badd (XIc Int.one) (XIc Int.one)))) (XLv i).
Definition negate_sep_out := map negate_sep_expr [0;1;2;3;4]%nat.
Definition negate_sep_words (w : nat -> int64) i := Int64.sub (Int64.repr (4*negate_mask i)) (w i).
Definition negate_sep_run := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 160
  f_secp256k1_fe_negate negate_sep_args negate_sep_regs [] 5.
Definition negate_sep_tree := Eval vm_compute in negate_sep_run.
Definition negate_sep_state := match negate_sep_tree with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition negate_sep_out_regs :=
  [mkreg (u64_cells 0 negate_sep_out) true (Some 40);free_region (fe_reg (vars5 0)) 40].

Lemma negate_sep_run_eq : negate_sep_run=Some (RDone negate_sep_state ONormal).
Proof. reflexivity. Qed.
Lemma negate_sep_return : (stemps negate_sep_state)!1%positive=None.
Proof. reflexivity. Qed.
Lemma negate_sep_output_shape : sregs negate_sep_state=negate_sep_out_regs.
Proof. reflexivity. Qed.
Lemma negate_sep_output_den rho beta :
  map (den rho (lay beta)) negate_sep_out=map Vlong (words5 (negate_sep_words rho)).
Proof. reflexivity. Qed.

Theorem eval_negate_sep_symbolic rho beta m : rep rho beta negate_sep_regs m ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
     Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));Vint Int.one] E0 mf Vundef /\
  rep rho beta negate_sep_out_regs mf /\
  lframe (fun b pos => ~foot beta (map rshape negate_sep_regs) b pos) m mf.
Proof.
  intro HR.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 160 f_secp256k1_fe_negate
    negate_sep_args negate_sep_regs 5 _ negate_sep_run_eq eq_refl rho beta m HR)
    as (mf & result & HC & HP & HV & HS & HL).
  cbn [rsel fst] in HP,HV;rewrite negate_sep_return in HV;subst result.
  change (map (den rho (lay beta)) negate_sep_args) with
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));
     Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0));Vint Int.one] in HC.
  rewrite !Z.add_0_r in HC;rewrite negate_sep_output_shape in HP.
  exists mf;split;[exact HC|];split;assumption.
Qed.

Lemma negate_sep_initial w m bout bin : bout<>bin ->
  Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin 0 (words5 w) -> Mem.range_perm m bin 0 40 Cur Freeable ->
  rep w [(bout,0);(bin,0)] negate_sep_regs m.
Proof.
  intros HNe HO HI HF;apply two_region_rep_separate;[reflexivity|exact HNe| |].
  - apply region_with_freeable.
    + apply region_fe_undefined_from_storage;cbn [bas blk lay nth fst snd].
      * lia.
      * exists 0;reflexivity.
      * change (40<=18446744073709551615);lia.
      * apply freeable_range_writable;exact HO.
    + reflexivity.
    + reflexivity.
    + exact HO.
    + apply fe_undef_storage_size.
  - apply region_with_freeable.
    + apply field_region_from_values;exact HI.
    + reflexivity.
    + reflexivity.
    + exact HF.
    + apply field_region_storage_size.
Qed.

Lemma negate_sep_fields w beta m : rep w beta negate_sep_out_regs m ->
  fe_at m (blk beta 0) (bas beta 0) (words5 (negate_sep_words w)) /\
  fe_at m (blk beta 1) (bas beta 1) (words5 w) /\
  Mem.range_perm m (blk beta 0) 0 40 Cur Freeable /\
  Mem.range_perm m (blk beta 1) 0 40 Cur Freeable.
Proof.
  intro HR.
  pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof (rep_region _ _ _ m 1 _ HR eq_refl) as H1.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & HF0 & _).
  pose proof H1 as (_ & _ & _ & _ & _ & _ & HF1 & _).
  pose proof (region_ok_revalue_u64 w beta m 0 negate_sep_out true (Some 40) H0 eq_refl) as V0.
  rewrite (revalue_u64_machine_map _ _ _ _ (negate_sep_output_den w beta)) in V0.
  pose proof (region_ok_revalue_u64 w beta m 1 (vars5 0) true (Some 40) H1 eq_refl) as V1.
  assert (HD : map (den w (lay beta)) (vars5 0)=map Vlong (words5 w)) by reflexivity.
  rewrite (revalue_u64_machine_map _ _ _ _ HD) in V1.
  split;[exact (u64_region_fe_at _ _ _ _ _ _ V0)|].
  split;[exact (u64_region_fe_at _ _ _ _ _ _ V1)|];split;assumption.
Qed.

Lemma negate_sep_unsigned w : mul_small_input_bounds w ->
  forall i, (i<5)%nat ->
  Int64.unsigned (negate_sep_words w i)=4*negate_mask i-Int64.unsigned (w i).
Proof.
  intros HB i HI;unfold negate_sep_words;apply unsigned_sub_constant.
  - destruct (negate_mask_range i HI) as [H|[_ H]];lia.
  - pose proof (HB i HI).
    destruct i as [|[|[|[|[|i]]]]];try lia;cbn [Nat.eqb negate_mask] in *;lia.
Qed.

Lemma negate_sep_numeric w : mul_small_input_bounds w ->
  radix_value (negate_sep_words w)=4*feP-radix_value w /\
  square_input_bounds (negate_sep_words w).
Proof.
  intro HB;split.
  - rewrite !radix_value_matches_normalizer;unfold fe_val.
    rewrite !negate_sep_unsigned by (assumption || lia).
    unfold negate_mask,feP,feR;ring.
  - intros i HI;rewrite negate_sep_unsigned by assumption.
    pose proof (Int64.unsigned_range_2 (w i)).
    destruct i as [|[|[|[|[|i]]]]];try lia;cbn [Nat.eqb negate_mask] in *;lia.
Qed.

Theorem eval_negate_sep_from_storage w m bout bin :
  mul_small_input_bounds w -> bout<>bin -> Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin 0 (words5 w) -> Mem.range_perm m bin 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
    [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero;Vint Int.one] E0 mf Vundef /\
  fe_at mf bout 0 (words5 (negate_sep_words w)) /\ fe_at mf bin 0 (words5 w) /\
  Mem.range_perm mf bout 0 40 Cur Freeable /\ Mem.range_perm mf bin 0 40 Cur Freeable /\
  radix_value (negate_sep_words w)=4*feP-radix_value w /\
  square_input_bounds (negate_sep_words w) /\
  lframe (fun b _ => b<>bout /\ b<>bin) m mf.
Proof.
  intros HB HNe HO HI HF.
  destruct (eval_negate_sep_symbolic w [(bout,0);(bin,0)] m (negate_sep_initial w m bout bin HNe HO HI HF))
    as (mf & HC & HP & HL).
  destruct (negate_sep_fields w [(bout,0);(bin,0)] mf HP) as (FO & FI & FOF & FIF).
  destruct (negate_sep_numeric w HB) as [HV HBounds].
  exists mf;split;[exact HC|];split;[exact FO|];split;[exact FI|];
    split;[exact FOF|];split;[exact FIF|];split;[exact HV|];split;[exact HBounds|].
  exact (curve_frame_two negate_sep_regs bout bin m mf eq_refl HL).
Qed.
