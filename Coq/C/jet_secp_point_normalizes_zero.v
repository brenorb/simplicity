(** Original variable-time zero-mod-p test on an owned point coordinate,
    including its early return.  Reuse the checked zero-test arithmetic. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_eval C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep C.jet_sx_zval.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_local_regions C.jet_secp_curve_zero C.jet_secp_curve_weak C.jet_secp_curve_weak_math
  C.jet_secp_curve_zero_math C.jet_secp_point_write_run C.jet_secp_point_write_initial
  C.jet_secp_point_write_preservation C.jet_secp_owned_slice_fields C.jet_secp_write_fe_wide_values
  C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition point_normz_run k := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 300
  f_secp256k1_fe_normalizes_to_zero_var [XP 0 (point_coordinate_offset k)] (point_write_initial_regs k) [] 6.
Definition point_normz_tree := Eval vm_compute in fun k => match k with
  | PointX => point_normz_run PointX | PointY => point_normz_run PointY | PointZ => point_normz_run PointZ end.
Definition point_normz_early k := match point_normz_tree k with
  | Some (RIf _ (RDone st _) _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition point_normz_late k := match point_normz_tree k with
  | Some (RIf _ _ (RDone st _)) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Lemma point_normz_run_eq k : point_normz_run k=
  Some (RIf curve_zero_cond (RDone (point_normz_early k) ONormal) (RDone (point_normz_late k) ONormal)).
Proof. destruct k;reflexivity. Qed.
Lemma point_normz_logs k : leaves_log_nil
  (RIf curve_zero_cond (RDone (point_normz_early k) ONormal) (RDone (point_normz_late k) ONormal))=true.
Proof. destruct k;reflexivity. Qed.
Lemma point_normz_returns k : (stemps (point_normz_early k))!1%positive=Some (XIc Int.zero) /\
  (stemps (point_normz_late k))!1%positive=Some curve_zero_ret.
Proof. destruct k;split;reflexivity. Qed.
Lemma point_normz_regions k : sregs (point_normz_early k)=point_write_initial_regs k /\
  sregs (point_normz_late k)=point_write_initial_regs k.
Proof. destruct k;split;reflexivity. Qed.

Theorem eval_point_normz_symbolic k rho beta m : rep rho beta (point_write_initial_regs k) m ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalizes_to_zero_var)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+point_coordinate_offset k))] E0 mf
    (if truth rho (lay beta) curve_zero_cond then Vint Int.zero else den rho (lay beta) curve_zero_ret) /\
  rep rho beta (point_write_initial_regs k) mf /\
  lframe (fun b pos => ~foot beta (map rshape (point_write_initial_regs k)) b pos) m mf.
Proof.
  intro HR.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 300 f_secp256k1_fe_normalizes_to_zero_var
    [XP 0 (point_coordinate_offset k)] (point_write_initial_regs k) 6 _
    (point_normz_run_eq k) (point_normz_logs k) rho beta m HR)
    as (mf & result & HC & HP & HV & HS & HL).
  change (map (den rho (lay beta)) [XP 0 (point_coordinate_offset k)]) with
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+point_coordinate_offset k))] in HC.
  cbn [rsel fst] in HP,HV.
  destruct (truth rho (lay beta) curve_zero_cond) eqn:HB;cbn [fst] in HP,HV.
  - rewrite (proj1 (point_normz_returns k)) in HV;subst result.
    rewrite (proj1 (point_normz_regions k)) in HP;exists mf;split;[exact HC|];split;assumption.
  - rewrite (proj2 (point_normz_returns k)) in HV;subst result.
    rewrite (proj2 (point_normz_regions k)) in HP;exists mf;split;[exact HC|];split;assumption.
Qed.

Lemma point_normz_value rho beta :
  (forall n, (1<=n<=5)%nat -> Int64.unsigned (rho n)<=2^60) ->
  (if truth rho (lay beta) curve_zero_cond then Vint Int.zero else den rho (lay beta) curve_zero_ret)=
  Vint (if Z.eqb (fe_val (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
    (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat)) (Int64.unsigned (rho 5%nat)) mod feP) 0
    then Int.one else Int.zero).
Proof.
  intro HB;pose proof (curve_weak_bounds_holds rho HB) as HBAll.
  destruct curve_zero_checked as (HRC & HRK & HCC & HCK).
  pose proof (truth_zval rho curve_weak_bounds (lay beta) HBAll curve_zero_cond 0 1 HCC HCK) as HTruth.
  destruct (den_zval_int rho curve_weak_bounds (lay beta) HBAll curve_zero_ret 0 1 HRC HRK) as [HRet _].
  rewrite curve_zero_cond_zval,curve_b2z_truth in HTruth;rewrite curve_zero_ret_zval in HRet.
  assert (HRange : forall n, (1<=n<=5)%nat -> 0<=Int64.unsigned (rho n)<=2^60).
  { intros n HN;split;[apply Int64.unsigned_range_2|apply HB;exact HN]. }
  pose proof (curve_zero_math_numeric (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
    (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat)) (Int64.unsigned (rho 5%nat))
    (HRange 1%nat ltac:(lia)) (HRange 2%nat ltac:(lia)) (HRange 3%nat ltac:(lia))
    (HRange 4%nat ltac:(lia)) (HRange 5%nat ltac:(lia))) as HM.
  rewrite HTruth,HRet;rewrite <-HM;unfold zrho.
  destruct (curve_zero_fast (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 5%nat)));[reflexivity|].
  destruct (curve_weak_math (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
    (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat)) (Int64.unsigned (rho 5%nat))) as [[[[a b] c] d] e].
  destruct (curve_zero_test a b c d e);reflexivity.
Qed.

Lemma point_normz_fields k w beta m :
  rep (wide_fe_rho (w 0%nat) (w 1%nat) (w 2%nat) (w 3%nat) (w 4%nat) 0) beta (point_write_initial_regs k) m ->
  fe_at m (blk beta 0) (point_coordinate_offset k) (words5 w) /\
  Mem.range_perm m (blk beta 0) 0 128 Cur Freeable.
Proof.
  intro HR;pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & HF & _);split;[|exact HF].
  eapply owned_region_field_slice with (exprs:=vars5 1) (size:=128);
    [exact H0|destruct k;cbn;lia|destruct k;cbn;[exists 0|exists 5|exists 10];reflexivity|
     pose proof (point_coordinate_offset_bounds k);lia|
     change (128<=18446744073709551615);lia|reflexivity|reflexivity| |].
  - intros c HC;exact HC.
  - reflexivity.
Qed.

Theorem eval_point_normalizes_zero k w m b :
  square_input_bounds w -> fe_at m b (point_coordinate_offset k) (words5 w) ->
  Mem.range_perm m b 0 128 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalizes_to_zero_var)
    [Vptr b (Ptrofs.repr (point_coordinate_offset k))] E0 mf
    (Vint (if Z.eqb (radix_value w mod feP) 0 then Int.one else Int.zero)) /\
  fe_at mf b (point_coordinate_offset k) (words5 w) /\ Mem.range_perm mf b 0 128 Cur Freeable /\
  lframe (fun bx pos => bx<>b \/ pos<point_coordinate_offset k \/ point_coordinate_offset k+40<=pos) m mf.
Proof.
  intros HB HI HF.
  set (rho := wide_fe_rho (w 0%nat) (w 1%nat) (w 2%nat) (w 3%nat) (w 4%nat) 0).
  pose proof (point_write_initial_rep k (w 0%nat) (w 1%nat) (w 2%nat) (w 3%nat) (w 4%nat) 0 m b HI HF) as HR.
  destruct (eval_point_normz_symbolic k rho [(b,0)] m HR) as (mf & HC & HP & HL).
  assert (HB60 : forall n, (1<=n<=5)%nat -> Int64.unsigned (rho n)<=2^60).
  { intros n HN;destruct n as [|[|[|[|[|[|n]]]]]];try lia;
      cbn [rho wide_fe_rho rho5 nth];
      match goal with |- Int64.unsigned (w ?i)<=_ =>
        pose proof (HB i ltac:(lia)) as HBi;cbn [Nat.eqb] in HBi;
        change (2^60) with 1152921504606846976;lia
      end. }
  rewrite (point_normz_value rho [(b,0)] HB60) in HC.
  change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalizes_to_zero_var)
    [Vptr b (Ptrofs.repr (point_coordinate_offset k))] E0 mf
    (Vint (if Z.eqb (fe_val (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
      (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat)) mod feP) 0
      then Int.one else Int.zero))) in HC.
  rewrite <-(radix_value_matches_normalizer w) in HC.
  destruct (point_normz_fields k w [(b,0)] mf HP) as [FO FF].
  exists mf;split;[exact HC|];split;[exact FO|];split;[exact FF|].
  eapply lframe_implies;[exact HL|]. intros bx pos HO HV HFoot.
  destruct (point_write_foot_bounds k b bx pos HFoot) as [HE HP'];subst bx.
  destruct HO as [HN|[HN|HN]];[contradiction|lia|lia].
Qed.
