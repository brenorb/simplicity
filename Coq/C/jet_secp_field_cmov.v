(** Original five-limb conditional move for the actual boolean flags.
    No canonical-value or arithmetic-bound premise is needed: selection is
    exact at the machine-word level, and both caller objects remain owned. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep
  C.jet_sx_revalue_cells C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_local_regions C.jet_secp_field_add_initial C.jet_secp_field_pair_multiply
  C.jet_secp_multiply_run_run C.jet_secp_curve_frame C.jet_secp_multiply_normalize_bridge
  C.jet_secp_b32_exec C.jet_secp_fe_b32 C.jet_secp_closed_helpers
  C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition cmov_regs := field_mul_regs.
Definition cmov_int (flag:bool) := if flag then Int.one else Int.zero.
Definition cmov_args flag := [XP 0 0;XP 1 0;XI (cmov_int flag)].
Definition cmov_state flag := match xfun (genv_cenv secp_ge) [] (int_table secp_pure) 96
  f_secp256k1_fe_cmov (cmov_args flag) cmov_regs [] 10 with
  | Some (RDone st _) => st | _=>mkst (PTree.empty sx) [] [] 0 end.
Definition cmov_mask flag := XLb Badd (XI2L Signed (XI (cmov_int flag)))
  (XLnot (XI2L Signed (XIc Int.zero))).
Definition cmov_digit flag i := XLb Bor (XLb Band (XLv i) (cmov_mask flag))
  (XLb Band (XLv (i+5)) (XLnot (cmov_mask flag))).
Definition cmov_out flag := map (cmov_digit flag) [0%nat;1%nat;2%nat;3%nat;4%nat].
Definition cmov_out_regs flag :=
  [mkreg (u64_cells 0 (cmov_out flag)) true (Some 40);free_region (fe_reg (vars5 5)) 40].

Lemma cmov_run flag : xfun (genv_cenv secp_ge) [] (int_table secp_pure) 96
  f_secp256k1_fe_cmov (cmov_args flag) cmov_regs [] 10=Some (RDone (cmov_state flag) ONormal).
Proof. destruct flag;vm_compute;reflexivity. Qed.
Lemma cmov_return flag : (stemps (cmov_state flag))!1%positive=None.
Proof. destruct flag;vm_compute;reflexivity. Qed.
Lemma cmov_output flag : sregs (cmov_state flag)=cmov_out_regs flag.
Proof. destruct flag;vm_compute;reflexivity. Qed.
Lemma cmov_digit_den flag rho beta i : den rho (lay beta) (cmov_digit flag i)=
  Vlong (if flag then rho (i+5)%nat else rho i).
Proof.
  destruct flag.
  - change (Vlong (Int64.or (Int64.and (rho i) Int64.zero)
      (Int64.and (rho (i+5)%nat) Int64.mone))=Vlong (rho (i+5)%nat)).
    rewrite Int64.and_zero,Int64.and_mone,Int64.or_zero_l;reflexivity.
  - change (Vlong (Int64.or (Int64.and (rho i) Int64.mone)
      (Int64.and (rho (i+5)%nat) Int64.zero))=Vlong (rho i)).
    rewrite Int64.and_mone,Int64.and_zero,Int64.or_zero;reflexivity.
Qed.
Lemma cmov_out_den flag a b beta : map (den (field_pair_valuation a b) (lay beta)) (cmov_out flag)=
  map Vlong (words5 (if flag then b else a)).
Proof.
  unfold cmov_out;cbn [map];rewrite !cmov_digit_den;destruct flag;reflexivity.
Qed.

Theorem eval_field_cmov_symbolic flag rho beta m : rep rho beta cmov_regs m -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_cmov)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
     Vint (cmov_int flag)] E0 mf Vundef /\
  rep rho beta (cmov_out_regs flag) mf /\
  lframe (fun b pos=>~foot beta (map rshape cmov_regs) b pos) m mf.
Proof.
  intro Rep;destruct (xfun_pure secp_ge secp_pure secp_pure_ok 96 f_secp256k1_fe_cmov
    (cmov_args flag) cmov_regs 10 _ (cmov_run flag) eq_refl rho beta m Rep)
    as (mf & result & Call & Out & Ret & Shape & Frame).
  cbn [rsel fst] in Out,Ret;rewrite cmov_return in Ret;subst result.
  change (map (den rho (lay beta)) (cmov_args flag)) with
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0));
     Vint (cmov_int flag)] in Call.
  rewrite !Z.add_0_r in Call;rewrite cmov_output in Out.
  exists mf;split;[exact Call|];split;assumption.
Qed.
Lemma cmov_result flag a b m ba bb :
  rep (field_pair_valuation a b) [(ba,0);(bb,0)] (cmov_out_regs flag) m ->
  fe_at m ba 0 (words5 (if flag then b else a)) /\ fe_at m bb 0 (words5 b) /\
  Mem.range_perm m ba 0 40 Cur Freeable /\ Mem.range_perm m bb 0 40 Cur Freeable.
Proof.
  intro Rep;pose proof (rep_region _ _ _ m 0 _ Rep eq_refl) as H0.
  pose proof (rep_region _ _ _ m 1 _ Rep eq_refl) as H1.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & FA & _).
  pose proof H1 as (_ & _ & _ & _ & _ & _ & FB & _).
  pose proof (region_ok_revalue_u64 _ _ _ 0 (cmov_out flag) true (Some 40) H0
    ltac:(destruct flag;reflexivity)) as V0.
  rewrite (revalue_u64_machine_map _ _ _ _ (cmov_out_den flag a b [(ba,0);(bb,0)])) in V0.
  pose proof (region_ok_revalue_u64 _ _ _ 1 (vars5 5) true (Some 40) H1 eq_refl) as V1.
  assert (Den1:map (den (field_pair_valuation a b) (lay [(ba,0);(bb,0)])) (vars5 5)=map Vlong (words5 b))
    by reflexivity.
  rewrite (revalue_u64_machine_map _ _ _ _ Den1) in V1.
  split;[exact (u64_region_fe_at _ _ _ 0 _ _ V0)|];
    split;[exact (u64_region_fe_at _ _ _ 1 _ _ V1)|];split;assumption.
Qed.
Lemma cmov_closed : closed_stmtb secp_closed_helpers (fn_body f_secp256k1_fe_cmov)=true.
Proof. reflexivity. Qed.
Theorem eval_field_cmov flag a b m ba bb : ba<>bb ->
  fe_at m ba 0 (words5 a) -> fe_at m bb 0 (words5 b) ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_cmov)
    [Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero;Vint (cmov_int flag)] E0 mf Vundef /\
  fe_at mf ba 0 (words5 (if flag then b else a)) /\ fe_at mf bb 0 (words5 b) /\
  Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
  lframe (fun bi _=>bi<>ba /\ bi<>bb) m mf /\ readonly_preserved m mf.
Proof.
  intros Ne A B FA FB.
  destruct (eval_field_cmov_symbolic flag (field_pair_valuation a b) [(ba,0);(bb,0)] m
    (field_pair_initial a b m ba bb Ne A B FA FB)) as (mf & Call & Rep & Frame).
  destruct (cmov_result flag a b mf ba bb Rep) as (AF & BF & FAF & FBF).
  exists mf;split;[exact Call|];split;[exact AF|];split;[exact BF|];
    split;[exact FAF|];split;[exact FBF|];split.
  - exact (curve_frame_two cmov_regs ba bb m mf eq_refl Frame).
  - eapply (secp_closed_function_preserved f_secp256k1_fe_cmov);[exact cmov_closed|reflexivity|exact Call].
Qed.
