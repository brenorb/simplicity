(** Actual fe_mul_int(7), with exact machine limbs, value and bounds needed by
    the projective curve checker.  No field-normalization call is inserted. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_eval C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_sx_revalue_cells C.jet_secp_fns C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_field_add_initial C.jet_secp_fe_math.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_curve_frame.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition mul7_regs := [free_region (fe_reg (vars5 0)) 40].
Definition mul7_args := [XP 0 0; XI (Int.repr 7)].
Definition mul7_run := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 64
  f_secp256k1_fe_mul_int mul7_args mul7_regs [] 5.
Definition mul7_state := match mul7_run with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition mul7_out := map (fun x => XLb Bmul x (XI2L Signed (XI (Int.repr 7)))) (vars5 0).
Definition mul7_words (rho : nat -> int64) (i : nat) : int64 := Int64.mul (rho i) (Int64.repr 7).

Lemma mul7_run_eq : mul7_run = Some (RDone mul7_state ONormal).
Proof. reflexivity. Qed.
Lemma mul7_return : (stemps mul7_state)!1%positive = None.
Proof. reflexivity. Qed.
Lemma mul7_output_shape : sregs mul7_state = [mkreg (u64_cells 0 mul7_out) true (Some 40)].
Proof. reflexivity. Qed.

Theorem eval_field_mul7_symbolic rho layout m : rep rho layout mul7_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul_int)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0)); Vint (Int.repr 7)] E0 mf Vundef /\
    rep rho layout [mkreg (u64_cells 0 mul7_out) true (Some 40)] mf /\
    lframe (fun b o => ~ foot layout (map rshape mul7_regs) b o) m mf.
Proof.
  intro HR.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 64 f_secp256k1_fe_mul_int
    mul7_args mul7_regs 5 _ mul7_run_eq eq_refl rho layout m HR)
    as (mf & result & HC & HF & HRet & HS & HL).
  cbn [rsel fst] in HF,HRet. rewrite mul7_return in HRet;subst result.
  change (map (den rho (lay layout)) mul7_args) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0+0));Vint (Int.repr 7)] in HC.
  rewrite Z.add_0_r in HC;rewrite mul7_output_shape in HF.
  exists mf;split;[exact HC|];split;assumption.
Qed.

Lemma mul7_initial rho m b :
  fe_at m b 0 (words5 rho) -> Mem.range_perm m b 0 40 Cur Freeable -> rep rho [(b,0)] mul7_regs m.
Proof.
  intros HI HF. apply (rep_add rho [] [] m b 0);[apply rep_nil|cbn;tauto|].
  apply region_with_freeable.
  - apply field_region_from_values;exact HI.
  - reflexivity.
  - reflexivity.
  - exact HF.
  - apply field_region_storage_size.
Qed.

Lemma mul7_result rho layout m :
  rep rho layout [mkreg (u64_cells 0 mul7_out) true (Some 40)] m ->
  fe_at m (blk layout 0) (bas layout 0) (words5 (mul7_words rho)) /\
  Mem.range_perm m (blk layout 0) 0 40 Cur Freeable.
Proof.
  intro HR;pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & HF & _).
  split;[|exact HF].
  pose proof (region_ok_revalue_u64 rho layout m 0 mul7_out true (Some 40) H0 eq_refl) as HV.
  assert (HD : map (den rho (lay layout)) mul7_out = map Vlong (words5 (mul7_words rho))) by reflexivity.
  rewrite (revalue_u64_machine_map rho layout _ _ HD) in HV.
  exact (u64_region_fe_at _ _ _ _ _ _ HV).
Qed.

Lemma mul7_unsigned rho :
  (forall i, (i<5)%nat -> Int64.unsigned (rho i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
  forall i, (i<5)%nat -> Int64.unsigned (mul7_words rho i)=7*Int64.unsigned (rho i).
Proof.
  intros HB i HI. unfold mul7_words,Int64.mul.
  change (Int64.unsigned (Int64.repr 7)) with 7.
  rewrite Int64.unsigned_repr;[ring|].
  pose proof (HB i HI);pose proof (Int64.unsigned_range_2 (rho i)).
  change Int64.max_unsigned with 18446744073709551615.
  destruct (Nat.eqb i 4);lia.
Qed.

Lemma mul7_radix rho :
  (forall i, (i<5)%nat -> Int64.unsigned (rho i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
  radix_value (mul7_words rho)=7*radix_value rho.
Proof.
  intro HB;rewrite !radix_value_matches_normalizer;unfold fe_val.
  rewrite (mul7_unsigned rho HB 0%nat ltac:(lia)),(mul7_unsigned rho HB 1%nat ltac:(lia)),
    (mul7_unsigned rho HB 2%nat ltac:(lia)),(mul7_unsigned rho HB 3%nat ltac:(lia)),
    (mul7_unsigned rho HB 4%nat ltac:(lia));ring.
Qed.

Theorem eval_field_mul7_from_storage rho m b :
  (forall i, (i<5)%nat -> Int64.unsigned (rho i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
  fe_at m b 0 (words5 rho) -> Mem.range_perm m b 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul_int)
    [Vptr b Ptrofs.zero;Vint (Int.repr 7)] E0 mf Vundef /\
  fe_at mf b 0 (words5 (mul7_words rho)) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
  radix_value (mul7_words rho)=7*radix_value rho /\
  (forall i, (i<5)%nat -> Int64.unsigned (mul7_words rho i)<
    if Nat.eqb i 4 then 3940649673949184 else 31525197391593472) /\
  lframe (fun bx _ => bx<>b) m mf.
Proof.
  intros HB HI HF.
  destruct (eval_field_mul7_symbolic rho [(b,0)] m (mul7_initial rho m b HI HF))
    as (mf & HC & HR & HL).
  destruct (mul7_result rho [(b,0)] mf HR) as [FO FF].
  exists mf;split;[exact HC|]. split;[exact FO|]. split;[exact FF|].
  split;[apply mul7_radix;exact HB|]. split.
  - intros i HIndex;rewrite mul7_unsigned by assumption.
    pose proof (HB i HIndex);destruct (Nat.eqb i 4);lia.
  - exact (curve_frame_one mul7_regs b m mf eq_refl HL).
Qed.
