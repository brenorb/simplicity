(** Actual original fe_add_int(7), needed by both on-curve helpers. This is
    an internal execution contract, not a registered curve-jet theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_eval C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_sx_revalue_cells C.jet_secp_fns C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_field_add_initial.
Require Import C.jet_secp_fe_math.
Require Import C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_multiply_finish_product.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition add7_regs := [free_region (fe_reg (vars5 0)) 40].
Definition add7_args := [XP 0 0; XI (Int.repr 7)].
Definition add7_run := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 32
  f_secp256k1_fe_add_int add7_args add7_regs [] 5.
Definition add7_state := match add7_run with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition add7_out :=
  [XLb Badd (XLv 0) (XI2L Signed (XI (Int.repr 7))); XLv 1; XLv 2; XLv 3; XLv 4].
Definition add7_words (rho : nat -> int64) (i : nat) : int64 :=
  if Nat.eqb i 0 then Int64.add (rho 0%nat) (Int64.repr 7) else rho i.

Lemma add7_run_eq : add7_run = Some (RDone add7_state ONormal).
Proof. vm_compute; reflexivity. Qed.
Lemma add7_return : (stemps add7_state)!1%positive = None.
Proof. vm_compute; reflexivity. Qed.
Lemma add7_output_shape : sregs add7_state = [mkreg (u64_cells 0 add7_out) true (Some 40)].
Proof. vm_compute; reflexivity. Qed.

Theorem eval_field_add7_symbolic rho layout m : rep rho layout add7_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add_int)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0)); Vint (Int.repr 7)] E0 mf Vundef /\
    rep rho layout [mkreg (u64_cells 0 add7_out) true (Some 40)] mf /\
    lframe (fun b o => ~ foot layout (map rshape add7_regs) b o) m mf.
Proof.
  intro HR.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 32 f_secp256k1_fe_add_int
    add7_args add7_regs 5 _ add7_run_eq eq_refl rho layout m HR)
    as (mf & result & HC & HF & HRet & HS & HL).
  cbn [rsel fst] in HF, HRet. rewrite add7_return in HRet. subst result.
  change (map (den rho (lay layout)) add7_args) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0)); Vint (Int.repr 7)] in HC.
  rewrite Z.add_0_r in HC. rewrite add7_output_shape in HF.
  exists mf. split; [exact HC|]. split; assumption.
Qed.


Lemma add7_from_storage rho m b :
  fe_at m b 0 (field_values rho 0) -> Mem.range_perm m b 0 40 Cur Freeable ->
  rep rho [(b, 0)] add7_regs m.
Proof.
  intros HF HP. unfold add7_regs.
  apply (rep_add rho [] [] m b 0); [apply rep_nil|cbn; tauto|].
  apply region_with_freeable.
  - apply field_region_from_values. exact HF.
  - reflexivity.
  - reflexivity.
  - exact HP.
  - apply field_region_storage_size.
Qed.

Lemma add7_result_fields rho layout m :
  rep rho layout [mkreg (u64_cells 0 add7_out) true (Some 40)] m ->
  fe_at m (blk layout 0) (bas layout 0) (field_values (add7_words rho) 0) /\
  Mem.range_perm m (blk layout 0) 0 40 Cur Freeable.
Proof.
  intro HR. pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & HF & _).
  split; [|exact HF].
  pose proof (region_ok_revalue_u64 rho layout m 0 add7_out true (Some 40) H0 eq_refl) as HV.
  assert (HD : map (den rho (lay layout)) add7_out = map Vlong (field_values (add7_words rho) 0))
    by reflexivity.
  rewrite (revalue_u64_machine_map rho layout _ _ HD) in HV.
  eapply u64_region_fe_at; exact HV.
Qed.

Theorem eval_field_add7_from_storage rho m b :
  fe_at m b 0 (field_values rho 0) -> Mem.range_perm m b 0 40 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add_int)
      [Vptr b Ptrofs.zero; Vint (Int.repr 7)] E0 mf Vundef /\
    fe_at mf b 0 (field_values (add7_words rho) 0) /\
    Mem.range_perm mf b 0 40 Cur Freeable /\
    lframe (fun b' o => ~ foot [(b, 0)] (map rshape add7_regs) b' o) m mf.
Proof.
  intros HF HP.
  destruct (eval_field_add7_symbolic rho [(b, 0)] m (add7_from_storage rho m b HF HP))
    as (mf & HC & HR & HL).
  destruct (add7_result_fields rho [(b, 0)] mf HR) as [HV HFV].
  exists mf. split; [exact HC|]. split; [exact HV|]. split; assumption.
Qed.

Lemma add7_radix_value rho :
  Int64.unsigned (rho 0%nat) + 7 <= Int64.max_unsigned ->
  fe_val (Int64.unsigned (add7_words rho 0%nat))
    (Int64.unsigned (add7_words rho 1%nat))
    (Int64.unsigned (add7_words rho 2%nat))
    (Int64.unsigned (add7_words rho 3%nat))
    (Int64.unsigned (add7_words rho 4%nat)) =
  fe_val (Int64.unsigned (rho 0%nat)) (Int64.unsigned (rho 1%nat))
    (Int64.unsigned (rho 2%nat)) (Int64.unsigned (rho 3%nat))
    (Int64.unsigned (rho 4%nat)) + 7.
Proof.
  intro HB.
  assert (HL : Int64.unsigned (Int64.add (rho 0%nat) (Int64.repr 7)) =
    Int64.unsigned (rho 0%nat) + 7).
  { assert (H7 : Int64.unsigned (Int64.repr 7) = 7) by reflexivity.
    unfold Int64.add. rewrite H7.
    rewrite Int64.unsigned_repr; [reflexivity|]. pose proof (Int64.unsigned_range (rho 0%nat)). lia. }
  unfold fe_val, add7_words. cbn [Nat.eqb]. rewrite HL. ring.
Qed.

Lemma add7_radix rho :
  Int64.unsigned (rho 0%nat) + 7 <= Int64.max_unsigned ->
  radix_value (add7_words rho) = radix_value rho + 7.
Proof.
  intro HB. rewrite !radix_value_matches_normalizer.
  apply add7_radix_value; exact HB.
Qed.

Theorem eval_field_add7_small rho m b :
  fe_at m b 0 (field_values rho 0) -> Mem.range_perm m b 0 40 Cur Freeable ->
  (forall i, (i < 5)%nat -> Int64.unsigned (rho i) <
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add_int)
      [Vptr b Ptrofs.zero; Vint (Int.repr 7)] E0 mf Vundef /\
    fe_at mf b 0 (field_values (add7_words rho) 0) /\
    radix_value (add7_words rho) = radix_value rho + 7 /\
    (forall i, (i < 5)%nat -> Int64.unsigned (add7_words rho i) <= 2^60) /\
    Mem.range_perm mf b 0 40 Cur Freeable /\
    lframe (fun b' o => ~ foot [(b, 0)] (map rshape add7_regs) b' o) m mf.
Proof.
  intros HF HP HB.
  assert (HNoWrap : Int64.unsigned (rho 0%nat) + 7 <= Int64.max_unsigned).
  { pose proof (HB 0%nat ltac:(lia)) as HLow. cbn [Nat.eqb] in HLow.
    change Int64.max_unsigned with 18446744073709551615; lia. }
  destruct (eval_field_add7_from_storage rho m b HF HP) as (mf & HC & HV & HFree & HL).
  exists mf. split; [exact HC|]. split; [exact HV|].
  split; [apply add7_radix; exact HNoWrap|]. split; [|split; assumption].
  intros i HI. unfold add7_words. destruct (Nat.eqb i 0) eqn:HZ.
  - apply Nat.eqb_eq in HZ; subst i.
    unfold Int64.add.
    assert (H7 : Int64.unsigned (Int64.repr 7) = 7) by reflexivity.
    rewrite H7, Int64.unsigned_repr by (pose proof (Int64.unsigned_range_2 (rho 0%nat)); lia).
    pose proof (HB 0%nat ltac:(lia)) as HLow. cbn [Nat.eqb] in HLow. lia.
  - pose proof (HB i HI). destruct (Nat.eqb i 4); lia.
Qed.
