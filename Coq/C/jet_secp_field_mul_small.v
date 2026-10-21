(** Original fe_mul_int with a reusable small nonnegative multiplier. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_eval C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_sx_revalue_cells C.jet_secp_fns C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_field_add_initial C.jet_secp_fe_math.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_curve_frame C.jet_secp_square_columns.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition mul_small_regs := [free_region (fe_reg (vars5 0)) 40].
Definition mul_small_args (c : int) := [XP 0 0;XI c].
Definition mul_small_run c := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 64
  f_secp256k1_fe_mul_int (mul_small_args c) mul_small_regs [] 5.
Definition mul_small_state c := match mul_small_run c with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition mul_small_out c := map (fun x => XLb Bmul x (XI2L Signed (XI c))) (vars5 0).
Definition mul_small_words c (rho : nat -> int64) i := Int64.mul (rho i) (Int64.repr (Int.signed c)).
Definition mul_small_input_bounds (rho : nat -> int64) :=
  forall i, (i<5)%nat -> Int64.unsigned (rho i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496.

Lemma mul_small_run_eq c : mul_small_run c=Some (RDone (mul_small_state c) ONormal).
Proof. reflexivity. Qed.
Lemma mul_small_return c : (stemps (mul_small_state c))!1%positive=None.
Proof. reflexivity. Qed.
Lemma mul_small_output_shape c :
  sregs (mul_small_state c)=[mkreg (u64_cells 0 (mul_small_out c)) true (Some 40)].
Proof. reflexivity. Qed.
Lemma mul_small_output_den c rho layout :
  map (den rho (lay layout)) (mul_small_out c)=map Vlong (words5 (mul_small_words c rho)).
Proof. reflexivity. Qed.

Theorem eval_field_mul_small_symbolic c rho layout m : rep rho layout mul_small_regs m ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul_int)
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));Vint c] E0 mf Vundef /\
  rep rho layout [mkreg (u64_cells 0 (mul_small_out c)) true (Some 40)] mf /\
  lframe (fun b pos => ~foot layout (map rshape mul_small_regs) b pos) m mf.
Proof.
  intro HR.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 64 f_secp256k1_fe_mul_int
    (mul_small_args c) mul_small_regs 5 _ (mul_small_run_eq c) eq_refl rho layout m HR)
    as (mf & result & HC & HP & HV & HS & HL).
  cbn [rsel fst] in HP,HV;rewrite mul_small_return in HV;subst result.
  change (map (den rho (lay layout)) (mul_small_args c)) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0+0));Vint c] in HC.
  rewrite Z.add_0_r in HC;rewrite mul_small_output_shape in HP.
  exists mf;split;[exact HC|];split;assumption.
Qed.

Lemma mul_small_initial rho m b :
  fe_at m b 0 (words5 rho) -> Mem.range_perm m b 0 40 Cur Freeable ->
  rep rho [(b,0)] mul_small_regs m.
Proof.
  intros HI HF;apply (rep_add rho [] [] m b 0);[apply rep_nil|cbn;tauto|].
  apply region_with_freeable.
  - apply field_region_from_values;exact HI.
  - reflexivity.
  - reflexivity.
  - exact HF.
  - apply field_region_storage_size.
Qed.

Lemma mul_small_result c rho layout m :
  rep rho layout [mkreg (u64_cells 0 (mul_small_out c)) true (Some 40)] m ->
  fe_at m (blk layout 0) (bas layout 0) (words5 (mul_small_words c rho)) /\
  Mem.range_perm m (blk layout 0) 0 40 Cur Freeable.
Proof.
  intro HR;pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & HF & _).
  pose proof (region_ok_revalue_u64 rho layout m 0 (mul_small_out c) true (Some 40) H0 eq_refl) as HV.
  rewrite (revalue_u64_machine_map _ _ _ _ (mul_small_output_den c rho layout)) in HV.
  split;[exact (u64_region_fe_at _ _ _ _ _ _ HV)|exact HF].
Qed.

Lemma mul_small_unsigned c rho : 0<=Int.signed c<=7 -> mul_small_input_bounds rho ->
  forall i, (i<5)%nat ->
  Int64.unsigned (mul_small_words c rho i)=Int.signed c*Int64.unsigned (rho i).
Proof.
  intros HC HB i HI;unfold mul_small_words,Int64.mul.
  rewrite (Int64.unsigned_repr (Int.signed c)) by
    (change Int64.max_unsigned with 18446744073709551615;lia).
  rewrite Int64.unsigned_repr;[ring|].
  pose proof (HB i HI);pose proof (Int64.unsigned_range_2 (rho i)).
  change Int64.max_unsigned with 18446744073709551615.
  destruct (Nat.eqb i 4);nia.
Qed.

Lemma mul_small_radix c rho : 0<=Int.signed c<=7 -> mul_small_input_bounds rho ->
  radix_value (mul_small_words c rho)=Int.signed c*radix_value rho.
Proof.
  intros HC HB;rewrite !radix_value_matches_normalizer;unfold fe_val.
  rewrite (mul_small_unsigned c rho HC HB 0%nat ltac:(lia)),
    (mul_small_unsigned c rho HC HB 1%nat ltac:(lia)),
    (mul_small_unsigned c rho HC HB 2%nat ltac:(lia)),
    (mul_small_unsigned c rho HC HB 3%nat ltac:(lia)),
    (mul_small_unsigned c rho HC HB 4%nat ltac:(lia));ring.
Qed.

Lemma mul_small_output_bounds c rho : 0<=Int.signed c<=7 -> mul_small_input_bounds rho ->
  square_input_bounds (mul_small_words c rho).
Proof.
  intros HC HB i HI;rewrite mul_small_unsigned by assumption.
  pose proof (HB i HI);pose proof (Int64.unsigned_range_2 (rho i)).
  destruct (Nat.eqb i 4);nia.
Qed.

Theorem eval_field_mul_small_from_storage c rho m b :
  0<=Int.signed c<=7 -> mul_small_input_bounds rho ->
  fe_at m b 0 (words5 rho) -> Mem.range_perm m b 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul_int)
    [Vptr b Ptrofs.zero;Vint c] E0 mf Vundef /\
  fe_at mf b 0 (words5 (mul_small_words c rho)) /\
  Mem.range_perm mf b 0 40 Cur Freeable /\
  radix_value (mul_small_words c rho)=Int.signed c*radix_value rho /\
  square_input_bounds (mul_small_words c rho) /\
  lframe (fun bx _ => bx<>b) m mf.
Proof.
  intros HC HB HI HF.
  destruct (eval_field_mul_small_symbolic c rho [(b,0)] m (mul_small_initial rho m b HI HF))
    as (mf & HCall & HP & HL).
  destruct (mul_small_result c rho [(b,0)] mf HP) as [HO HFree].
  exists mf;split;[exact HCall|];split;[exact HO|];split;[exact HFree|];
    split;[apply mul_small_radix;assumption|];
    split;[apply mul_small_output_bounds;assumption|].
  exact (curve_frame_one mul_small_regs b m mf eq_refl HL).
Qed.
