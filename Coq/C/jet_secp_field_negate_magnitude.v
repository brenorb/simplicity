(** The original in-place fe_negate with its actual magnitude argument.
    Execution retains machine arithmetic for every int. Numeric conclusions
    for magnitudes 0..7 discharge subtraction bounds separately; in particular
    magnitude 3 applies after SWU's multiply-by-3, without normalization or
    substituting a magnitude-one helper. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_eval C.jet_sx_pure
  C.jet_sx_mem C.jet_sx_rep C.jet_sx_revalue_cells C.jet_secp_fns C.jet_secp_linkage
  C.jets_secp C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_field_add_initial
  C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_field_mul_small C.jet_secp_curve_frame C.jet_secp_square_columns
  C.jet_secp_field_negate_values C.jet_secp_div62_numeric.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition negate_mag_regs := mul_small_regs.
Definition negate_mag_args (c:int) := [XP 0 0;XP 0 0;XI c].
Definition negate_mag_state (c:int) := match
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 160
    f_secp256k1_fe_negate (negate_mag_args c) negate_mag_regs [] 5 with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition negate_mag_expr c i := XLb Bsub
  (XLb Bmul (XLb Bmul (XLc (Int64.repr (negate_mask i))) (XI2L Signed (XIc (Int.repr 2))))
    (XI2L Signed (XIb Badd (XI c) (XIc Int.one)))) (XLv i).
Definition negate_mag_out c := map (negate_mag_expr c) [0;1;2;3;4]%nat.
Definition negate_mag_machine_constant (c:int) i :=
  Int64.mul (Int64.mul (Int64.repr (negate_mask i)) (Int64.repr 2))
    (Int64.repr (Int.signed (Int.add c Int.one))).
Definition negate_mag_words c (w:nat->int64) i :=
  Int64.sub (negate_mag_machine_constant c i) (w i).
Definition negate_mag_input_bounds c (w:nat->int64) :=
  forall i,(i<5)%nat -> Int64.unsigned (w i)<=2*(Int.signed c+1)*negate_mask i.

Lemma negate_mag_run c :
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 160
    f_secp256k1_fe_negate (negate_mag_args c) negate_mag_regs [] 5=
    Some (RDone (negate_mag_state c) ONormal).
Proof. reflexivity. Qed.
Lemma negate_mag_output c :
  sregs (negate_mag_state c)=[mkreg (u64_cells 0 (negate_mag_out c)) true (Some 40)].
Proof. reflexivity. Qed.
Lemma negate_mag_return c : (stemps (negate_mag_state c))!1%positive=None.
Proof. reflexivity. Qed.
Lemma negate_mag_output_den c w beta :
  map (den w (lay beta)) (negate_mag_out c)=map Vlong (words5 (negate_mag_words c w)).
Proof. reflexivity. Qed.

Lemma negate_mag_constant c i : 0<=Int.signed c<=7 ->
  negate_mag_machine_constant c i=Int64.repr (2*(Int.signed c+1)*negate_mask i).
Proof.
  intro C;unfold negate_mag_machine_constant.
  rewrite !div62_repr_mul,Int.add_signed;change (Int.signed Int.one) with 1.
  rewrite Int.signed_repr by (change Int.min_signed with (-2147483648);
    change Int.max_signed with 2147483647;lia).
  f_equal;ring.
Qed.
Lemma negate_mag_unsigned c w i : 0<=Int.signed c<=7 -> (i<5)%nat ->
  Int64.unsigned (w i)<=2*(Int.signed c+1)*negate_mask i ->
  Int64.unsigned (negate_mag_words c w i)=2*(Int.signed c+1)*negate_mask i-Int64.unsigned (w i).
Proof.
  intros C Index Bound;unfold negate_mag_words;rewrite negate_mag_constant by exact C.
  apply unsigned_sub_constant;[|exact Bound].
  destruct i as [|[|[|[|[|i]]]]];try lia;cbn [negate_mask];
    change Int64.max_unsigned with 18446744073709551615;nia.
Qed.
Lemma negate_mag_numeric c w : 0<=Int.signed c<=7 -> negate_mag_input_bounds c w ->
  radix_value (negate_mag_words c w)=2*(Int.signed c+1)*feP-radix_value w /\
  square_input_bounds (negate_mag_words c w).
Proof.
  intros C Bound;split.
  - rewrite !radix_value_matches_normalizer;unfold fe_val.
    rewrite !negate_mag_unsigned by solve [exact C|apply Bound;lia|lia].
    unfold negate_mask,feP,feR;ring.
  - intros i Index;rewrite negate_mag_unsigned by
      solve [exact C|exact Index|apply Bound;exact Index].
    pose proof (Int64.unsigned_range_2 (w i)).
    destruct i as [|[|[|[|[|i]]]]];try lia;cbn [Nat.eqb negate_mask];nia.
Qed.
Lemma negate_mag_scaled_input c w : 0<=Int.signed c<=7 -> mul_small_input_bounds w ->
  negate_mag_input_bounds c (mul_small_words c w).
Proof.
  intros C Bounds i Index;rewrite mul_small_unsigned by assumption.
  pose proof (Bounds i Index);pose proof (Int64.unsigned_range_2 (w i)).
  destruct i as [|[|[|[|[|i]]]]];try lia;cbn [Nat.eqb negate_mask] in *;nia.
Qed.

Theorem eval_negate_mag_symbolic c w beta m : rep w beta negate_mag_regs m -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
     Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vint c] E0 mf Vundef /\
  rep w beta [mkreg (u64_cells 0 (negate_mag_out c)) true (Some 40)] mf /\
  lframe (fun b pos=>~foot beta (map rshape negate_mag_regs) b pos) m mf.
Proof.
  intro HR;destruct (xfun_pure secp_ge secp_pure secp_pure_ok 160 f_secp256k1_fe_negate
    (negate_mag_args c) negate_mag_regs 5 _ (negate_mag_run c) eq_refl w beta m HR)
    as (mf & result & Call & Rep & Ret & Shape & Frame).
  cbn [rsel fst] in Rep,Ret;rewrite negate_mag_return in Ret;subst result.
  change (map (den w (lay beta)) (negate_mag_args c)) with
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));
     Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));Vint c] in Call.
  rewrite Z.add_0_r in Call;rewrite negate_mag_output in Rep.
  exists mf;split;[exact Call|];split;assumption.
Qed.
Lemma negate_mag_result c w beta m :
  rep w beta [mkreg (u64_cells 0 (negate_mag_out c)) true (Some 40)] m ->
  fe_at m (blk beta 0) (bas beta 0) (words5 (negate_mag_words c w)) /\
  Mem.range_perm m (blk beta 0) 0 40 Cur Freeable.
Proof.
  intro HR;pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & Free & _).
  pose proof (region_ok_revalue_u64 w beta m 0 (negate_mag_out c) true (Some 40) H0 eq_refl) as V.
  rewrite (revalue_u64_machine_map _ _ _ _ (negate_mag_output_den c w beta)) in V.
  split;[exact (u64_region_fe_at _ _ _ _ _ _ V)|exact Free].
Qed.
Theorem eval_negate_mag_from_storage c w m b : fe_at m b 0 (words5 w) ->
  Mem.range_perm m b 0 40 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
    [Vptr b Ptrofs.zero;Vptr b Ptrofs.zero;Vint c] E0 mf Vundef /\
  fe_at mf b 0 (words5 (negate_mag_words c w)) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
  lframe (fun bx _=>bx<>b) m mf.
Proof.
  intros Input Free;destruct (eval_negate_mag_symbolic c w [(b,0)] m
    (mul_small_initial w m b Input Free)) as (mf & Call & Rep & Frame).
  destruct (negate_mag_result c w [(b,0)] mf Rep) as [Out Owned].
  exists mf;split;[exact Call|];split;[exact Out|];split;[exact Owned|].
  exact (curve_frame_one negate_mag_regs b m mf eq_refl Frame).
Qed.
Theorem eval_negate_mag_bounded c w m b : 0<=Int.signed c<=7 -> negate_mag_input_bounds c w ->
  fe_at m b 0 (words5 w) -> Mem.range_perm m b 0 40 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
    [Vptr b Ptrofs.zero;Vptr b Ptrofs.zero;Vint c] E0 mf Vundef /\
  fe_at mf b 0 (words5 (negate_mag_words c w)) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
  radix_value (negate_mag_words c w)=2*(Int.signed c+1)*feP-radix_value w /\
  square_input_bounds (negate_mag_words c w) /\ lframe (fun bx _=>bx<>b) m mf.
Proof.
  intros C Bounds Input Free;destruct (eval_negate_mag_from_storage c w m b Input Free)
    as (mf & Call & Out & Owned & Frame).
  destruct (negate_mag_numeric c w C Bounds) as [Value Bound].
  exists mf;split;[exact Call|];split;[exact Out|];split;[exact Owned|];
    split;[exact Value|];split;assumption.
Qed.
