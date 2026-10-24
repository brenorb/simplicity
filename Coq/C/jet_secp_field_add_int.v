(** Original fe_add_int, parameterized for the SWU additions by 8 and 1.
    Share the owned-field relation with fe_mul_int. Execution is proved for
    every C int; the small-addition corollary separately rules out overflow. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_eval C.jet_sx_pure
  C.jet_sx_mem C.jet_sx_rep C.jet_sx_revalue_cells C.jet_secp_fns C.jet_secp_linkage
  C.jets_secp C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_field_add_initial
  C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_field_mul_small C.jet_secp_curve_frame C.jet_secp_square_columns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition add_int_regs := mul_small_regs.
Definition add_int_args (c:int) := [XP 0 0;XI c].
Definition add_int_state (c:int) := match
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 32
    f_secp256k1_fe_add_int (add_int_args c) add_int_regs [] 5 with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition add_int_out c :=
  [XLb Badd (XLv 0) (XI2L Signed (XI c));XLv 1;XLv 2;XLv 3;XLv 4].
Definition add_int_words (c:int) (w:nat->int64) (i:nat) :=
  if Nat.eqb i 0 then Int64.add (w 0%nat) (Int64.repr (Int.signed c)) else w i.

Lemma add_int_run c :
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 32
    f_secp256k1_fe_add_int (add_int_args c) add_int_regs [] 5=
    Some (RDone (add_int_state c) ONormal).
Proof. reflexivity. Qed.
Lemma add_int_return c : (stemps (add_int_state c))!1%positive=None.
Proof. reflexivity. Qed.
Lemma add_int_output c :
  sregs (add_int_state c)=[mkreg (u64_cells 0 (add_int_out c)) true (Some 40)].
Proof. reflexivity. Qed.
Lemma add_int_output_den c w beta :
  map (den w (lay beta)) (add_int_out c)=map Vlong (words5 (add_int_words c w)).
Proof. reflexivity. Qed.

Theorem eval_field_add_int_symbolic c w layout m : rep w layout add_int_regs m -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add_int)
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));Vint c] E0 mf Vundef /\
  rep w layout [mkreg (u64_cells 0 (add_int_out c)) true (Some 40)] mf /\
  lframe (fun b pos=>~foot layout (map rshape add_int_regs) b pos) m mf.
Proof.
  intro HR;destruct (xfun_pure secp_ge secp_pure secp_pure_ok 32 f_secp256k1_fe_add_int
    (add_int_args c) add_int_regs 5 _ (add_int_run c) eq_refl w layout m HR)
    as (mf & result & HC & HP & HV & HS & HL).
  cbn [rsel fst] in HP,HV;rewrite add_int_return in HV;subst result.
  change (map (den w (lay layout)) (add_int_args c)) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0+0));Vint c] in HC.
  rewrite Z.add_0_r in HC;rewrite add_int_output in HP.
  exists mf;split;[exact HC|];split;assumption.
Qed.
Lemma add_int_initial w m b : fe_at m b 0 (words5 w) ->
  Mem.range_perm m b 0 40 Cur Freeable -> rep w [(b,0)] add_int_regs m.
Proof. apply mul_small_initial. Qed.
Lemma add_int_result c w layout m :
  rep w layout [mkreg (u64_cells 0 (add_int_out c)) true (Some 40)] m ->
  fe_at m (blk layout 0) (bas layout 0) (words5 (add_int_words c w)) /\
  Mem.range_perm m (blk layout 0) 0 40 Cur Freeable.
Proof.
  intro HR;pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & HF & _).
  pose proof (region_ok_revalue_u64 w layout m 0 (add_int_out c) true (Some 40) H0 eq_refl) as HV.
  rewrite (revalue_u64_machine_map _ _ _ _ (add_int_output_den c w layout)) in HV.
  split;[exact (u64_region_fe_at _ _ _ _ _ _ HV)|exact HF].
Qed.

Lemma add_int_unsigned_zero c w :
  0<=Int64.unsigned (w 0%nat)+Int.signed c<=Int64.max_unsigned ->
  Int64.unsigned (add_int_words c w 0%nat)=Int64.unsigned (w 0%nat)+Int.signed c.
Proof.
  intro Bound;unfold add_int_words;cbn [Nat.eqb];unfold Int64.add.
  rewrite !Int64.unsigned_repr_eq,Z.add_mod_idemp_r by
    (change Int64.modulus with 18446744073709551616;lia).
  apply Z.mod_small;change Int64.modulus with 18446744073709551616;
    change Int64.max_unsigned with 18446744073709551615 in Bound;lia.
Qed.
Lemma add_int_radix c w :
  0<=Int64.unsigned (w 0%nat)+Int.signed c<=Int64.max_unsigned ->
  radix_value (add_int_words c w)=radix_value w+Int.signed c.
Proof.
  intro Bound;rewrite !radix_value_matches_normalizer;unfold fe_val.
  rewrite (add_int_unsigned_zero c w Bound);unfold add_int_words;cbn [Nat.eqb];ring.
Qed.
Lemma add_int_bounds c w : 0<=Int.signed c<=8 -> mul_small_input_bounds w ->
  square_input_bounds (add_int_words c w).
Proof.
  intros C B i Index;unfold add_int_words;destruct (Nat.eqb i 0) eqn:Zero.
  - apply Nat.eqb_eq in Zero;subst i.
    change (Int64.unsigned (add_int_words c w 0%nat)<72057594037927936).
    pose proof (B 0%nat ltac:(lia)) as Bound;cbn [Nat.eqb] in Bound.
    rewrite add_int_unsigned_zero by (pose proof (Int64.unsigned_range_2 (w 0%nat));
      change Int64.max_unsigned with 18446744073709551615;lia).
    lia.
  - pose proof (B i Index);destruct (Nat.eqb i 4);lia.
Qed.

Theorem eval_field_add_int_from_storage c w m b :
  fe_at m b 0 (words5 w) -> Mem.range_perm m b 0 40 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add_int)
    [Vptr b Ptrofs.zero;Vint c] E0 mf Vundef /\
  fe_at mf b 0 (words5 (add_int_words c w)) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
  lframe (fun bx _=>bx<>b) m mf.
Proof.
  intros HI HF;destruct (eval_field_add_int_symbolic c w [(b,0)] m (add_int_initial w m b HI HF))
    as (mf & Call & Rep & Frame).
  destruct (add_int_result c w [(b,0)] mf Rep) as [Out Free].
  exists mf;split;[exact Call|];split;[exact Out|];split;[exact Free|].
  exact (curve_frame_one add_int_regs b m mf eq_refl Frame).
Qed.
Theorem eval_field_add_int_small c w m b : 0<=Int.signed c<=8 -> mul_small_input_bounds w ->
  fe_at m b 0 (words5 w) -> Mem.range_perm m b 0 40 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add_int)
    [Vptr b Ptrofs.zero;Vint c] E0 mf Vundef /\
  fe_at mf b 0 (words5 (add_int_words c w)) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
  radix_value (add_int_words c w)=radix_value w+Int.signed c /\
  square_input_bounds (add_int_words c w) /\ lframe (fun bx _=>bx<>b) m mf.
Proof.
  intros C Bounds Input Free;destruct (eval_field_add_int_from_storage c w m b Input Free)
    as (mf & Call & Out & Owned & Frame).
  exists mf;split;[exact Call|];split;[exact Out|];split;[exact Owned|];split.
  - apply add_int_radix;pose proof (Bounds 0%nat ltac:(lia)) as Low;cbn [Nat.eqb] in Low.
    pose proof (Int64.unsigned_range_2 (w 0%nat));
      change Int64.max_unsigned with 18446744073709551615;lia.
  - split;[apply add_int_bounds;assumption|exact Frame].
Qed.
