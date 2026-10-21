(** Original magnitude-two fe_negate in place at point Y.  The complete
    point allocation is retained; no magnitude-one call is substituted. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_eval C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_local_regions
  C.jet_secp_point_mul_storage C.jet_secp_owned_slice_fields C.jet_secp_field_negate_values
  C.jet_secp_field_sum_bounds C.jet_secp_field_add_initial C.jet_secp_square_columns
  C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition point_y_neg2_regs := [mkreg (u64_cells 40 (vars5 0)) true (Some 128)].
Definition point_y_neg2_args := [XP 0 40;XP 0 40;XIc (Int.repr 2)].
Definition point_y_neg2_expr i := XLb Bsub
  (XLb Bmul (XLb Bmul (XLc (Int64.repr (negate_mask i))) (XI2L Signed (XIc (Int.repr 2))))
    (XI2L Signed (XIb Badd (XIc (Int.repr 2)) (XIc Int.one)))) (XLv i).
Definition point_y_neg2_out := map point_y_neg2_expr [0;1;2;3;4]%nat.
Definition point_y_neg2_words (w : nat -> int64) i := Int64.sub (Int64.repr (6*negate_mask i)) (w i).
Definition point_y_neg2_run := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 160
  f_secp256k1_fe_negate point_y_neg2_args point_y_neg2_regs [] 5.
Definition point_y_neg2_tree := Eval vm_compute in point_y_neg2_run.
Definition point_y_neg2_state := match point_y_neg2_tree with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.

Lemma point_y_neg2_run_eq : point_y_neg2_run=Some (RDone point_y_neg2_state ONormal).
Proof. reflexivity. Qed.
Lemma point_y_neg2_return : (stemps point_y_neg2_state)!1%positive=None.
Proof. reflexivity. Qed.
Lemma point_y_neg2_output_shape : sregs point_y_neg2_state=[mkreg (u64_cells 40 point_y_neg2_out) true (Some 128)].
Proof. reflexivity. Qed.
Lemma point_y_neg2_output_den w beta :
  map (den w (lay beta)) point_y_neg2_out=map Vlong (words5 (point_y_neg2_words w)).
Proof. reflexivity. Qed.

Theorem eval_point_y_neg2_symbolic w beta m : rep w beta point_y_neg2_regs m ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+40));
     Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+40));Vint (Int.repr 2)] E0 mf Vundef /\
  rep w beta [mkreg (u64_cells 40 point_y_neg2_out) true (Some 128)] mf /\
  lframe (fun b pos => ~foot beta (map rshape point_y_neg2_regs) b pos) m mf.
Proof.
  intro HR.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 160 f_secp256k1_fe_negate
    point_y_neg2_args point_y_neg2_regs 5 _ point_y_neg2_run_eq eq_refl w beta m HR)
    as (mf & result & HC & HP & HV & HS & HL).
  cbn [rsel fst] in HP,HV;rewrite point_y_neg2_return in HV;subst result.
  rewrite point_y_neg2_output_shape in HP.
  exists mf;split;[exact HC|];split;assumption.
Qed.

Lemma point_y_neg2_initial w m bp : fe_at m bp 40 (words5 w) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> rep w [(bp,0)] point_y_neg2_regs m.
Proof.
  intros HI HF;apply (rep_add w [] [] m bp 0);[apply rep_nil|cbn;tauto|].
  apply owned_field_slice_region;[reflexivity|lia|lia|exact HI|exact HF].
Qed.

Lemma point_y_neg2_fields w beta m :
  rep w beta [mkreg (u64_cells 40 point_y_neg2_out) true (Some 128)] m ->
  fe_at m (blk beta 0) 40 (words5 (point_y_neg2_words w)) /\
  Mem.range_perm m (blk beta 0) 0 128 Cur Freeable.
Proof.
  intro HR;pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & HF & _).
  split;[|exact HF].
  eapply owned_region_field_slice with (exprs:=point_y_neg2_out) (size:=128);
    [exact H0|lia|exists 5;reflexivity|lia|
     change (128<=18446744073709551615);lia|reflexivity|reflexivity| |].
  - intros c HC;exact HC.
  - apply point_y_neg2_output_den.
Qed.

Lemma point_y_neg2_unsigned w : field_scaled_bounds 2 w ->
  forall i, (i<5)%nat ->
  Int64.unsigned (point_y_neg2_words w i)=6*negate_mask i-Int64.unsigned (w i).
Proof.
  intros HB i HI;unfold point_y_neg2_words;apply unsigned_sub_constant.
  - destruct i as [|[|[|[|[|i]]]]];try lia;cbn [negate_mask];
      change Int64.max_unsigned with 18446744073709551615;lia.
  - pose proof (HB i HI);destruct i as [|[|[|[|[|i]]]]];try lia;
      cbn [Nat.eqb negate_mask] in *;lia.
Qed.

Lemma point_y_neg2_numeric w : field_scaled_bounds 2 w ->
  radix_value (point_y_neg2_words w)=6*feP-radix_value w /\
  field_scaled_bounds 6 (point_y_neg2_words w).
Proof.
  intro HB;split.
  - rewrite !radix_value_matches_normalizer;unfold fe_val.
    rewrite !point_y_neg2_unsigned by (assumption || lia).
    unfold negate_mask,feP,feR;ring.
  - intros i HI;rewrite point_y_neg2_unsigned by assumption.
    pose proof (Int64.unsigned_range_2 (w i)).
    destruct i as [|[|[|[|[|i]]]]];try lia;cbn [Nat.eqb negate_mask] in *;lia.
Qed.

Lemma point_y_neg2_foot bp b pos :
  foot [(bp,0)] (map rshape point_y_neg2_regs) b pos -> b=bp /\ 40<=pos<80.
Proof.
  intros (r & sh & d & ch & HN & HC & HB & HP);destruct r;[|destruct r;discriminate HN].
  split;[exact HB|].
  cbn [point_y_neg2_regs map nth_error rshape rcells rw rfree] in HN;injection HN as <-.
  cbn [rshape rcells rw rfree fst map cshape cofs cchunk u64_cells vars5 In] in HC.
  repeat match type of HC with _ \/ _ => destruct HC as [HC|HC] end;
    try contradiction;inversion HC;subst d ch;cbn [bas lay nth snd] in HP;
    change (size_chunk Mint64) with 8 in HP;lia.
Qed.

Theorem eval_point_y_negate2 w m bp : field_scaled_bounds 2 w ->
  fe_at m bp 40 (words5 w) -> Mem.range_perm m bp 0 128 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
    [Vptr bp (Ptrofs.repr 40);Vptr bp (Ptrofs.repr 40);Vint (Int.repr 2)] E0 mf Vundef /\
  fe_at mf bp 40 (words5 (point_y_neg2_words w)) /\ Mem.range_perm mf bp 0 128 Cur Freeable /\
  radix_value (point_y_neg2_words w)=6*feP-radix_value w /\
  square_input_bounds (point_y_neg2_words w) /\
  lframe (fun b pos => b<>bp \/ pos<40 \/ 80<=pos) m mf.
Proof.
  intros HB HI HF.
  destruct (eval_point_y_neg2_symbolic w [(bp,0)] m (point_y_neg2_initial w m bp HI HF))
    as (mf & HC & HP & HL).
  destruct (point_y_neg2_fields w [(bp,0)] mf HP) as [FO FF].
  destruct (point_y_neg2_numeric w HB) as [HV HBounds].
  exists mf;split;[exact HC|];split;[exact FO|];split;[exact FF|];split;[exact HV|].
  split;[exact (field_scaled_loose 6 _ ltac:(lia) HBounds)|].
  eapply lframe_implies;[exact HL|]. intros b pos HO HV' HFoot.
  destruct (point_y_neg2_foot bp b pos HFoot) as [HE HR].
  subst b;destruct HO as [HN|[HN|HN]];[contradiction|lia|lia].
Qed.
