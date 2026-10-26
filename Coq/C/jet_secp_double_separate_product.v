(** Actual r.z = a.z * a.y with distinct projective allocations. This is
    the first arithmetic call of table construction's out-of-place doubling.
    The destination may be uninitialized; the source fields share one block.
    The existing proved u128 oracles discharge the multiplication log. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_local_regions C.jet_secp_u128_word_oracle C.jet_secp_field_mul_word_model
 C.jet_secp_point_mul_run C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric
 C.jet_secp_field_point_multiply C.jet_secp_owned_slice_fields C.jet_secp_field_add_initial
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_curve_mul C.jet_secp_b32_exec.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition double_separate_product_undefined :=
 [mkcell 80 Mint64 None;mkcell 88 Mint64 None;mkcell 96 Mint64 None;
  mkcell 104 Mint64 None;mkcell 112 Mint64 None].
Definition double_separate_product_regs :=
 [mkreg double_separate_product_undefined true (Some 128);
  mkreg (u64_cells 40 (vars5 5)++u64_cells 80 (vars5 0)) true (Some 128)].
Definition double_separate_product_args := [XP 0 80;XP 1 80;XP 1 40].
Definition double_separate_product_run := xfun (genv_cenv secp_ge) [] point_mul_table 400
 f_secp256k1_fe_mul double_separate_product_args double_separate_product_regs [] 10.
Definition double_separate_product_tree := Eval vm_compute in double_separate_product_run.
Definition double_separate_product_state := match double_separate_product_tree with
 | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition double_separate_product_out :=
 [mkreg (u64_cells 80 point_mul_out) true (Some 128);
  mkreg (u64_cells 40 (vars5 5)++u64_cells 80 (vars5 0)) true (Some 128)].

Lemma double_separate_product_run_eq : double_separate_product_run=
 Some (RDone double_separate_product_state ONormal).
Proof. reflexivity. Qed.
Lemma double_separate_product_log : slog double_separate_product_state=fe_mul_log.
Proof. reflexivity. Qed.
Lemma double_separate_product_output : sregs double_separate_product_state=double_separate_product_out.
Proof. reflexivity. Qed.
Lemma double_separate_product_return : (stemps double_separate_product_state)!1%positive=None.
Proof. reflexivity. Qed.

Local Opaque double_separate_product_state.
Theorem eval_double_separate_product_symbolic rho beta m :
 rep rho beta double_separate_product_regs m -> Forall (u128_evok rho) fe_mul_log -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+80));
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+80));
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+40))] E0 mf Vundef /\
 rep rho beta double_separate_product_out mf /\
 lframe (fun b pos=>~foot beta (map rshape double_separate_product_regs) b pos) m mf.
Proof.
 intros Initial Solves.
 destruct (xfun_top_sound secp_ge [] point_mul_table u128_evok u128_inv u128_ext
   ltac:(intros;exact I) ltac:(intros;contradiction) point_mul_table_ok
   400 f_secp256k1_fe_mul double_separate_product_args double_separate_product_regs [] 10
   (RDone double_separate_product_state ONormal) double_separate_product_run_eq rho beta m Initial)
   as (mf & result & Call & Rep & Ret & State & _ & Frame).
 - split;intros;discriminate.
 - intros r _ Eq;exact Eq.
 - exact I.
 - cbn [rsel fst];rewrite double_separate_product_log;exact Solves.
 - cbn [rsel fst] in Rep,Ret;rewrite double_separate_product_return in Ret;subst result.
   rewrite double_separate_product_output in Rep.
   exists mf;split;[exact Call|];split;[exact Rep|].
   eapply lframe_implies;[exact Frame|].
   intros b pos Outside Valid;split;[exact Valid|];split;[exact Outside|intros Eq;exact Eq].
Qed.

Lemma double_separate_product_initial z y m br ba : br<>ba ->
 Mem.range_perm m br 0 128 Cur Freeable ->
 fe_at m ba 80 (words5 z) -> fe_at m ba 40 (words5 y) ->
 Mem.range_perm m ba 0 128 Cur Freeable ->
 rep (point_mul_valuation z y) [(br,0);(ba,0)] double_separate_product_regs m.
Proof.
 intros Separate RF ZAt YAt AF.
 apply two_region_rep_separate;[reflexivity|exact Separate| |].
 - unfold region_ok;cbn [rcells rw rfree blk bas lay nth fst snd].
   split;[lia|];split.
   + eapply Mem.perm_valid_block;apply (RF 0);lia.
   + split;[reflexivity|];split.
     * apply Forall_forall;intros c InC;cbn [double_separate_product_undefined In] in InC.
       repeat match type of InC with _ \/ _=>destruct InC as [InC|InC] end;
         try contradiction;subst c;apply writable_undefined_cell;
         cbn [blk bas lay nth fst snd size_chunk align_chunk cofs cchunk];
         try (change Ptrofs.max_unsigned with 18446744073709551615;lia);
         try (intros pos Range;apply (freeable_range_writable m br 0 128 RF);lia);
         match goal with |- (8|?ofs)=>exists (ofs/8);reflexivity end.
     * split;[reflexivity|];split;[reflexivity|];split;[exact RF|].
       repeat constructor;cbn [double_separate_product_undefined cofs cchunk size_chunk];lia.
 - apply owned_region_append.
   + apply owned_field_values_slice_region;[reflexivity|lia|lia| |exact AF].
     rewrite point_mul_valuation_second;exact YAt.
   + apply owned_field_slice_region;[reflexivity|lia|lia| |exact AF].
     rewrite point_mul_valuation_first;exact ZAt.
   + reflexivity.
Qed.

Lemma double_separate_product_fields z y m br ba :
 rep (point_mul_valuation z y) [(br,0);(ba,0)] double_separate_product_out m ->
 fe_at m br 80 (words5 (point_mul_words z y)) /\
 fe_at m ba 80 (words5 z) /\ fe_at m ba 40 (words5 y) /\
 Mem.range_perm m br 0 128 Cur Freeable /\ Mem.range_perm m ba 0 128 Cur Freeable.
Proof.
 intro Rep.
 pose proof (rep_region _ _ _ m 0 _ Rep eq_refl) as R.
 pose proof (rep_region _ _ _ m 1 _ Rep eq_refl) as A.
 pose proof R as (_ & _ & _ & _ & _ & _ & RF & _).
 pose proof A as (_ & _ & _ & _ & _ & _ & AF & _).
 split.
 - eapply owned_region_field_slice with (exprs:=point_mul_out) (size:=128)
    (rho:=point_mul_valuation z y) (beta:=[(br,0);(ba,0)]) (r:=0%nat);
    [exact R|lia|exists 10;reflexivity|lia|
     change (128<=18446744073709551615);lia|reflexivity|reflexivity| |].
   + intros c InC;exact InC.
   + apply point_mul_output_den.
 - split.
   + eapply owned_region_field_slice with (exprs:=vars5 0) (size:=128)
      (rho:=point_mul_valuation z y) (beta:=[(br,0);(ba,0)]) (r:=1%nat);
      [exact A|lia|exists 10;reflexivity|lia|
       change (128<=18446744073709551615);lia|reflexivity|reflexivity| |].
     * intros c InC;apply in_or_app;right;exact InC.
     * reflexivity.
   + split;[|split;assumption].
     eapply owned_region_field_slice with (exprs:=vars5 5) (size:=128)
      (rho:=point_mul_valuation z y) (beta:=[(br,0);(ba,0)]) (r:=1%nat);
      [exact A|lia|exists 5;reflexivity|lia|
       change (128<=18446744073709551615);lia|reflexivity|reflexivity| |].
     * intros c InC;apply in_or_app;left;exact InC.
     * reflexivity.
Qed.

Lemma double_separate_product_foot br ba b pos :
 foot [(br,0);(ba,0)] (map rshape double_separate_product_regs) b pos ->
 (b=br /\ 80<=pos<120) \/ (b=ba /\ 40<=pos<120).
Proof.
 intros (r & sh & d & ch & Nth & Cell & Block & Range).
 destruct r as [|[|r]];[left|right|destruct r;discriminate Nth];
   split;[exact Block| |exact Block|];
   cbn [double_separate_product_regs map nth_error rshape rcells rw rfree] in Nth;
   injection Nth as <-;
   cbn [double_separate_product_undefined rshape rcells rw rfree fst map cshape cofs cchunk u64_cells vars5 app In] in Cell;
   repeat match type of Cell with _ \/ _=>destruct Cell as [Cell|Cell] end;
   try contradiction;inversion Cell;subst d ch;cbn [bas lay nth snd] in Range;
   change (size_chunk Mint64) with 8 in Range;lia.
Qed.

Theorem eval_double_separate_product z y m br ba :
 square_input_bounds z -> square_input_bounds y -> br<>ba ->
 Mem.range_perm m br 0 128 Cur Freeable ->
 fe_at m ba 80 (words5 z) -> fe_at m ba 40 (words5 y) ->
 Mem.range_perm m ba 0 128 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
  [Vptr br (Ptrofs.repr 80);Vptr ba (Ptrofs.repr 80);Vptr ba (Ptrofs.repr 40)] E0 mf Vundef /\
 fe_at mf br 80 (words5 (point_mul_words z y)) /\
 fe_at mf ba 80 (words5 z) /\ fe_at mf ba 40 (words5 y) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 radix_value (point_mul_words z y) mod feP=(radix_value z*radix_value y) mod feP /\
 square_input_bounds (point_mul_words z y) /\
 lframe (fun b pos=>(b<>br \/ pos<80 \/ 120<=pos) /\
   (b<>ba \/ pos<40 \/ 120<=pos)) m mf.
Proof.
 intros BZ BY Separate RF ZAt YAt AF.
 destruct (eval_double_separate_product_symbolic (point_mul_valuation z y) [(br,0);(ba,0)] m
   (double_separate_product_initial z y m br ba Separate RF ZAt YAt AF)
   (fm_solves _ _ _ _ _ _ _ _ _ _)) as (mf & Call & Rep & Frame).
 destruct (double_separate_product_fields z y mf br ba Rep) as (Out & ZF & YF & RFF & AFF).
 destruct (curve_mul_value_bounds z y (field_operand_from_bounds z BZ)
   (field_operand_from_bounds y BY)) as [Value Bounds].
 exists mf;split;[exact Call|];split;[exact Out|];split;[exact ZF|];split;[exact YF|];
   split;[exact RFF|];split;[exact AFF|];split;[exact Value|];
   split;[exact (proj2 (point_mul_value_and_bounds z y BZ BY))|].
 eapply lframe_implies;[exact Frame|].
 intros b pos [OutsideR OutsideA] Valid Foot.
 destruct (double_separate_product_foot br ba b pos Foot) as [[Same Range]|[Same Range]];
   subst b;[destruct OutsideR|destruct OutsideA];intuition lia.
Qed.
