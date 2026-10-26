(** Original fe_mul with its output aliasing its first operand. Both field
    slices may have arbitrary valid offsets; reuse the existing word log and
    numeric bridge. Caller allocation permissions are retained separately. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep
 C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_fe_b32 C.jet_secp_b32_exec C.jet_secp_field_add_initial
 C.jet_secp_point_mul_run C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric
 C.jet_secp_u128_word_oracle C.jet_secp_field_mul_word_model C.jet_secp_curve_mul
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_slice_permissions C.jet_clight_internal_permissions C.jet_secp_field_slice_product.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition field_slice_accumulate_regs := [fe_reg (vars5 0);fe_reg (vars5 5)].
Definition field_slice_accumulate_args := [XP 0 0;XP 0 0;XP 1 0].
Definition field_slice_accumulate_run := xfun (genv_cenv secp_ge) [] point_mul_table 400
 f_secp256k1_fe_mul field_slice_accumulate_args field_slice_accumulate_regs [] 10.
Definition field_slice_accumulate_tree := Eval vm_compute in field_slice_accumulate_run.
Definition field_slice_accumulate_state := match field_slice_accumulate_tree with
 | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition field_slice_accumulate_out :=
 [mkreg (u64_cells 0 point_mul_out) true None;fe_reg (vars5 5)].
Lemma field_slice_accumulate_run_eq :
 field_slice_accumulate_run=Some (RDone field_slice_accumulate_state ONormal).
Proof. reflexivity. Qed.
Lemma field_slice_accumulate_log : slog field_slice_accumulate_state=fe_mul_log.
Proof. reflexivity. Qed.
Lemma field_slice_accumulate_output : sregs field_slice_accumulate_state=field_slice_accumulate_out.
Proof. reflexivity. Qed.
Lemma field_slice_accumulate_return : (stemps field_slice_accumulate_state)!1%positive=None.
Proof. reflexivity. Qed.
Local Opaque field_slice_accumulate_state.

Theorem eval_field_slice_accumulate_symbolic rho beta m :
 rep rho beta field_slice_accumulate_regs m -> Forall (u128_evok rho) fe_mul_log -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
 rep rho beta field_slice_accumulate_out mf /\
 lframe (fun b pos=>~foot beta (map rshape field_slice_accumulate_regs) b pos) m mf.
Proof.
 intros Initial Solves.
 destruct (xfun_top_sound secp_ge [] point_mul_table u128_evok u128_inv u128_ext
   ltac:(intros;exact I) ltac:(intros;contradiction) point_mul_table_ok 400 f_secp256k1_fe_mul
   field_slice_accumulate_args field_slice_accumulate_regs [] 10
   (RDone field_slice_accumulate_state ONormal) field_slice_accumulate_run_eq rho beta m Initial)
  as (mf & result & Call & Rep & Ret & Shape & _ & Frame).
 - split;intros;discriminate.
 - intros r _ Eq;exact Eq.
 - exact I.
 - cbn [rsel fst];rewrite field_slice_accumulate_log;exact Solves.
 - cbn [rsel fst] in Rep,Ret;rewrite field_slice_accumulate_return in Ret;subst result.
   rewrite field_slice_accumulate_output in Rep.
   change (map (den rho (lay beta)) field_slice_accumulate_args) with
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));
     Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0))] in Call.
   rewrite !Z.add_0_r in Call;exists mf;split;[exact Call|];split;[exact Rep|].
   eapply lframe_implies;[exact Frame|].
   intros b pos Outside Valid;split;[exact Valid|];split;[exact Outside|intros Eq;exact Eq].
Qed.

Lemma field_slice_accumulate_initial a b m ba oa bb ob :
 field_slice_separated ba oa bb ob ->
 fe_at m ba oa (words5 a) -> fe_at m bb ob (words5 b) ->
 rep (point_mul_valuation a b) [(ba,oa);(bb,ob)] field_slice_accumulate_regs m.
Proof.
 intros AB A B.
 assert (H0:region_ok (point_mul_valuation a b) [(ba,oa);(bb,ob)] m 0 (fe_reg (vars5 0))).
 { apply field_region_from_values;exact A. }
 assert (H1:region_ok (point_mul_valuation a b) [(ba,oa);(bb,ob)] m 1 (fe_reg (vars5 5))).
 { apply field_region_from_values;exact B. }
 split;[reflexivity|];split.
 - intros r1 r2 reg1 reg2 Different E1 E2.
   assert (B1:(r1<2)%nat) by (change (r1<length field_slice_accumulate_regs)%nat;apply nth_error_Some;congruence).
   assert (B2:(r2<2)%nat) by (change (r2<length field_slice_accumulate_regs)%nat;apply nth_error_Some;congruence).
   destruct r1 as [|[|r1]],r2 as [|[|r2]];try lia;
    cbn [field_slice_accumulate_regs nth_error] in E1,E2;injection E1 as <-;injection E2 as <-;
    apply field_slice_regions_separated;try reflexivity;
    try (repeat constructor;cbn;lia);
    cbn [blk bas lay nth fst snd];first [assumption|apply field_slice_separated_sym;assumption].
 - intros r reg Nth;destruct r as [|[|r]];cbn [field_slice_accumulate_regs nth_error] in Nth;
    try (destruct r;discriminate);inversion Nth;subst reg;assumption.
Qed.

Lemma field_slice_accumulate_fields a b beta m :
 rep (point_mul_valuation a b) beta field_slice_accumulate_out m ->
 fe_at m (blk beta 0) (bas beta 0) (words5 (point_mul_words a b)) /\
 fe_at m (blk beta 1) (bas beta 1) (words5 b).
Proof.
 intro Rep;split;eapply field_slice_region_words;
  [exact (rep_region _ _ _ m 0 _ Rep eq_refl)|reflexivity|apply point_mul_output_den|
   exact (rep_region _ _ _ m 1 _ Rep eq_refl)|reflexivity|reflexivity].
Qed.

Lemma field_slice_accumulate_foot beta bx pos :
 foot beta (map rshape field_slice_accumulate_regs) bx pos -> exists r,
 (r<2)%nat /\ bx=blk beta r /\ bas beta r<=pos<bas beta r+40.
Proof.
 intros (r & sh & d & ch & Nth & Cell & Block & Range);exists r;
  destruct r as [|[|r]];try (destruct r;discriminate Nth);
  split;[lia| |lia|];split;[exact Block| |exact Block|];
  cbn [field_slice_accumulate_regs map nth_error rshape rcells rw rfree] in Nth;injection Nth as <-;
  cbn [fe_reg rshape rcells rw rfree fst map cshape cofs cchunk u64_cells vars5 In] in Cell;
  repeat match type of Cell with _ \/ _=>destruct Cell as [Cell|Cell] end;
  try contradiction;inversion Cell;subst d ch;change (size_chunk Mint64) with 8 in Range;lia.
Qed.

Theorem eval_field_slice_accumulate a b m ba oa bb ob :
 square_input_bounds a -> square_input_bounds b -> field_slice_separated ba oa bb ob ->
 fe_at m ba oa (words5 a) -> fe_at m bb ob (words5 b) -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
  [Vptr ba (Ptrofs.repr oa);Vptr ba (Ptrofs.repr oa);Vptr bb (Ptrofs.repr ob)] E0 mf Vundef /\
 fe_at mf ba oa (words5 (point_mul_words a b)) /\ fe_at mf bb ob (words5 b) /\
 radix_value (point_mul_words a b) mod feP=(radix_value a*radix_value b) mod feP /\
 square_input_bounds (point_mul_words a b) /\ keeps_permissions m mf /\
 lframe (fun bx pos=>(bx<>ba \/ pos<oa \/ oa+40<=pos) /\
  (bx<>bb \/ pos<ob \/ ob+40<=pos)) m mf.
Proof.
 intros BA BB AB A B.
 destruct (eval_field_slice_accumulate_symbolic (point_mul_valuation a b) [(ba,oa);(bb,ob)] m
   (field_slice_accumulate_initial a b m ba oa bb ob AB A B)
   (fm_solves _ _ _ _ _ _ _ _ _ _)) as (mf & Call & Rep & Frame).
 destruct (field_slice_accumulate_fields a b [(ba,oa);(bb,ob)] mf Rep) as (Out & BP).
 destruct (curve_mul_value_bounds a b (field_operand_from_bounds a BA) (field_operand_from_bounds b BB)) as [Value Bounds].
 exists mf;split;[exact Call|];split;[exact Out|];split;[exact BP|];split;[exact Value|];
  split;[exact (proj2 (point_mul_value_and_bounds a b BA BB))|];split.
 - eapply (secp_internal_keeps_permissions f_secp256k1_fe_mul);[reflexivity|reflexivity|exact Call].
 - eapply lframe_implies;[exact Frame|].
   intros bx pos (NA & NB) Valid Foot.
   destruct (field_slice_accumulate_foot [(ba,oa);(bb,ob)] bx pos Foot) as (r & Bound & Same & Range).
   destruct r as [|[|r]];try lia;cbn [blk bas lay nth fst snd] in Same,Range;subst bx;
    [destruct NA|destruct NB];intuition lia.
Qed.
