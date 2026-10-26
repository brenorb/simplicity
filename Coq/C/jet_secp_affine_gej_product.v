(** Actual multiplication into X/Y of an affine allocation from X/Y of a
    projective allocation and a private field. The destination owner size is
    parameterized so a table allocation need not be relabelled as 128 bytes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep
 C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_local_regions
 C.jet_secp_u128_word_oracle C.jet_secp_field_mul_word_model C.jet_secp_point_mul_run
 C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric C.jet_secp_field_point_multiply
 C.jet_secp_owned_slice_fields C.jet_secp_b32_exec C.jet_secp_fe_b32 C.jet_secp_field_add_initial
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_field_mul_small C.jet_secp_curve_mul C.jet_secp_curve_square.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition affine_gej_product_undefined y := map (fun ofs=>mkcell (curve_square_offset y+ofs) Mint64 None)
 [0;8;16;24;32].
Definition affine_gej_product_regs y size :=
 [mkreg (affine_gej_product_undefined y) true (Some size);
  mkreg (u64_cells (curve_square_offset y) (vars5 0)) true (Some 128);
  free_region (fe_reg (vars5 5)) 40].
Definition affine_gej_product_args y := [XP 0 (curve_square_offset y);XP 1 (curve_square_offset y);XP 2 0].
Definition affine_gej_product_run y size := xfun (genv_cenv secp_ge) [] point_mul_table 400
 f_secp256k1_fe_mul (affine_gej_product_args y) (affine_gej_product_regs y size) [] 10.
Definition affine_gej_product_tree := Eval vm_compute in fun (y:bool) (size:Z) =>
 if y then affine_gej_product_run true size else affine_gej_product_run false size.
Definition affine_gej_product_state y size := match affine_gej_product_tree y size with
 | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition affine_gej_product_out y size :=
 [mkreg (u64_cells (curve_square_offset y) point_mul_out) true (Some size);
  mkreg (u64_cells (curve_square_offset y) (vars5 0)) true (Some 128);
  free_region (fe_reg (vars5 5)) 40].
Lemma affine_gej_product_run_eq y size : affine_gej_product_run y size=
 Some (RDone (affine_gej_product_state y size) ONormal).
Proof. destruct y;reflexivity. Qed.
Lemma affine_gej_product_log y size : slog (affine_gej_product_state y size)=fe_mul_log.
Proof. destruct y;reflexivity. Qed.
Lemma affine_gej_product_output y size : sregs (affine_gej_product_state y size)=affine_gej_product_out y size.
Proof. destruct y;reflexivity. Qed.
Lemma affine_gej_product_return y size : (stemps (affine_gej_product_state y size))!1%positive=None.
Proof. destruct y;reflexivity. Qed.

Local Opaque affine_gej_product_state.
Theorem eval_affine_gej_product_symbolic y size rho beta m :
 rep rho beta (affine_gej_product_regs y size) m -> Forall (u128_evok rho) fe_mul_log -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+curve_square_offset y));
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+curve_square_offset y));
   Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef /\
 rep rho beta (affine_gej_product_out y size) mf /\
 lframe (fun b pos=>~foot beta (map rshape (affine_gej_product_regs y size)) b pos) m mf.
Proof.
 intros Initial Solves.
 destruct (xfun_top_sound secp_ge [] point_mul_table u128_evok u128_inv u128_ext
   ltac:(intros;exact I) ltac:(intros;contradiction) point_mul_table_ok 400 f_secp256k1_fe_mul
   (affine_gej_product_args y) (affine_gej_product_regs y size) [] 10
   (RDone (affine_gej_product_state y size) ONormal) (affine_gej_product_run_eq y size) rho beta m Initial)
  as (mf & result & Call & Rep & Ret & Shape & _ & Frame).
 - split;intros;discriminate.
 - intros r _ Eq;exact Eq.
 - exact I.
 - cbn [rsel fst];rewrite affine_gej_product_log;exact Solves.
 - cbn [rsel fst] in Rep,Ret;rewrite affine_gej_product_return in Ret;subst result.
   rewrite affine_gej_product_output in Rep.
   change (map (den rho (lay beta)) (affine_gej_product_args y)) with
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+curve_square_offset y));
     Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+curve_square_offset y));
     Vptr (blk beta 2) (Ptrofs.repr (bas beta 2+0))] in Call.
   rewrite Z.add_0_r in Call.
   exists mf;split;[exact Call|];split;[exact Rep|].
   eapply lframe_implies;[exact Frame|].
   intros b pos Outside Valid;split;[exact Valid|];split;[exact Outside|intros Eq;exact Eq].
Qed.

Lemma affine_gej_product_initial y size a b m br ba bf :
 88<=size -> br<>ba -> br<>bf -> ba<>bf ->
 Mem.range_perm m br 0 size Cur Freeable ->
 fe_at m ba (curve_square_offset y) (words5 a) -> Mem.range_perm m ba 0 128 Cur Freeable ->
 fe_at m bf 0 (words5 b) -> Mem.range_perm m bf 0 40 Cur Freeable ->
 rep (point_mul_valuation a b) [(br,0);(ba,0);(bf,0)] (affine_gej_product_regs y size) m.
Proof.
 intros Size RA RF AF FreeR A FreeA B FreeF.
 assert (H0:region_ok (point_mul_valuation a b) [(br,0);(ba,0);(bf,0)] m 0
  (mkreg (affine_gej_product_undefined y) true (Some size))).
 { unfold region_ok;cbn [rcells rw rfree blk bas lay nth fst snd].
   split;[lia|];split.
   - eapply Mem.perm_valid_block;exact (FreeR 0 ltac:(lia)).
   - split;[destruct y;reflexivity|];split.
     + apply Forall_forall;intros c InC;destruct y;
        cbn [affine_gej_product_undefined curve_square_offset map In] in InC;
        repeat match type of InC with _ \/ _=>destruct InC as [InC|InC] end;
        try contradiction;subst c;apply writable_undefined_cell;
        cbn [blk bas lay nth fst snd size_chunk align_chunk];
        try (change Ptrofs.max_unsigned with 18446744073709551615;lia);
        try (intros pos Range;apply (freeable_range_writable m br 0 size FreeR);lia);
        match goal with |- (8|?ofs)=>exists (ofs/8);reflexivity end.
     + split;[reflexivity|];split;[reflexivity|];split;[exact FreeR|].
       destruct y;repeat constructor;cbn [affine_gej_product_undefined curve_square_offset cofs cchunk size_chunk];lia. }
 assert (H1:region_ok (point_mul_valuation a b) [(br,0);(ba,0);(bf,0)] m 1
  (mkreg (u64_cells (curve_square_offset y) (vars5 0)) true (Some 128))).
 { apply owned_field_slice_region;[reflexivity|lia|destruct y;cbn [curve_square_offset];lia| |exact FreeA].
   rewrite point_mul_valuation_first;exact A. }
 assert (H2:region_ok (point_mul_valuation a b) [(br,0);(ba,0);(bf,0)] m 2
  (free_region (fe_reg (vars5 5)) 40)).
 { apply owned_field_values_slice_region;[reflexivity|lia|lia| |exact FreeF].
   rewrite point_mul_valuation_second;exact B. }
 split;[reflexivity|];split.
 - intros r1 r2 reg1 reg2 Different E1 E2.
   assert (B1:(r1<3)%nat) by (change (r1<length (affine_gej_product_regs y size))%nat;apply nth_error_Some;congruence).
   assert (B2:(r2<3)%nat) by (change (r2<length (affine_gej_product_regs y size))%nat;apply nth_error_Some;congruence).
   destruct r1 as [|[|[|r1]]],r2 as [|[|[|r2]]];try lia;left;cbn [blk lay nth fst];congruence.
 - intros r reg Nth;destruct r as [|[|[|r]]];cbn [affine_gej_product_regs nth_error] in Nth;
    try (destruct r;discriminate);inversion Nth;subst reg;assumption.
Qed.

Lemma affine_gej_product_fields y size a b m br ba bf :
 88<=size -> size<=Ptrofs.max_unsigned ->
 rep (point_mul_valuation a b) [(br,0);(ba,0);(bf,0)] (affine_gej_product_out y size) m ->
 fe_at m br (curve_square_offset y) (words5 (point_mul_words a b)) /\
 fe_at m ba (curve_square_offset y) (words5 a) /\ fe_at m bf 0 (words5 b) /\
 Mem.range_perm m br 0 size Cur Freeable /\ Mem.range_perm m ba 0 128 Cur Freeable /\
 Mem.range_perm m bf 0 40 Cur Freeable.
Proof.
 intros Size Max Rep.
 pose proof (rep_region _ _ _ m 0 _ Rep eq_refl) as R.
 pose proof (rep_region _ _ _ m 1 _ Rep eq_refl) as A.
 pose proof (rep_region _ _ _ m 2 _ Rep eq_refl) as F.
 pose proof R as (_ & _ & _ & _ & _ & _ & RF & _).
 pose proof A as (_ & _ & _ & _ & _ & _ & AF & _).
 pose proof F as (_ & _ & _ & _ & _ & _ & FF & _).
 split.
 - eapply owned_region_field_slice with (exprs:=point_mul_out) (size:=size)
    (rho:=point_mul_valuation a b) (beta:=[(br,0);(ba,0);(bf,0)]) (r:=0%nat);
    [exact R|destruct y;cbn [curve_square_offset];lia|
     destruct y;cbn [curve_square_offset];[exists 5|exists 0];reflexivity|
     destruct y;cbn [curve_square_offset];lia|exact Max|reflexivity|reflexivity| |].
   + intros c InC;exact InC.
   + apply point_mul_output_den.
 - split.
   + eapply owned_region_field_slice with (exprs:=vars5 0) (size:=128)
      (rho:=point_mul_valuation a b) (beta:=[(br,0);(ba,0);(bf,0)]) (r:=1%nat);
      [exact A|destruct y;cbn [curve_square_offset];lia|
       destruct y;cbn [curve_square_offset];[exists 5|exists 0];reflexivity|
       destruct y;cbn [curve_square_offset];lia|change (128<=18446744073709551615);lia|reflexivity|reflexivity| |].
     * intros c InC;exact InC.
     * reflexivity.
   + split;[|repeat split;assumption].
     eapply owned_region_field_slice with (exprs:=vars5 5) (size:=40)
      (rho:=point_mul_valuation a b) (beta:=[(br,0);(ba,0);(bf,0)]) (r:=2%nat);
      [exact F|lia|exists 0;reflexivity|lia|change (40<=18446744073709551615);lia|reflexivity|reflexivity| |].
     * intros c InC;exact InC.
     * reflexivity.
Qed.

Lemma affine_gej_product_foot y size br ba bf bx pos :
 foot [(br,0);(ba,0);(bf,0)] (map rshape (affine_gej_product_regs y size)) bx pos ->
 (bx=br /\ curve_square_offset y<=pos<curve_square_offset y+40) \/
 (bx=ba /\ curve_square_offset y<=pos<curve_square_offset y+40) \/ bx=bf.
Proof.
 intros (r & sh & d & ch & Nth & Cell & Block & Range).
 destruct r as [|[|[|r]]];[left|right;left|right;right;exact Block|destruct r;discriminate Nth];
   split;[exact Block| |exact Block|];destruct y;
   cbn [affine_gej_product_regs map nth_error rshape rcells rw rfree] in Nth;injection Nth as <-;
   cbn [affine_gej_product_undefined curve_square_offset rshape rcells rw rfree fst map cshape cofs cchunk u64_cells vars5 In] in Cell;
   repeat match type of Cell with _ \/ _=>destruct Cell as [Cell|Cell] end;
   try contradiction;inversion Cell;subst d ch;cbn [bas lay nth snd curve_square_offset] in Range;
   change (size_chunk Mint64) with 8 in Range;cbn [curve_square_offset];lia.
Qed.

Theorem eval_affine_gej_product y size a b m br ba bf :
 88<=size -> size<=Ptrofs.max_unsigned -> square_input_bounds a -> square_input_bounds b ->
 br<>ba -> br<>bf -> ba<>bf -> Mem.range_perm m br 0 size Cur Freeable ->
 fe_at m ba (curve_square_offset y) (words5 a) -> Mem.range_perm m ba 0 128 Cur Freeable ->
 fe_at m bf 0 (words5 b) -> Mem.range_perm m bf 0 40 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
  [Vptr br (Ptrofs.repr (curve_square_offset y));Vptr ba (Ptrofs.repr (curve_square_offset y));Vptr bf Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br (curve_square_offset y) (words5 (point_mul_words a b)) /\
 fe_at mf ba (curve_square_offset y) (words5 a) /\ fe_at mf bf 0 (words5 b) /\
 Mem.range_perm mf br 0 size Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 Mem.range_perm mf bf 0 40 Cur Freeable /\
 radix_value (point_mul_words a b) mod feP=(radix_value a*radix_value b) mod feP /\
 square_input_bounds (point_mul_words a b) /\
 lframe (fun bx pos=>bx<>bf /\ (bx<>br \/ pos<curve_square_offset y \/ curve_square_offset y+40<=pos) /\
  (bx<>ba \/ pos<curve_square_offset y \/ curve_square_offset y+40<=pos)) m mf.
Proof.
 intros Size Max BA BB RA RF AF FreeR A FreeA B FreeF.
 destruct (eval_affine_gej_product_symbolic y size (point_mul_valuation a b) [(br,0);(ba,0);(bf,0)] m
   (affine_gej_product_initial y size a b m br ba bf Size RA RF AF FreeR A FreeA B FreeF)
   (fm_solves _ _ _ _ _ _ _ _ _ _)) as (mf & Call & Rep & Frame).
 destruct (affine_gej_product_fields y size a b mf br ba bf Size Max Rep)
  as (Out & AP & BF & RFF & AFF & FFF).
 destruct (curve_mul_value_bounds a b (field_operand_from_bounds a BA) (field_operand_from_bounds b BB)) as [Value Bounds].
 exists mf;split;[exact Call|];split;[exact Out|];split;[exact AP|];split;[exact BF|];
  split;[exact RFF|];split;[exact AFF|];split;[exact FFF|];split;[exact Value|];
  split;[exact (proj2 (point_mul_value_and_bounds a b BA BB))|].
 eapply lframe_implies;[exact Frame|].
 intros bx pos (NF & NR & NA) Valid Foot.
 destruct (affine_gej_product_foot y size br ba bf bx pos Foot) as [[Same Range]|[[Same Range]|Same]];
  subst bx;[destruct NR|destruct NA|];intuition lia.
Qed.
