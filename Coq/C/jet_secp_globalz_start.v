(** Original nonempty global-Z prefix: weak-normalize the last Y field and
    copy the last ratio into the real zs local. All memory premises for the
    descending loop are derived from initial table/ratio storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_globalz_loop C.jet_secp_globalz_prepare C.jet_secp_globalz_factor_call
 C.jet_secp_curve_statements C.jet_secp_field_slice_weak C.jet_secp_field_weak_loose
 C.jet_secp_field_copy_owned C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_generator_globalz_empty
 C.jet_secp_statement_prefix C.jet_secp_slice_permissions C.jet_clight_internal_permissions
 C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge weak_loose_words.

Definition globalz_start_normalize := curve_call _secp256k1_fe_normalize_weak f_secp256k1_fe_normalize_weak None
 [Eaddrof (globalz_table_field _y curve_fe_type) (tptr curve_fe_type)].
Definition globalz_start_copy := Sassign (Evar _zs curve_fe_type) (Ederef globalz_ratio_address curve_fe_type).
Definition globalz_start := statement_sequence (fst (split_statement_last globalz_nonempty_branch)) Sskip.
Definition globalz_start_frame (br bf:block) (bx:block) pos :=
 bx<>bf /\ (bx<>br \/ pos<656 \/ 696<=pos).
Lemma globalz_start_source : globalz_start=Ssequence globalz_start_normalize (Ssequence globalz_start_copy Sskip).
Proof. reflexivity. Qed.

Lemma globalz_table_weak_last m mf br xs ys : globalz_table_rep m br xs ys ->
 Mem.range_perm m br 0 704 Cur Freeable -> fe_at mf br 656 (words5 (weak_loose_words (ys 7%nat))) ->
 lframe (fun bx pos=>bx<>br \/ pos<656 \/ 696<=pos) m mf ->
 globalz_table_rep mf br xs (globalz_replace ys 7 (weak_loose_words (ys 7%nat))).
Proof.
 intros Table Free Y Frame k Bound;destruct (Table k Bound) as (XK & YK & FlagK).
 assert (K:0<=Z.of_nat k<=7) by lia.
 assert (Valid:Mem.valid_block m br) by (eapply Mem.perm_valid_block;apply (Free 0);lia).
 split.
 - eapply curve_keep_field_range;[reflexivity|exact XK|exact Frame|];intros pos Range;right;left;lia.
 - split.
   + unfold globalz_replace;destruct (Nat.eq_dec k 7) as [->|Different];[exact Y|].
     eapply curve_keep_field_range;[reflexivity|exact YK|exact Frame|];intros pos Range;right;left;
      assert (Z.of_nat k<7) by lia;lia.
   + rewrite (proj1 Frame Mint32 br (88*Z.of_nat k+80) Valid);[exact FlagK|].
     intros pos Range;change (88*Z.of_nat k+80<=pos<88*Z.of_nat k+80+4) in Range.
     destruct (Nat.eq_dec k 7) as [->|Different];[right;right;cbn in *;lia|right;left];
      assert (Z.of_nat k<7) by lia;lia.
Qed.

Theorem exec_globalz_start e le m br bf bz xs ys ratios :
 br<>bf -> br<>bz -> bf<>bz ->
 e!_zs=Some (bf,curve_fe_type) -> e!_secp256k1_fe_normalize_weak=None ->
 le!_a=Some (Vptr br Ptrofs.zero) -> le!_zr=Some (Vptr bz Ptrofs.zero) ->
 le!_i=Some (Vlong (Int64.repr 7)) ->
 globalz_table_bounds xs ys -> globalz_ratios_bounds ratios ->
 globalz_table_rep m br xs ys -> globalz_ratios_rep m bz ratios ->
 Mem.range_perm m br 0 704 Cur Freeable -> Mem.range_perm m bf 0 40 Cur Freeable ->
 Mem.range_perm m bz 0 320 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m globalz_start E0 le mf Out_normal /\
 globalz_table_rep mf br xs (globalz_replace ys 7 (weak_loose_words (ys 7%nat))) /\
 globalz_ratios_rep mf bz ratios /\ fe_at mf bf 0 (words5 (ratios 7%nat)) /\
 globalz_table_bounds xs (globalz_replace ys 7 (weak_loose_words (ys 7%nat))) /\
 Mem.range_perm mf br 0 704 Cur Freeable /\ Mem.range_perm mf bf 0 40 Cur Freeable /\
 Mem.range_perm mf bz 0 320 Cur Freeable /\ keeps_permissions m mf /\
 lframe (globalz_start_frame br bf) m mf /\ readonly_preserved m mf.
Proof.
 intros AF AR FR Factor Global A Ratios IndexTemp TableBounds RatioBounds Table RatiosRep FreeA FreeZ FreeR.
 destruct (Table 7%nat ltac:(lia)) as (_ & Y & _).
 destruct (TableBounds 7%nat ltac:(lia)) as (_ & BY).
 destruct (eval_field_slice_weak (ys 7%nat) m br 656
   ltac:(intros i Bound;pose proof (square_input56 _ BY i Bound);lia) Y)
  as (m1 & Normalize & Y1 & Numeric & BoundY & Keep1 & Frame1 & Readonly1).
 assert (Table1:globalz_table_rep m1 br xs (globalz_replace ys 7 (weak_loose_words (ys 7%nat)))).
 { eapply globalz_table_weak_last;[exact Table|exact FreeA|exact Y1|exact Frame1]. }
 assert (Ratios1:globalz_ratios_rep m1 bz ratios).
 { intros j Bound;eapply field_at_lframe;[exact (RatiosRep j Bound)|exact Frame1|];intros;left;congruence. }
 assert (FreeZ1:Mem.range_perm m1 bf 0 40 Cur Freeable) by
  (eapply keeps_range_permissions;[exact Keep1|exact FreeZ]).
 destruct (exec_field_copy_owned e le m1 (Ederef globalz_ratio_address curve_fe_type) (Evar _zs curve_fe_type)
   bz 280 bf 0 (ratios 7%nat) eq_refl eq_refl
   ltac:(eapply eval_Elvalue;[apply eval_Ederef;apply (eval_globalz_ratio e le m1 bz 7);[lia|exact Ratios|exact IndexTemp]|
     apply deref_loc_copy;reflexivity])
   ltac:(apply eval_Evar_local;exact Factor) (not_eq_sym FR) (Ratios1 7%nat ltac:(lia))
   ltac:(lia) ltac:(exists 0;reflexivity) ltac:(change (40<=18446744073709551615);lia) FreeZ1)
  as (mf & Copy & ZF & Perm2 & Frame2).
 assert (Keep:keeps_permissions m mf).
 { intros b pos k p Perm;apply (proj2 (Perm2 b pos k p));apply Keep1;exact Perm. }
 assert (NormalizeStmt:Clight2.exec_stmt secp_ge e le m globalz_start_normalize E0 le m1 Out_normal).
 { unfold globalz_start_normalize;eapply exec_curve_call with (vargs:=[Vptr br (Ptrofs.repr 656)]) (v:=Vundef).
   - unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
   - exact Global.
   - eapply eval_Econs.
     + apply eval_Eaddrof;apply (eval_globalz_table_field e le m br 7 _y 40 curve_fe_type);
        [lia|right;left;reflexivity|exact A|exact IndexTemp].
     + reflexivity.
     + constructor.
   - exact Normalize. }
 assert (Valid:Mem.valid_block m1 br) by (eapply Mem.perm_valid_block;apply Keep1;apply (FreeA 0);lia).
 exists mf;split.
 - rewrite globalz_start_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m1);
    [exact NormalizeStmt|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mf);[exact Copy|constructor].
 - split.
   + intros j Bound;destruct (Table1 j Bound) as (X1 & Y1' & Flag1).
     split;[eapply field_at_lframe;[exact X1|exact Frame2|];intros;left;exact AF|];
      split;[eapply field_at_lframe;[exact Y1'|exact Frame2|];intros;left;exact AF|].
     rewrite (proj1 Frame2 Mint32 br (88*Z.of_nat j+80) Valid);[exact Flag1|];intros;left;exact AF.
   + split.
     * intros j Bound;eapply field_at_lframe;[exact (Ratios1 j Bound)|exact Frame2|];intros;left;congruence.
     * split;[exact ZF|];split.
       { intros j Bound;unfold globalz_replace;destruct (Nat.eq_dec j 7) as [->|Different];
          [split;[exact (proj1 (TableBounds 7%nat ltac:(lia)))|exact BoundY]|apply TableBounds;exact Bound]. }
       split;[eapply keeps_range_permissions;[exact Keep|exact FreeA]|];
        split;[eapply keeps_range_permissions;[exact Keep|exact FreeZ]|];
        split;[eapply keeps_range_permissions;[exact Keep|exact FreeR]|];split;[exact Keep|];split.
       { eapply lframe_trans;eapply lframe_implies;[exact Frame1| |exact Frame2|];
          intros b pos [NotZ Outside] Valid';[exact Outside|left;exact NotZ]. }
       eapply preserved_trans;[exact Readonly1|];inversion Copy;subst;eapply assign_preserved;eassumption.
Qed.
