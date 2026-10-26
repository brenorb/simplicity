(** Original global-Z temporary preparation: two typed coordinate copies and
    the finite flag store. The temporary's Z bytes may be uninitialized. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_curve_statements C.jet_secp_gej_infinity_layout C.jet_secp_globalz_indexed_call
 C.jet_secp_field_copy_owned C.jet_secp_multiply_normalize_bridge C.jet_secp_local_regions
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_clight_internal_preserve
 C.jet_secp_statement_prefix.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition globalz_tmp_field fid ty := Efield (Evar _tmpa (Tstruct __6123 noattr)) fid ty.
Definition globalz_table_field fid ty := Efield
 (Ederef globalz_indexed_entry_address curve_ge_type) fid ty.
Definition globalz_copy_statement (y:bool) := Sassign
 (globalz_tmp_field (if y then _y else _x) curve_fe_type)
 (globalz_table_field (if y then _y else _x) curve_fe_type).
Definition globalz_finite_statement := Sassign (globalz_tmp_field _infinity tint) (Econst_int Int.zero tint).
Definition globalz_prepare_statements :=
 [globalz_copy_statement false;globalz_copy_statement true;globalz_finite_statement].
Definition globalz_prepare := statement_sequence globalz_prepare_statements Sskip.
Definition globalz_decrement := Sset _i
 (Ebinop Osub (Etempvar _i tulong) (Econst_int Int.one tint) tulong).

Lemma globalz_prepare_source : globalz_indexed_loop_body=
 Ssequence (match globalz_indexed_loop_body with Ssequence s _=>s | _=>Sskip end)
 (Ssequence globalz_decrement (statement_sequence globalz_prepare_statements globalz_indexed_scale_statement)).
Proof. reflexivity. Qed.

Lemma eval_globalz_tmp_field e le m bt fid delta ty :
 In (fid,delta) [(_x,0);(_y,40);(_infinity,120)] ->
 e!_tmpa=Some (bt,Tstruct __6123 noattr) ->
 eval_lvalue secp_ge e le m (globalz_tmp_field fid ty) bt (Ptrofs.repr delta) Full.
Proof.
 intros Field Tmp.
 assert (Layout:In (fid,delta) [(_x,0);(_y,40);(_z,80);(_infinity,120)]).
 { destruct Field as [Same|[Same|[Same|Same]]];try contradiction;
    [left|right;left|right;right;right;left];exact Same. }
 destruct (gej_infinity_field_layout fid delta Layout) as (co & Lookup & Offset).
 unfold globalz_tmp_field;rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)).
 eapply eval_Efield_struct with (co:=co) (delta:=delta).
 - eapply eval_Elvalue;[apply eval_Evar_local;exact Tmp|apply deref_loc_copy;reflexivity].
 - reflexivity.
 - exact Lookup.
 - exact Offset.
Qed.

Lemma eval_globalz_table_field e le m br i fid delta ty :
 0<=i<8 -> In (fid,delta) [(_x,0);(_y,40);(_infinity,80)] ->
 le!_a=Some (Vptr br Ptrofs.zero) -> le!_i=Some (Vlong (Int64.repr i)) ->
 eval_lvalue secp_ge e le m (globalz_table_field fid ty) br (Ptrofs.repr (88*i+delta)) Full.
Proof.
 intros Index Field A IndexTemp.
 destruct (curve_affine_layout fid delta Field) as (co & Lookup & Offset).
 assert (Bound:0<=delta<=80) by
  (destruct Field as [Same|[Same|[Same|Same]]];try contradiction;inversion Same;lia).
 replace (Ptrofs.repr (88*i+delta)) with (Ptrofs.add (Ptrofs.repr (88*i)) (Ptrofs.repr delta)).
 - unfold globalz_table_field;eapply eval_Efield_struct with (co:=co) (delta:=delta).
   + eapply eval_Elvalue.
     * apply eval_Ederef;apply eval_globalz_indexed_entry with (br:=br) (i:=i);assumption.
     * apply deref_loc_copy;reflexivity.
   + reflexivity.
   + exact Lookup.
   + exact Offset.
 - unfold Ptrofs.add;rewrite !Ptrofs.unsigned_repr by
    (change Ptrofs.max_unsigned with 18446744073709551615;lia);reflexivity.
Qed.

Theorem exec_globalz_prepare e le x y m br bt i :
 0<=i<8 -> br<>bt -> e!_tmpa=Some (bt,Tstruct __6123 noattr) ->
 le!_a=Some (Vptr br Ptrofs.zero) -> le!_i=Some (Vlong (Int64.repr i)) ->
 fe_at m br (88*i+0) (words5 x) -> fe_at m br (88*i+40) (words5 y) ->
 Mem.range_perm m bt 0 128 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m globalz_prepare E0 le mf Out_normal /\
 fe_at mf bt 0 (words5 x) /\ fe_at mf bt 40 (words5 y) /\
 Mem.load Mint32 mf bt 120=Some (Vint Int.zero) /\
 (forall b pos k p,Mem.perm mf b pos k p <-> Mem.perm m b pos k p) /\
 lframe (fun b pos=>b<>bt \/ pos<0 \/ 124<=pos) m mf /\ readonly_preserved m mf.
Proof.
 intros Index Sep Tmp A IndexTemp X Y Free.
 destruct (exec_field_copy_owned e le m
   (globalz_table_field _x curve_fe_type) (globalz_tmp_field _x curve_fe_type)
   br (88*i+0) bt 0 x eq_refl eq_refl
   ltac:(eapply eval_Elvalue;[apply eval_globalz_table_field with (i:=i);[exact Index|left;reflexivity|exact A|exact IndexTemp]|
     apply deref_loc_copy;reflexivity])
   ltac:(apply eval_globalz_tmp_field;[left;reflexivity|exact Tmp]) Sep X
   ltac:(lia) ltac:(exists 0;reflexivity) ltac:(change (40<=18446744073709551615);lia)
   ltac:(intros pos Range;apply Free;lia)) as (m1 & CopyX & X1 & PermX & FrameX).
 assert (Y1:fe_at m1 br (88*i+40) (words5 y)) by
  (eapply field_at_lframe;[exact Y|exact FrameX|];intros;left;exact Sep).
 assert (Free1:Mem.range_perm m1 bt 0 128 Cur Freeable).
 { intros pos Range;apply (proj2 (PermX bt pos Cur Freeable));apply Free;exact Range. }
 destruct (exec_field_copy_owned e le m1
   (globalz_table_field _y curve_fe_type) (globalz_tmp_field _y curve_fe_type)
   br (88*i+40) bt 40 y eq_refl eq_refl
   ltac:(eapply eval_Elvalue;[apply eval_globalz_table_field with (i:=i);[exact Index|right;left;reflexivity|exact A|exact IndexTemp]|
     apply deref_loc_copy;reflexivity])
   ltac:(apply eval_globalz_tmp_field;[right;left;reflexivity|exact Tmp]) Sep Y1
   ltac:(lia) ltac:(exists 5;reflexivity) ltac:(change (80<=18446744073709551615);lia)
   ltac:(intros pos Range;apply Free1;lia)) as (m2 & CopyY & Y2 & PermY & FrameY).
 assert (X2:fe_at m2 bt 0 (words5 x)).
 { eapply curve_keep_field_range;[reflexivity|exact X1|exact FrameY|];intros pos Range;right;left;lia. }
 assert (Free2:Mem.range_perm m2 bt 0 128 Cur Freeable).
 { intros pos Range;apply (proj2 (PermY bt pos Cur Freeable));apply Free1;exact Range. }
 assert (Access:Mem.valid_access m2 Mint32 bt 120 Writable).
 { split;[intros pos Range;apply (freeable_range_writable _ _ _ _ Free2);change (120<=pos<124) in Range;lia|
    change (4|120);exists 30;reflexivity]. }
 destruct (Mem.valid_access_store m2 Mint32 bt 120 (Vint Int.zero) Access) as (mf & Store).
 assert (FrameFlag:lframe (fun b pos=>b<>bt \/ pos<120 \/ 124<=pos) m2 mf).
 { apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact Store|].
   intros pos Range;change (120<=pos<124) in Range;intros [NE|[Low|High]];[contradiction|lia|lia]. }
 assert (FlagStmt:Clight2.exec_stmt secp_ge e le m2 globalz_finite_statement E0 le mf Out_normal).
 { unfold globalz_finite_statement;eapply exec_Sassign with (loc:=bt) (ofs:=Ptrofs.repr 120) (bf:=Full)
    (v2:=Vint Int.zero) (v:=Vint Int.zero).
   - apply eval_globalz_tmp_field;[right;right;left;reflexivity|exact Tmp].
   - constructor.
   - reflexivity.
   - eapply assign_loc_value with (chunk:=Mint32);[reflexivity|exact Store]. }
 assert (ReadonlyX:readonly_preserved m m1) by
  (inversion CopyX;subst;eapply assign_preserved;eassumption).
 assert (ReadonlyY:readonly_preserved m1 m2) by
  (inversion CopyY;subst;eapply assign_preserved;eassumption).
 exists mf;split.
 - unfold globalz_prepare,globalz_prepare_statements;cbn [statement_sequence].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m1);[exact CopyX|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m2);[exact CopyY|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mf);[exact FlagStmt|constructor].
 - split.
   + eapply curve_keep_field_range;[reflexivity|exact X2|exact FrameFlag|];intros pos Range;right;left;lia.
   + split.
     * eapply curve_keep_field_range;[reflexivity|exact Y2|exact FrameFlag|];intros pos Range;right;left;lia.
     * split;[exact (Mem.load_store_same _ _ _ _ _ _ Store)|];split.
       { intros b pos k p;rewrite <- (PermX b pos k p), <- (PermY b pos k p);split;intro Perm;
          [eapply Mem.perm_store_2|eapply Mem.perm_store_1];eassumption. }
       split.
       { eapply lframe_trans.
         - eapply lframe_implies;[exact FrameX|];intros b pos [NE|[Low|High]] Valid;
            [left;exact NE|right;left;exact Low|right;right;lia].
         - eapply lframe_trans;eapply lframe_implies;[exact FrameY| |exact FrameFlag|];
            intros b pos [NE|[Low|High]] Valid;
            [left;exact NE|right;left;lia|right;right;lia|
             left;exact NE|right;left;lia|right;right;lia]. }
       eapply preserved_trans;[exact ReadonlyX|];eapply preserved_trans;[exact ReadonlyY|].
       eapply store_preserved;exact Store.
Qed.
