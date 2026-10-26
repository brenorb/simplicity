(** One original odd-multiple-table iteration: the actual indexed-ratio
    mixed call, affine table writer and index increment. All helper execution
    premises are derived from the initial storage and bounds. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_odd_table_write C.jet_secp_mixed_function_ratio_slice C.jet_secp_mixed_body_ratio_slice
 C.jet_secp_mixed_body_loose C.jet_secp_mixed_finite_loose C.jet_secp_curve_statements
 C.jet_secp_statement_prefix C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
 C.jet_secp_field_read_preservation C.jet_secp_curve_frame C.jet_secp_slice_permissions
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition odd_table_loop := match
 nth 7 (fst (split_statement_last (fn_body f_secp256k1_ecmult_odd_multiples_table))) Sskip with
 | Ssequence _ loop => loop | _ => Sskip end.
Definition odd_table_loop_body := match odd_table_loop with
 | Sloop (Ssequence _ body) _ => body | _ => Sskip end.
Definition odd_table_increment := match odd_table_loop with
 | Sloop _ step => step | _ => Sskip end.
Definition odd_table_add_statement := match odd_table_loop_body with
 | Ssequence addition _ => addition | _ => Sskip end.
Definition odd_table_iteration := Ssequence odd_table_loop_body odd_table_increment.
Definition odd_table_point_address := Eaddrof (Evar _ai (Tstruct __6123 noattr))
 (tptr (Tstruct __6123 noattr)).
Definition odd_table_affine_address := Eaddrof (Evar _d_ge curve_ge_type) (tptr curve_ge_type).
Definition odd_table_ratio_address := Ebinop Oadd (Etempvar _zr (tptr curve_fe_type))
 (Etempvar _i tint) (tptr curve_fe_type).
Definition odd_table_iteration_temps le i := PTree.set _i (Vint (Int.repr (i+1))) le.
Definition odd_table_iteration_frame (br ba bg bz:block) i (b:block) pos :=
 b<>ba /\ b<>bg /\ (b<>br \/ pos<88*i \/ 88*i+84<=pos) /\
 (b<>bz \/ pos<40*i \/ 40*i+40<=pos).

Lemma odd_table_iteration_source : odd_table_iteration=
 Ssequence (Ssequence odd_table_add_statement odd_table_write_statement)
 (Sset _i (Ebinop Oadd (Etempvar _i tint) (Econst_int Int.one tint) tint)).
Proof. reflexivity. Qed.
Lemma odd_table_add_source : odd_table_add_statement=
 curve_call _secp256k1_gej_add_ge_var f_secp256k1_gej_add_ge_var None
 [odd_table_point_address;odd_table_point_address;odd_table_affine_address;odd_table_ratio_address].
Proof. reflexivity. Qed.
Lemma eval_odd_table_ratio_address e le m bz i : 0<=i<8 ->
 le!_zr=Some (Vptr bz Ptrofs.zero) -> le!_i=Some (Vint (Int.repr i)) ->
 eval_expr secp_ge e le m odd_table_ratio_address (Vptr bz (Ptrofs.repr (40*i))).
Proof.
 intros Index Ratios I;unfold odd_table_ratio_address.
 eapply eval_Ebinop with (v1:=Vptr bz Ptrofs.zero) (v2:=Vint (Int.repr i)).
 - apply eval_Etempvar;exact Ratios.
 - apply eval_Etempvar;exact I.
 - change (Some (Vptr bz (Ptrofs.add Ptrofs.zero
    (Ptrofs.mul (Ptrofs.repr 40) (Ptrofs.repr (Int.signed (Int.repr i))))))=
    Some (Vptr bz (Ptrofs.repr (40*i)))).
   rewrite Int.signed_repr by (change (-2147483648<=i<=2147483647);lia).
   rewrite Ptrofs.add_zero_l;unfold Ptrofs.mul.
   rewrite !Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615;lia);reflexivity.
Qed.
Lemma exec_odd_table_increment e le m i : 0<=i<8 -> le!_i=Some (Vint (Int.repr i)) ->
 Clight2.exec_stmt secp_ge e le m odd_table_increment E0 (odd_table_iteration_temps le i) m Out_normal.
Proof.
 intros Index I;unfold odd_table_increment,odd_table_iteration_temps;apply exec_Sset.
 eapply eval_Ebinop with (v1:=Vint (Int.repr i)) (v2:=Vint Int.one);
  [apply eval_Etempvar;exact I|constructor|].
 change (Some (Vint (Int.add (Int.repr i) Int.one))=Some (Vint (Int.repr (i+1)))).
 unfold Int.add;rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295;lia);reflexivity.
Qed.

Theorem exec_odd_table_iteration e le x y z u v flag m br ba bg bz i :
 1<=i<8 -> NoDup [br;ba;bg;bz] ->
 e!_ai=Some (ba,Tstruct __6123 noattr) -> e!_d_ge=Some (bg,curve_ge_type) ->
 e!_secp256k1_gej_add_ge_var=None -> e!_secp256k1_ge_set_xy=None ->
 le!_pre_a=Some (Vptr br Ptrofs.zero) -> le!_zr=Some (Vptr bz Ptrofs.zero) ->
 le!_i=Some (Vint (Int.repr i)) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.load Mint32 m ba 120=Some (Vint flag) ->
 fe_at m bg 0 (words5 u) -> fe_at m bg 40 (words5 v) -> Mem.load Mint32 m bg 80=Some (Vint Int.zero) ->
 Mem.range_perm m br 0 704 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable ->
 Mem.range_perm m bg 0 88 Cur Freeable -> Mem.range_perm m bz 0 320 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m odd_table_iteration E0 (odd_table_iteration_temps le i) mf Out_normal /\
 fe_at mf ba 0 (words5 (mixed_mode_body_x_words true flag x y z u v)) /\
 fe_at mf ba 40 (words5 (mixed_mode_body_y_words true flag x y z u v)) /\
 fe_at mf ba 80 (words5 (mixed_mode_body_z_words true flag x y z u v)) /\
 Mem.load Mint32 mf ba 120=Some (Vint (mixed_mode_body_flag true flag x y z u v)) /\
 fe_at mf bg 0 (words5 u) /\ fe_at mf bg 40 (words5 v) /\ Mem.load Mint32 mf bg 80=Some (Vint Int.zero) /\
 fe_at mf br (88*i) (words5 (mixed_mode_body_x_words true flag x y z u v)) /\
 fe_at mf br (88*i+40) (words5 (mixed_mode_body_y_words true flag x y z u v)) /\
 Mem.load Mint32 mf br (88*i+80)=Some (Vint Int.zero) /\
 fe_at mf bz (40*i) (words5 (mixed_mode_slice_ratio_words true flag x y z u v)) /\
 square_input_bounds (mixed_mode_body_x_words true flag x y z u v) /\
 square_input_bounds (mixed_mode_body_y_words true flag x y z u v) /\
 square_input_bounds (mixed_mode_body_z_words true flag x y z u v) /\
 square_input_bounds (mixed_mode_slice_ratio_words true flag x y z u v) /\
 Mem.range_perm mf br 0 704 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 Mem.range_perm mf bg 0 88 Cur Freeable /\ Mem.range_perm mf bz 0 320 Cur Freeable /\
 keeps_permissions m mf /\ lframe (odd_table_iteration_frame br ba bg bz i) m mf /\ readonly_preserved m mf.
Proof.
 intros Index Distinct AI DGE AddGlobal WriteGlobal Table Ratios I BX BY BZ BU BV X Y Z Flag U V GFlag
  FreeR FreeA FreeG FreeZ.
 assert (Separate:br<>ba /\ br<>bg /\ br<>bz /\ ba<>bg /\ ba<>bz /\ bg<>bz).
 { clear -Distinct;repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct;intuition congruence. }
 destruct Separate as (RA & RG & RZ & AG & AZ & GZ).
 assert (MixedDistinct:NoDup [ba;bg;bz]) by (inversion Distinct;subst;assumption).
 destruct (eval_mixed_ratio_slice_mode true x y z u v flag m ba bg bz (40*i) 320
   ltac:(lia) ltac:(exists (5*i);ring) ltac:(lia)
   ltac:(change Ptrofs.max_unsigned with 18446744073709551615;lia) MixedDistinct
   BX BY BZ BU BV Flag GFlag X Y Z U V FreeA FreeG FreeZ)
  as (m1 & Add & X1 & Y1 & Z1 & Flag1 & FreeA1 & FreeG1 & BX1 & BY1 & BZ1 & Ratio1 & FreeZ1 &
    U1 & V1 & GFlag1 & RatioBound & Keep1 & Frame1 & Readonly1).
 assert (AddRun:Clight2.exec_stmt secp_ge e le m odd_table_add_statement E0 le m1 Out_normal).
 { rewrite odd_table_add_source;eapply exec_curve_call with
    (vargs:=[Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bg Ptrofs.zero;Vptr bz (Ptrofs.repr (40*i))]) (v:=Vundef).
   - unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
   - exact AddGlobal.
   - eapply eval_Econs.
     + unfold odd_table_point_address;apply eval_Eaddrof;apply eval_Evar_local;exact AI.
     + reflexivity.
     + eapply eval_Econs.
       * unfold odd_table_point_address;apply eval_Eaddrof;apply eval_Evar_local;exact AI.
       * reflexivity.
       * eapply eval_Econs.
         -- unfold odd_table_affine_address;apply eval_Eaddrof;apply eval_Evar_local;exact DGE.
         -- reflexivity.
         -- eapply eval_Econs;[apply eval_odd_table_ratio_address with (bz:=bz) (i:=i);[lia|exact Ratios|exact I]|reflexivity|constructor].
   - exact Add. }
 assert (FreeR1:Mem.range_perm m1 br 0 704 Cur Freeable) by
  (eapply keeps_range_permissions;[exact Keep1|exact FreeR]).
 destruct (exec_odd_table_write e le _ _ m1 br ba i ltac:(lia) RA AI WriteGlobal Table I X1 Y1 FreeR1)
  as (mf & Write & TX & TY & TFlag & XF & YF & FreeRF & Perm2 & Frame2 & Readonly2).
 assert (ZF:fe_at mf ba 80 (words5 (mixed_mode_body_z_words true flag x y z u v))) by
  (eapply field_at_lframe;[exact Z1|exact Frame2|];intros;left;congruence).
 assert (FlagF:Mem.load Mint32 mf ba 120=Some (Vint (mixed_mode_body_flag true flag x y z u v))).
 { rewrite (proj1 Frame2 Mint32 ba 120);[exact Flag1| |intros;left;congruence].
   eapply Mem.perm_valid_block;apply (FreeA1 0);lia. }
 assert (UF:fe_at mf bg 0 (words5 u)) by
  (eapply field_at_lframe;[exact U1|exact Frame2|];intros;left;congruence).
 assert (VF:fe_at mf bg 40 (words5 v)) by
  (eapply field_at_lframe;[exact V1|exact Frame2|];intros;left;congruence).
 assert (GFlagF:Mem.load Mint32 mf bg 80=Some (Vint Int.zero)).
 { rewrite (proj1 Frame2 Mint32 bg 80);[exact GFlag1| |intros;left;congruence].
   eapply Mem.perm_valid_block;apply (FreeG1 0);lia. }
 assert (RatioF:fe_at mf bz (40*i) (words5 (mixed_mode_slice_ratio_words true flag x y z u v))) by
  (eapply field_at_lframe;[exact Ratio1|exact Frame2|];intros;left;congruence).
 assert (Keep:keeps_permissions m mf).
 { intros b pos k p Perm;apply (proj2 (Perm2 b pos k p));apply Keep1;exact Perm. }
 assert (FreeAF:Mem.range_perm mf ba 0 128 Cur Freeable) by
  (eapply keeps_range_permissions;[exact Keep|exact FreeA]).
 assert (FreeGF:Mem.range_perm mf bg 0 88 Cur Freeable) by
  (eapply keeps_range_permissions;[exact Keep|exact FreeG]).
 assert (FreeZF:Mem.range_perm mf bz 0 320 Cur Freeable) by
  (eapply keeps_range_permissions;[exact Keep|exact FreeZ]).
 assert (Frame:lframe (odd_table_iteration_frame br ba bg bz i) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact Frame1|];intros b pos (NA & NG & Entry & Ratio) Valid;
      split;[exact NA|];split;[exact NG|exact Ratio].
   - eapply lframe_implies;[exact Frame2|];intros b pos (NA & NG & Entry & Ratio) Valid;exact Entry. }
 assert (Readonly:readonly_preserved m mf) by
  (eapply preserved_trans;[exact Readonly1|exact Readonly2]).
 exists mf;split.
 - unfold odd_table_iteration;change (Clight2.exec_stmt secp_ge e le m
    (Ssequence (Ssequence odd_table_add_statement odd_table_write_statement) odd_table_increment)
    E0 (odd_table_iteration_temps le i) mf Out_normal).
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mf).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m1);[exact AddRun|exact Write].
   + apply exec_odd_table_increment;[lia|exact I].
 - repeat (first [assumption|split]).
Qed.
