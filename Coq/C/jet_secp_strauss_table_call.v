(** Original first-point table caller, reusing the verified table functions. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_strauss_bits_max C.jet_secp_generator_globalz_call
 C.jet_secp_gej_copy_owned C.jet_secp_scalar_table_execution C.jet_secp_fe_nv
 C.jet_secp_square_columns C.jet_secp_point_mul_storage C.jet_secp_double_coordinate_numeric C.jet_secp_double_all_calls
 C.jet_secp_odd_table_loop C.jet_secp_odd_table_body C.jet_secp_scalar_table_literal C.jet_secp_table_field_equiv
 C.jet_secp_odd_table_literal_walk C.jet_secp_field_zero_owned
 C.jet_secp_globalz_loop C.jet_secp_globalz_word_walk C.jet_secp_globalz_pass2 C.jet_secp_field_mul_small
 C.jet_secp_rescale_literal C.jet_secp_multiply_normalize_bridge
 C.jet_secp_field_read_preservation C.jet_secp_slice_permissions
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Opaque secp_ge odd_table_final_state point_mul_words literal_scalar_table5.
Set Default Timeout 10.

Definition strauss_point_source := Ederef
 (Ebinop Oadd (Etempvar _a (tptr (Tstruct __6123 noattr))) (Etempvar _np tulong)
  (tptr (Tstruct __6123 noattr))) (Tstruct __6123 noattr).
Definition strauss_point_copy := Sassign (Evar _tmp (Tstruct __6123 noattr)) strauss_point_source.
Definition strauss_table_width := Ebinop Oshl (Econst_long Int64.one tlong)
 (Ebinop Osub (Econst_int (Int.repr 5) tint) (Econst_int (Int.repr 2) tint) tint) tlong.
Definition strauss_table_offset := Ebinop Omul (Etempvar _no tulong) strauss_table_width tulong.
Definition strauss_table_arg tmp ty := Ebinop Oadd (Etempvar tmp (tptr ty)) strauss_table_offset (tptr ty).
Definition strauss_odd_table_call :=
 Ssequence (Sset _t'36 (generator_state_pointer _pre_a (Tstruct __6121 noattr)))
  (Ssequence (Sset _t'37 (generator_state_pointer _aux (Tstruct __5467 noattr)))
   (curve_call _secp256k1_ecmult_odd_multiples_table f_secp256k1_ecmult_odd_multiples_table None
    [strauss_table_width;strauss_table_arg _t'36 (Tstruct __6121 noattr);
     strauss_table_arg _t'37 (Tstruct __5467 noattr);
     Eaddrof (Evar _Z (Tstruct __5467 noattr)) (tptr (Tstruct __5467 noattr));
     Eaddrof (Evar _tmp (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr))])).
Definition strauss_rescale_body := match strauss_after_bits_max with
 | Ssequence _ (Ssequence (Sifthenelse _ body _) _)=>body | _=>Sskip end.
Definition strauss_auxiliary_body := match strauss_after_bits_max with
 | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence (Sifthenelse _ body _) _)))=>body | _=>Sskip end.

Lemma strauss_first_table_source : strauss_after_bits_max=
 Ssequence strauss_point_copy
  (Ssequence (Sifthenelse (Etempvar _no tulong) strauss_rescale_body Sskip)
   (Ssequence strauss_odd_table_call
    (Ssequence (Sifthenelse (Etempvar _no tulong) strauss_auxiliary_body Sskip)
     (Sset _no (Ebinop Oadd (Etempvar _no tulong) (Econst_int Int.one tint) tulong))))).
Proof. reflexivity. Qed.

Definition strauss_table_call_temps le bt bx :=
 PTree.set _t'37 (Vptr bx Ptrofs.zero) (PTree.set _t'36 (Vptr bt Ptrofs.zero) le).
Definition strauss_first_table_temps le bt bx :=
 PTree.set _no (Vlong Int64.one) (strauss_table_call_temps le bt bx).
Definition strauss_table_prepare := Ssequence strauss_after_bits_max generator_globalz_statement.
Definition strauss_table_prepare_temps le bt bx :=
 generator_globalz_call_temps (strauss_first_table_temps le bt bx) (Vptr bt Ptrofs.zero) (Vptr bx Ptrofs.zero).

Lemma eval_strauss_point_source e le m ba : le!_a=Some (Vptr ba Ptrofs.zero) ->
 le!_np=Some (Vlong Int64.zero) -> eval_expr secp_ge e le m strauss_point_source (Vptr ba Ptrofs.zero).
Proof.
 intros A NP;unfold strauss_point_source;eapply eval_Elvalue with (loc:=ba) (ofs:=Ptrofs.zero) (bf:=Full).
 - apply eval_Ederef;eapply eval_Ebinop with (v1:=Vptr ba Ptrofs.zero) (v2:=Vlong Int64.zero);
   [apply eval_Etempvar;exact A|apply eval_Etempvar;exact NP|reflexivity].
 - apply deref_loc_copy;reflexivity.
Qed.
Lemma eval_strauss_table_width e le m :
 eval_expr secp_ge e le m strauss_table_width (Vlong (Int64.repr 8)).
Proof.
 unfold strauss_table_width;eapply eval_Ebinop with (v1:=Vlong Int64.one) (v2:=Vint (Int.repr 3));
  [constructor|eapply eval_Ebinop;[constructor|constructor|reflexivity]|reflexivity].
Qed.
Lemma eval_strauss_table_offset e le m : le!_no=Some (Vlong Int64.zero) ->
 eval_expr secp_ge e le m strauss_table_offset (Vlong Int64.zero).
Proof.
 intro No;unfold strauss_table_offset;eapply eval_Ebinop with
  (v1:=Vlong Int64.zero) (v2:=Vlong (Int64.repr 8));
  [apply eval_Etempvar;exact No|apply eval_strauss_table_width|reflexivity].
Qed.
Lemma eval_strauss_table_arg e le m tmp ty b :
 le!tmp=Some (Vptr b Ptrofs.zero) -> le!_no=Some (Vlong Int64.zero) ->
 eval_expr secp_ge e le m (strauss_table_arg tmp ty) (Vptr b Ptrofs.zero).
Proof.
 intros Pointer No;unfold strauss_table_arg;eapply eval_Ebinop with
  (v1:=Vptr b Ptrofs.zero) (v2:=Vlong Int64.zero);
  [apply eval_Etempvar;exact Pointer|apply eval_strauss_table_offset;exact No|].
 unfold sem_binary_operation,sem_add,sem_add_ptr_long.
 change (Some (Vptr b (Ptrofs.add Ptrofs.zero
  (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv secp_ge) ty)) Ptrofs.zero)))=Some (Vptr b Ptrofs.zero)).
 rewrite Ptrofs.mul_zero,Ptrofs.add_zero;reflexivity.
Qed.

Lemma exec_strauss_odd_table_from_call e le m mf bs bt bx bo bj :
 e!_Z=Some (bo,Tstruct __5467 noattr) -> e!_tmp=Some (bj,Tstruct __6123 noattr) ->
 e!_secp256k1_ecmult_odd_multiples_table=None ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_no=Some (Vlong Int64.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_odd_multiples_table)
  [Vint (Int.repr 8);Vptr bt Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr bo Ptrofs.zero;Vptr bj Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m strauss_odd_table_call E0 (strauss_table_call_temps le bt bx) mf Out_normal.
Proof.
 intros LocalZ LocalTmp Symbol State No Table Aux Call.
 pose (lt:=PTree.set _t'36 (Vptr bt Ptrofs.zero) le).
 pose (lx:=strauss_table_call_temps le bt bx).
 assert (StateT:lt!_state=Some (Vptr bs Ptrofs.zero)).
 { unfold lt;rewrite PTree.gso by discriminate;exact State. }
 assert (NoX:lx!_no=Some (Vlong Int64.zero)).
 { unfold lx,strauss_table_call_temps;rewrite !PTree.gso by discriminate;exact No. }
 unfold strauss_odd_table_call;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lt) (m1:=m).
 - apply exec_Sset;eapply eval_generator_state_pointer with (base:=0) (delta:=8);
   [left;reflexivity|exact State|lia|change Ptrofs.max_unsigned with 18446744073709551615;lia|exact Table].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lx) (m1:=m).
   + apply exec_Sset;eapply eval_generator_state_pointer with (base:=0) (delta:=0);
     [right;left;reflexivity|exact StateT|lia|change Ptrofs.max_unsigned with 18446744073709551615;lia|exact Aux].
   + eapply exec_curve_call with
      (vargs:=[Vint (Int.repr 8);Vptr bt Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr bo Ptrofs.zero;Vptr bj Ptrofs.zero]) (v:=Vundef).
     * unfold secp_pure;repeat first [left;reflexivity|right].
     * exact Symbol.
     * eapply eval_Econs with (v1:=Vlong (Int64.repr 8));[apply eval_strauss_table_width|reflexivity|].
       eapply eval_Econs with (v1:=Vptr bt Ptrofs.zero).
       -- apply eval_strauss_table_arg;[unfold lx,strauss_table_call_temps;rewrite PTree.gso by discriminate;apply PTree.gss|exact NoX].
       -- reflexivity.
       -- eapply eval_Econs with (v1:=Vptr bx Ptrofs.zero).
          ++ apply eval_strauss_table_arg;[unfold lx,strauss_table_call_temps;apply PTree.gss|exact NoX].
          ++ reflexivity.
          ++ eapply eval_Econs with (v1:=Vptr bo Ptrofs.zero);
             [apply eval_Eaddrof;apply eval_Evar_local;exact LocalZ|reflexivity|].
             eapply eval_Econs with (v1:=Vptr bj Ptrofs.zero);
             [apply eval_Eaddrof;apply eval_Evar_local;exact LocalTmp|reflexivity|constructor].
     * exact Call.
Qed.

Lemma exec_strauss_first_table_from_calls e le m mc mf bs bt bx bo bj :
 e!_Z=Some (bo,Tstruct __5467 noattr) -> e!_tmp=Some (bj,Tstruct __6123 noattr) ->
 e!_secp256k1_ecmult_odd_multiples_table=None ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_no=Some (Vlong Int64.zero) ->
 Mem.load Mptr mc bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr mc bs 0=Some (Vptr bx Ptrofs.zero) ->
 Clight2.exec_stmt secp_ge e le m strauss_point_copy E0 le mc Out_normal ->
 Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ecmult_odd_multiples_table)
  [Vint (Int.repr 8);Vptr bt Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr bo Ptrofs.zero;Vptr bj Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m strauss_after_bits_max E0 (strauss_first_table_temps le bt bx) mf Out_normal.
Proof.
 intros LocalZ LocalTmp Symbol State No Table Aux Copy Call;rewrite strauss_first_table_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Copy|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
 - eapply exec_Sifthenelse with (v1:=Vlong Int64.zero) (b:=Datatypes.false);
   [apply eval_Etempvar;exact No|reflexivity|constructor].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
   + exact (exec_strauss_odd_table_from_call e le mc mf bs bt bx bo bj
      LocalZ LocalTmp Symbol State No Table Aux Call).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
     * eapply exec_Sifthenelse with (v1:=Vlong Int64.zero) (b:=Datatypes.false);
       [apply eval_Etempvar;unfold strauss_table_call_temps;rewrite !PTree.gso by discriminate;exact No|reflexivity|constructor].
     * apply exec_Sset;eapply eval_Ebinop with (v1:=Vlong Int64.zero) (v2:=Vint Int.one);
       [apply eval_Etempvar;unfold strauss_table_call_temps;rewrite !PTree.gso by discriminate;exact No|constructor|reflexivity].
Qed.

Lemma eval_strauss_globalz_count e le m : le!_no=Some (Vlong Int64.one) ->
 eval_expr secp_ge e le m generator_globalz_count (Vlong (Int64.repr 8)).
Proof.
 intro No;unfold generator_globalz_count;eapply eval_Ebinop with
  (v1:=Vlong (Int64.repr 8)) (v2:=Vlong Int64.one);
  [apply eval_strauss_table_width|apply eval_Etempvar;exact No|reflexivity].
Qed.
Lemma exec_strauss_globalz_from_call e le m mf bs bt bx :
 e!_secp256k1_ge_table_set_globalz=None -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_no=Some (Vlong Int64.one) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_table_set_globalz)
  [Vlong (Int64.repr 8);Vptr bt Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m generator_globalz_statement E0
  (generator_globalz_call_temps le (Vptr bt Ptrofs.zero) (Vptr bx Ptrofs.zero)) mf Out_normal.
Proof.
 intros Symbol State No Table Aux Call;rewrite generator_globalz_statement_source.
 pose (lt:=PTree.set _t'32 (Vptr bt Ptrofs.zero) le).
 pose (lx:=generator_globalz_call_temps le (Vptr bt Ptrofs.zero) (Vptr bx Ptrofs.zero)).
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lt) (m1:=m).
 - apply exec_Sset;eapply eval_generator_state_pointer with (base:=0) (delta:=8);
   [left;reflexivity|exact State|lia|change Ptrofs.max_unsigned with 18446744073709551615;lia|exact Table].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lx) (m1:=m).
   + apply exec_Sset;eapply eval_generator_state_pointer with (base:=0) (delta:=0).
     * right;left;reflexivity.
     * unfold lt;rewrite PTree.gso by discriminate;exact State.
     * lia.
     * change Ptrofs.max_unsigned with 18446744073709551615;lia.
     * exact Aux.
   + eapply exec_curve_call with
     (vargs:=[Vlong (Int64.repr 8);Vptr bt Ptrofs.zero;Vptr bx Ptrofs.zero]) (v:=Vundef).
     * unfold secp_pure;repeat first [left;reflexivity|right].
     * exact Symbol.
     * eapply eval_Econs with (v1:=Vlong (Int64.repr 8)).
       -- apply eval_strauss_globalz_count;unfold lx,generator_globalz_call_temps;
          rewrite !PTree.gso by discriminate;exact No.
       -- reflexivity.
       -- eapply eval_Econs with (v1:=Vptr bt Ptrofs.zero).
          ++ apply eval_Etempvar;unfold lx,generator_globalz_call_temps;rewrite PTree.gso by discriminate;apply PTree.gss.
          ++ reflexivity.
          ++ eapply eval_Econs with (v1:=Vptr bx Ptrofs.zero);
             [apply eval_Etempvar;unfold lx,generator_globalz_call_temps;apply PTree.gss|reflexivity|constructor].
     * exact Call.
Qed.

Theorem exec_strauss_table_prepare e le m ba bs bt bx bo bj x y z
 (ax ay az:Ty.tySem (Word 8)) :
 e!_Z=Some (bo,Tstruct __5467 noattr) -> e!_tmp=Some (bj,Tstruct __6123 noattr) ->
 e!_secp256k1_ecmult_odd_multiples_table=None -> e!_secp256k1_ge_table_set_globalz=None ->
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_np=Some (Vlong Int64.zero) ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_no=Some (Vlong Int64.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
 (forall b hi,In (b,hi) [(bs,24);(ba,128);(bj,128);(bt,704);(bx,320);(bo,40)] ->
  Mem.range_perm m b 0 hi Cur Freeable) -> NoDup [ba;bs;bt;bx;bo;bj] ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az -> field_zero_result z=Int.zero ->
 let sf:=odd_table_final_state x y z in exists mf xf yf,
 Clight2.exec_stmt secp_ge e le m strauss_table_prepare E0 (strauss_table_prepare_temps le bt bx) mf Out_normal /\
 globalz_table_rep mf bt xf yf /\ globalz_table_bounds xf yf /\
 (forall k,(k<8)%nat -> mul_small_input_bounds (yf k)) /\
 fe_at mf bo 0 (words5 (point_mul_words (odd_table_z sf) (double_output_z_words y z))) /\
 square_input_bounds (point_mul_words (odd_table_z sf) (double_output_z_words y z)) /\
 (rescale_field_output (point_mul_words (odd_table_z sf) (double_output_z_words y z)),
  globalz_word_vector (globalz_decoded_points xf yf))=@literal_scalar_table5 Alg.CoreFunSem ((ax,ay),az) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
 Mem.load Mint32 mf ba 120=Some (Vint Int.zero) /\
 Mem.load Mptr mf bs 8=Some (Vptr bt Ptrofs.zero) /\ Mem.load Mptr mf bs 0=Some (Vptr bx Ptrofs.zero) /\
 (forall b hi,In (b,hi) [(bs,24);(ba,128);(bj,128);(bt,704);(bx,320);(bo,40)] ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\ keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun b _=>b<>bt /\ b<>bj /\ b<>bx /\ b<>bo) m mf /\
 (strauss_table_prepare_temps le bt bx)!_no=Some (Vlong Int64.one) /\
 (forall id,~In id [_no;_t'32;_t'33;_t'36;_t'37] ->
  (strauss_table_prepare_temps le bt bx)!id=le!id) /\
 (exists m1,
  Clight2.exec_stmt secp_ge e le m strauss_after_bits_max E0 (strauss_first_table_temps le bt bx) m1 Out_normal /\
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_ge_table_set_globalz)
   [Vlong (Int64.repr 8);Vptr bt Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf Vundef /\
  Mem.load Mptr m1 bs 8=Some (Vptr bt Ptrofs.zero) /\ Mem.load Mptr m1 bs 0=Some (Vptr bx Ptrofs.zero)).
Proof.
 intros LocalZ LocalTmp OddSymbol GlobalSymbol A NP State No Table Aux BX BY BZ X Y Z Flag
  Owned Separate HX HY HZ Finite;cbv zeta.
 assert (FreeS:Mem.range_perm m bs 0 24 Cur Freeable) by (apply Owned;cbn [In];tauto).
 assert (FreeA:Mem.range_perm m ba 0 128 Cur Freeable) by (apply Owned;cbn [In];tauto).
 assert (FreeJ:Mem.range_perm m bj 0 128 Cur Freeable) by (apply Owned;cbn [In];tauto).
 assert (FreeT:Mem.range_perm m bt 0 704 Cur Freeable) by (apply Owned;cbn [In];tauto).
 assert (FreeX:Mem.range_perm m bx 0 320 Cur Freeable) by (apply Owned;cbn [In];tauto).
 assert (FreeO:Mem.range_perm m bo 0 40 Cur Freeable) by (apply Owned;cbn [In];tauto).
 assert (D:ba<>bs /\ ba<>bt /\ ba<>bx /\ ba<>bo /\ ba<>bj /\
  bs<>bt /\ bs<>bx /\ bs<>bo /\ bs<>bj /\ bt<>bx /\ bt<>bo /\ bt<>bj /\ bx<>bo /\ bx<>bj /\ bo<>bj).
 { repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence. }
 assert (TableSeparate:NoDup [bt;bj;bx;bo]).
 { repeat constructor;cbn [In];intuition congruence. }
 destruct (exec_gej_copy_owned e le m strauss_point_source (Evar _tmp (Tstruct __6123 noattr))
  ba bj x y z Int.zero eq_refl eq_refl (eval_strauss_point_source e le m ba A NP)
  ltac:(apply eval_Evar_local;exact LocalTmp) ltac:(tauto) FreeA FreeJ X Y Z Flag)
  as (mc & Copy & XJ & YJ & ZJ & FlagJ & FreeAC & FreeJC & CopyFrame).
 assert (CopyKeep:keeps_permissions m mc).
 { inversion Copy;subst;eapply assign_keeps_permissions;eassumption. }
 assert (CopyReadonly:readonly_preserved m mc).
 { inversion Copy;subst;eapply assign_preserved;eassumption. }
 assert (VS:Mem.valid_block m bs) by (eapply Mem.perm_valid_block;apply (FreeS 0);lia).
 assert (VC:Mem.valid_block mc bs) by (eapply Mem.perm_valid_block;apply CopyKeep,(FreeS 0);lia).
 assert (TableC:Mem.load Mptr mc bs 8=Some (Vptr bt Ptrofs.zero)).
 { rewrite (proj1 CopyFrame Mptr bs 8 VS ltac:(intros;tauto));exact Table. }
 assert (AuxC:Mem.load Mptr mc bs 0=Some (Vptr bx Ptrofs.zero)).
 { rewrite (proj1 CopyFrame Mptr bs 0 VS ltac:(intros;tauto));exact Aux. }
 destruct (eval_scalar_table5_calls x y z mc bt bj bx bo ax ay az TableSeparate BX BY BZ
  XJ YJ ZJ FlagJ ltac:(eapply keeps_range_permissions;[exact CopyKeep|exact FreeT]) FreeJC
  ltac:(eapply keeps_range_permissions;[exact CopyKeep|exact FreeX])
  ltac:(eapply keeps_range_permissions;[exact CopyKeep|exact FreeO]) HX HY HZ Finite)
  as (m1 & mf & xf & yf & First & Second & TableF & BoundsF & TightY & Product & ProductBound &
   Literal & XJF & YJF & ZJF & FlagJF & FreeTF & FreeJF & FreeXF & FreeOF & KeepT & FrameT & ReadonlyT & FirstFrame).
 assert (Table1:Mem.load Mptr m1 bs 8=Some (Vptr bt Ptrofs.zero)).
 { rewrite (proj1 FirstFrame Mptr bs 8 VC);[exact TableC|intros;intuition congruence]. }
 assert (Aux1:Mem.load Mptr m1 bs 0=Some (Vptr bx Ptrofs.zero)).
 { rewrite (proj1 FirstFrame Mptr bs 0 VC);[exact AuxC|intros;intuition congruence]. }
 pose (l1:=strauss_first_table_temps le bt bx).
 assert (Caller:Clight2.exec_stmt secp_ge e le m strauss_after_bits_max E0 l1 m1 Out_normal).
 { exact (exec_strauss_first_table_from_calls e le m mc m1 bs bt bx bo bj
    LocalZ LocalTmp OddSymbol State No TableC AuxC Copy First). }
 assert (State1:l1!_state=Some (Vptr bs Ptrofs.zero)).
 { unfold l1,strauss_first_table_temps,strauss_table_call_temps;rewrite !PTree.gso by discriminate;exact State. }
 assert (No1:l1!_no=Some (Vlong Int64.one)) by (unfold l1,strauss_first_table_temps;apply PTree.gss).
 pose proof (exec_strauss_globalz_from_call e l1 m1 mf bs bt bx GlobalSymbol State1 No1 Table1 Aux1 Second) as Global.
 assert (Keep:keeps_permissions m mf) by (eapply keeps_permissions_trans;[exact CopyKeep|exact KeepT]).
 assert (Frame:lframe (fun b _=>b<>bt /\ b<>bj /\ b<>bx /\ b<>bo) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact CopyFrame|intros b pos (_ & J & _) _;exact J].
   - exact FrameT. }
 assert (XA:fe_at mf ba 0 (words5 x)) by (eapply field_at_lframe;[exact X|exact Frame|intros;intuition congruence]).
 assert (YA:fe_at mf ba 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact Frame|intros;intuition congruence]).
 assert (ZA:fe_at mf ba 80 (words5 z)) by (eapply field_at_lframe;[exact Z|exact Frame|intros;intuition congruence]).
 assert (VA:Mem.valid_block m ba) by (eapply Mem.perm_valid_block;apply (FreeA 0);lia).
 assert (FlagA:Mem.load Mint32 mf ba 120=Some (Vint Int.zero)).
 { rewrite (proj1 Frame Mint32 ba 120 VA);[exact Flag|intros;intuition congruence]. }
 assert (TableFinal:Mem.load Mptr mf bs 8=Some (Vptr bt Ptrofs.zero)).
 { rewrite (proj1 Frame Mptr bs 8 VS);[exact Table|intros;intuition congruence]. }
 assert (AuxFinal:Mem.load Mptr mf bs 0=Some (Vptr bx Ptrofs.zero)).
 { rewrite (proj1 Frame Mptr bs 0 VS);[exact Aux|intros;intuition congruence]. }
 exists mf,xf,yf;split.
 - unfold strauss_table_prepare,strauss_table_prepare_temps;
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Caller|exact Global].
 - split;[exact TableF|];split;[exact BoundsF|];split;[exact TightY|];split;[exact Product|];
   split;[exact ProductBound|];split;[exact Literal|];split;[exact XA|];split;[exact YA|];split;[exact ZA|];
   split;[exact FlagA|];split;[exact TableFinal|];split;[exact AuxFinal|];split.
   + intros b hi Slot pos Range;apply Keep,(Owned b hi Slot);exact Range.
   + split;[exact Keep|];split.
     * eapply preserved_trans;[exact CopyReadonly|exact ReadonlyT].
     * split;[exact Frame|];split.
       -- unfold strauss_table_prepare_temps,generator_globalz_call_temps.
          rewrite !PTree.gso by discriminate;exact No1.
       -- split.
          ++ intros id Outside;unfold strauss_table_prepare_temps,generator_globalz_call_temps,
              strauss_first_table_temps,strauss_table_call_temps;
             rewrite !PTree.gso;cbn [In] in Outside;intuition congruence.
          ++ exists m1;split;[exact Caller|];split;[exact Second|];split;[exact Table1|exact Aux1].
Qed.
