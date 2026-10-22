(** Original mixed-addition early branches with a non-NULL ratio pointer: the
    incoming-infinity branch clears it and the H=0, I<>0 branch sets it to zero. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
  C.jet_secp_field_zero_owned C.jet_secp_mixed_zero C.jet_secp_mixed_zero_branch
  C.jet_secp_mixed_head C.jet_secp_double_var_ratio C.jet_secp_double_var_statements
  C.jet_secp_gej_set_ge_owned C.jet_secp_gej_infinity_owned C.jet_secp_point_set_bit
  C.jet_secp_fe_clear_memory C.jet_secp_fe_set_owned C.jet_secp_local_regions C.jet_secp_double_flag.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition zero_words : nat -> int64 := fun _ => Int64.zero.

Local Ltac original_pure := unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
Local Ltac keep_temp H := rewrite PTree.gso by discriminate;exact H.
Local Ltac keep_branch_field HF Frame :=
  eapply field_at_lframe;[exact HF|exact Frame|];intro pos;repeat split;congruence.
Local Ltac keep_branch_free HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;congruence.

Lemma eval_mixed_ratio_clear_owned m br : Mem.range_perm m br 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_clear) [Vptr br Ptrofs.zero] E0 mf Vundef /\
  fe_at mf br 0 (words5 zero_words) /\
  Mem.range_perm mf br 0 40 Cur Freeable /\ lframe (fun b _=>b<>br) m mf.
Proof.
  intro RF.
  destruct (eval_fe_clear_owned m br 0 ltac:(lia) ltac:(exists 0;reflexivity)
    ltac:(change (40<=18446744073709551615);lia) (freeable_range_writable _ _ _ _ RF))
    as (mf & HC & Field & Loads & Perms & Valid).
  exists mf;split;[exact HC|];split;[exact Field|];split.
  - intros pos HP;apply (proj2 (Perms br pos Cur Freeable));apply RF;exact HP.
  - split.
    + intros ch b ofs HV HO;apply Loads;left;apply (HO ofs).
      pose proof (size_chunk_pos ch);lia.
    + split;[intros b pos k p HV HO HP;apply (proj2 (Perms b pos k p));exact HP|exact Valid].
Qed.

Lemma exec_mixed_head_infinite_ratio e le m mc mf ba br bb flag :
  le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
  le!_b=Some (Vptr bb Ptrofs.zero) -> le!_rzr=Some (Vptr br Ptrofs.zero) ->
  e!_secp256k1_gej_set_ge=None -> e!_secp256k1_fe_clear=None ->
  Mem.load Mint32 m ba 120=Some (Vint flag) -> flag<>Int.zero ->
  Mem.range_perm m br 0 40 Cur Freeable ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_clear) [Vptr br Ptrofs.zero] E0 mc Vundef ->
  Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_gej_set_ge)
    [Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m mixed_head E0
    (PTree.set _t'4 (Vint flag) le) mf (Out_return None).
Proof.
  intros HA HR HB HN HE HClr HF HFlag RF CC HC;unfold mixed_head.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'4 (Vint flag) le).
  - apply exec_Sset;eapply eval_Elvalue.
    + apply eval_double_flag_field;exact HA.
    + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
      change (Mem.load Mint32 m ba 120=Some (Vint flag));exact HF.
  - eapply exec_Sifthenelse with (v1:=Vint flag) (b:=true).
    + apply eval_Etempvar;apply PTree.gss.
    + change (Some (negb (Int.eq flag Int.zero))=Some true).
      rewrite Int.eq_false by exact HFlag;reflexivity.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'4 (Vint flag) le).
      * eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=m)
          (le1:=PTree.set _t'4 (Vint flag) le) (out1:=Out_normal).
        -- apply exec_Sskip.
        -- constructor.
        -- apply exec_Sbreak.
        -- constructor.
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=PTree.set _t'4 (Vint flag) le).
        -- eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
           ++ apply eval_double_var_nonnull_test with (br:=br);
                [keep_temp HN|apply Mem.valid_pointer_nonempty_perm;
                  eapply Mem.perm_implies;[apply (RF 0);lia|constructor]].
           ++ reflexivity.
           ++ change (Clight2.exec_stmt secp_ge e (PTree.set _t'4 (Vint flag) le) m
                (curve_call _secp256k1_fe_clear f_secp256k1_fe_clear None [Etempvar _rzr (tptr curve_fe_type)])
                E0 (PTree.set _t'4 (Vint flag) le) mc Out_normal).
              eapply exec_curve_call with (vargs:=[Vptr br Ptrofs.zero]) (v:=Vundef).
              ** original_pure.
              ** exact HClr.
              ** eapply eval_Econs;[apply eval_Etempvar;keep_temp HN|reflexivity|constructor].
              ** exact CC.
        -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set _t'4 (Vint flag) le).
           ++ change (Clight2.exec_stmt secp_ge e (PTree.set _t'4 (Vint flag) le) mc
                (curve_call _secp256k1_gej_set_ge f_secp256k1_gej_set_ge None
                  [Etempvar _r (tptr (Tstruct __6123 noattr));Etempvar _b (tptr (Tstruct __6121 noattr))])
                E0 (PTree.set _t'4 (Vint flag) le) mf Out_normal).
              eapply exec_curve_call with (vargs:=[Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero]) (v:=Vundef).
              ** original_pure.
              ** exact HE.
              ** eapply eval_Econs;[apply eval_Etempvar;keep_temp HR|reflexivity|].
                 eapply eval_Econs;[apply eval_Etempvar;keep_temp HB|reflexivity|constructor].
              ** exact HC.
           ++ apply exec_Sreturn_none.
Qed.

Theorem mixed_infinite_body_ratio e le m ba bb br x y flag :
  le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
  le!_b=Some (Vptr bb Ptrofs.zero) -> le!_rzr=Some (Vptr br Ptrofs.zero) ->
  e!_secp256k1_gej_set_ge=None -> e!_secp256k1_fe_clear=None ->
  ba<>bb -> ba<>br -> bb<>br ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m br 0 40 Cur Freeable ->
  Mem.load Mint32 m ba 120=Some (Vint flag) -> flag<>Int.zero ->
  fe_at m bb 0 (words5 x) -> fe_at m bb 40 (words5 y) ->
  Mem.load Mint32 m bb 80=Some (Vint Int.zero) ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_ge_var) E0
    (PTree.set _t'4 (Vint flag) le) mf (Out_return None) /\
  fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\
  fe_at mf ba 80 (words5 (point_set_bit_words true)) /\
  Mem.load Mint32 mf ba 120=Some (Vint Int.zero) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\
  fe_at mf br 0 (words5 zero_words) /\ Mem.range_perm mf br 0 40 Cur Freeable /\
  lframe (fun b _=>b<>ba /\ b<>br) m mf.
Proof.
  intros HA HR HB HN HE HClr SAB SAR SBR PF RF HFlag HNZ X Y HBF.
  destruct (eval_mixed_ratio_clear_owned m br RF) as (mc & CC & RC & RFC & FC).
  assert (VBA : Mem.valid_block m ba) by (eapply Mem.perm_valid_block;apply (PF 0);lia).
  assert (VBB : Mem.valid_block m bb).
  { eapply Mem.perm_valid_block;destruct X as (_ & _ & _ & XP & _);apply (XP 0);lia. }
  assert (XC : fe_at mc bb 0 (words5 x)) by (eapply field_at_lframe;[exact X|exact FC|];intros;congruence).
  assert (YC : fe_at mc bb 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact FC|];intros;congruence).
  assert (PFC : Mem.range_perm mc ba 0 128 Cur Freeable) by (keep_branch_free PF FC).
  assert (FlagC : Mem.load Mint32 mc ba 120=Some (Vint flag)).
  { rewrite (proj1 FC Mint32 ba 120 VBA);[exact HFlag|intros;congruence]. }
  assert (FlagBC : Mem.load Mint32 mc bb 80=Some (Vint Int.zero)).
  { rewrite (proj1 FC Mint32 bb 80 VBB);[exact HBF|intros;congruence]. }
  destruct (eval_gej_set_ge_owned mc ba bb x y Int.zero SAB PFC XC YC FlagBC)
    as (mf & HC & XO & YO & ZO & FO & PFO & Frame).
  exists mf;split.
  - rewrite mixed_body_source;eapply exec_Sseq_2.
    + eapply exec_mixed_head_infinite_ratio with (mc:=mc);eassumption.
    + discriminate.
  - assert (RFF : Mem.range_perm mf br 0 40 Cur Freeable) by (keep_branch_free RFC Frame).
    assert (RZ : fe_at mf br 0 (words5 zero_words)) by (keep_branch_field RC Frame).
    split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FO|];split;[exact PFO|].
    split;[exact RZ|];split;[exact RFF|].
    eapply lframe_trans.
    + eapply lframe_implies;[exact FC|];intros b pos (_ & NR) HV;exact NR.
    + eapply lframe_implies;[exact Frame|];intros b pos (NA & _) HV;exact NA.
Qed.

Theorem exec_mixed_inverse_branch_ratio e le m bp bi br i :
  le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vptr br Ptrofs.zero) ->
  e!_i=Some (bi,curve_fe_type) -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
  e!_secp256k1_gej_set_infinity=None -> e!_secp256k1_fe_set_int=None ->
  bp<>bi -> bp<>br -> bi<>br ->
  square_input_bounds i -> radix_value i mod feP<>0 -> fe_at m bi 0 (words5 i) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
  Mem.range_perm m br 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m mixed_zero_branch E0 (PTree.set _t'1 (Vint Int.zero) le) mf (Out_return None) /\
  fe_at mf bp 0 (repeat Int64.zero 5) /\ fe_at mf bp 40 (repeat Int64.zero 5) /\
  fe_at mf bp 80 (repeat Int64.zero 5) /\ Mem.load Mint32 mf bp 120=Some (Vint Int.one) /\
  fe_at mf bi 0 (words5 i) /\ Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  fe_at mf br 0 (words5 zero_words) /\ Mem.range_perm mf br 0 40 Cur Freeable /\
  lframe (fun bx _=>bx<>bp /\ bx<>bi /\ bx<>br) m mf.
Proof.
  intros HR HN EI EN EF ES SPI SPR SIR BI INZ I PF IF RF.
  destruct (exec_mixed_zero_call true i e le m bi EI EN BI I IF)
    as (mz & CI & IZ & IFZ & FI).
  assert (VI : field_zero_result i=Int.zero).
  { unfold field_zero_result;apply Z.eqb_neq in INZ;rewrite INZ;reflexivity. }
  rewrite VI in CI.
  assert (PFZ : Mem.range_perm mz bp 0 128 Cur Freeable) by (keep_branch_free PF FI).
  assert (RFZ : Mem.range_perm mz br 0 40 Cur Freeable) by (keep_branch_free RF FI).
  destruct (eval_fe_set_owned false mz br RFZ) as (ms & CS & RS & RFS & FS).
  assert (PFS : Mem.range_perm ms bp 0 128 Cur Freeable) by (keep_branch_free PFZ FS).
  assert (IS : fe_at ms bi 0 (words5 i)) by (keep_branch_field IZ FS).
  assert (IFS : Mem.range_perm ms bi 0 40 Cur Freeable) by (keep_branch_free IFZ FS).
  destruct (eval_gej_infinity_initializer_owned ms bp 0 ltac:(lia) ltac:(exists 0;reflexivity)
    ltac:(change (128<=18446744073709551615);lia) (freeable_range_writable _ _ _ _ PFS))
    as (mf & CF & XO & YO & ZO & FlagO & LF & Perm & Valid).
  assert (FF : lframe (fun bx _=>bx<>bp) ms mf).
  { split.
    - intros ch bx pos HV HP;apply LF;left;apply (HP pos);pose proof (size_chunk_pos ch);lia.
    - split;[intros bx pos k p HV HP HQ;apply (proj2 (Perm bx pos k p));exact HQ|exact Valid]. }
  assert (IO : fe_at mf bi 0 (words5 i)) by (keep_branch_field IS FF).
  assert (IFO : Mem.range_perm mf bi 0 40 Cur Freeable) by (keep_branch_free IFS FF).
  assert (RO : fe_at mf br 0 (words5 zero_words)) by (keep_branch_field RS FF).
  assert (RFO : Mem.range_perm mf br 0 40 Cur Freeable) by (keep_branch_free RFS FF).
  assert (PFO : Mem.range_perm mf bp 0 128 Cur Freeable).
  { intros pos HP;apply (proj2 (Perm bp pos Cur Freeable));apply PFS;exact HP. }
  assert (Frame : lframe (fun bx _=>bx<>bp /\ bx<>bi /\ bx<>br) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FI|];intros bx pos (_ & HI & _) HV;exact HI.
    - eapply lframe_trans.
      + eapply lframe_implies;[exact FS|];intros bx pos (_ & _ & HR') HV;exact HR'.
      + eapply lframe_implies;[exact FF|];intros bx pos (HP & _ & _) HV;exact HP. }
  exists mf;split.
  - rewrite mixed_i_zero_source.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set _t'1 (Vint Int.zero) le).
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz) (le1:=PTree.set _t'1 (Vint Int.zero) le).
      * exact CI.
      * rewrite mixed_i_dispatch_source;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
        -- apply eval_Etempvar;apply PTree.gss.
        -- reflexivity.
        -- rewrite mixed_inverse_source.
           eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ms) (le1:=PTree.set _t'1 (Vint Int.zero) le).
           ++ eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
              ** apply eval_double_var_nonnull_test with (br:=br);
                   [keep_temp HN|apply Mem.valid_pointer_nonempty_perm;
                     eapply Mem.perm_implies;[apply (RFZ 0);lia|constructor]].
              ** reflexivity.
              ** change (Clight2.exec_stmt secp_ge e (PTree.set _t'1 (Vint Int.zero) le) mz
                   (curve_call _secp256k1_fe_set_int f_secp256k1_fe_set_int None
                     [Etempvar _rzr (tptr curve_fe_type);Econst_int Int.zero tint])
                   E0 (PTree.set _t'1 (Vint Int.zero) le) ms Out_normal).
                 eapply exec_curve_call with (vargs:=[Vptr br Ptrofs.zero;Vint Int.zero]) (v:=Vundef).
                 --- original_pure.
                 --- exact ES.
                 --- eapply eval_Econs;[apply eval_Etempvar;keep_temp HN|reflexivity|].
                     eapply eval_Econs;[constructor|reflexivity|constructor].
                 --- exact CS.
           ++ unfold mixed_infinity_call;eapply exec_curve_call with (vargs:=[Vptr bp Ptrofs.zero]) (v:=Vundef).
              ** original_pure.
              ** exact EF.
              ** eapply eval_Econs;[apply eval_Etempvar;keep_temp HR|reflexivity|constructor].
              ** exact CF.
    + apply exec_Sreturn_none.
  - repeat (first [assumption|split]).
Qed.
