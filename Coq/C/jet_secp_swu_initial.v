(** Execute the original SWU helper's first two calls from real storage:
    wd = t^2; x1 = negc * wd. No execution or value premise is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Integers Memory Values Events Maps.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_swu_startup C.jet_secp_swu_candidates C.jet_secp_swu_constant_product
  C.jet_secp_fe_math C.jet_secp_square_columns C.jet_secp_square_numeric
  C.jet_secp_square_separate_caller C.jet_secp_point_mul_storage C.jet_secp_field_mul_small
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
  C.jet_secp_fns C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge swu_constant_block.

Definition swu_initial_square := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
  [curve_local_address _wd;Etempvar _t (tptr curve_fe_type)].
Definition swu_initial_product := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
  [curve_local_address _x1;curve_local_address _negc;curve_local_address _wd].
Definition swu_after_initial := match fn_body f_shallue_van_de_woestijne with
  | Ssequence _ (Ssequence _ rest)=>rest | _=>Sskip end.
Lemma swu_initial_source : fn_body f_shallue_van_de_woestijne=
  Ssequence swu_initial_square (Ssequence swu_initial_product swu_after_initial).
Proof. reflexivity. Qed.
Lemma swu_square_closed : closed_stmtb secp_closed_helpers (fn_body f_secp256k1_fe_sqr)=true.
Proof. vm_compute;reflexivity. Qed.

Lemma exec_swu_square_call e le m mf bt bwd :
  e!_secp256k1_fe_sqr=None -> e!_wd=Some (bwd,curve_fe_type) ->
  le!_t=Some (Vptr bt Ptrofs.zero) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr bwd Ptrofs.zero;Vptr bt Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_initial_square E0 le mf Out_normal.
Proof.
  intros Function Wd T Call;unfold swu_initial_square;eapply exec_curve_call with
    (vargs:=[Vptr bwd Ptrofs.zero;Vptr bt Ptrofs.zero]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Function.
  - eapply eval_Econs;[apply eval_curve_local;exact Wd|reflexivity|].
    eapply eval_Econs;[apply eval_Etempvar;exact T|reflexivity|constructor].
  - exact Call.
Qed.
Lemma exec_swu_product_call e le m mf bwd bx1 :
  e!_secp256k1_fe_mul=None -> e!_wd=Some (bwd,curve_fe_type) ->
  e!_x1=Some (bx1,curve_fe_type) -> e!_negc=None ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr bx1 Ptrofs.zero;Vptr (swu_constant_block false) Ptrofs.zero;Vptr bwd Ptrofs.zero]
    E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_initial_product E0 le mf Out_normal.
Proof.
  intros Function Wd X1 Negc Call;unfold swu_initial_product;eapply exec_curve_call with
    (vargs:=[Vptr bx1 Ptrofs.zero;Vptr (swu_constant_block false) Ptrofs.zero;Vptr bwd Ptrofs.zero])
    (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Function.
  - eapply eval_Econs;[apply eval_curve_local;exact X1|reflexivity|].
    eapply eval_Econs;[apply (eval_swu_constant_address false);exact Negc|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact Wd|reflexivity|constructor].
  - exact Call.
Qed.

Definition swu_initial_a w := point_mul_words (swu_constant_digits false) (square_words w).
Theorem exec_swu_initial e le m bt bwd bx1 w :
  e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_negc=None ->
  e!_wd=Some (bwd,curve_fe_type) -> e!_x1=Some (bx1,curve_fe_type) ->
  le!_t=Some (Vptr bt Ptrofs.zero) -> NoDup [bt;bwd;bx1] -> swu_startup m ->
  square_input_bounds w -> fe_at m bt 0 (words5 w) ->
  Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bwd 0 40 Cur Freeable ->
  Mem.range_perm m bx1 0 40 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m (Ssequence swu_initial_square swu_initial_product) E0 le mf Out_normal /\
  fe_at mf bt 0 (words5 w) /\ fe_at mf bwd 0 (words5 (square_words w)) /\
  fe_at mf bx1 0 (words5 (swu_initial_a w)) /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  Mem.range_perm mf bwd 0 40 Cur Freeable /\ Mem.range_perm mf bx1 0 40 Cur Freeable /\
  radix_value (swu_initial_a w) mod feP=(swu_negc_constant*(radix_value w*radix_value w)) mod feP /\
  mul_small_input_bounds (swu_initial_a w) /\ swu_startup mf /\
  lframe (fun b _=>b<>bt /\ b<>bwd /\ b<>bx1) m mf /\ readonly_preserved m mf.
Proof.
  intros ES EM EN EW EX T Sep Ready Bounds Input FT FW FX.
  assert (Pairs:bt<>bwd /\ bt<>bx1 /\ bwd<>bx1).
  { repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence. }
  destruct Pairs as [TW [TX WX]].
  destruct (eval_square_separate_from_storage w m bwd bt Bounds FW Input FT ltac:(congruence))
    as (ms & Square & SQ & FWS & InputS & FTS & SqValue & SqBounds & FrameS).
  assert (ReadonlyS:readonly_preserved m ms).
  { eapply secp_closed_function_preserved;[exact swu_square_closed|reflexivity|exact Square]. }
  assert (ReadyS:swu_startup ms) by (apply (swu_startup_preserved m ms Ready ReadonlyS)).
  assert (FXS:Mem.range_perm ms bx1 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FX|exact FrameS|];intros;split;congruence. }
  destruct (eval_swu_constant_product false (square_words w) ms bx1 bwd
    ltac:(congruence) ReadyS SqBounds FXS SQ FWS)
    as (mf & Multiply & A & SQF & FXF & FWF & ReadyF & Value & Tight & FrameM & ReadonlyM).
  assert (InputF:fe_at mf bt 0 (words5 w)).
  { eapply curve_keep_field_range;[reflexivity|exact InputS|exact FrameM|];intros;split;congruence. }
  assert (FTF:Mem.range_perm mf bt 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FTS|exact FrameM|];intros;split;congruence. }
  rewrite field_prime_matches_normalizer in SqValue.
  change (radix_value (swu_initial_a w) mod feP=
    (swu_negc_constant*radix_value (square_words w)) mod feP) in Value.
  rewrite <-Z.mul_mod_idemp_r,SqValue,Z.mul_mod_idemp_r in Value by (unfold feP,feR;lia).
  exists mf;split.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=ms).
    + eapply exec_swu_square_call;eassumption.
    + eapply exec_swu_product_call;eassumption.
  - split;[exact InputF|];split;[exact SQF|];split;[exact A|];split;[exact FTF|];
      split;[exact FWF|];split;[exact FXF|];split;[exact Value|];split;[exact Tight|];
      split;[exact ReadyF|];split.
    + eapply lframe_trans;
        [eapply lframe_implies;[exact FrameS|]|eapply lframe_implies;[exact FrameM|]];
        intros b pos H _;intuition congruence.
    + eapply preserved_trans;[exact ReadonlyS|exact ReadonlyM].
Qed.
