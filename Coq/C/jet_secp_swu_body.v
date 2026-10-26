(** Entire original SWU statement body from bounded machine limbs and their
    matched logical field value; the real reader theorem is a specialization.
    Function entry/freeing and the public read/write wrapper remain outside
    this theorem. The original CTZ call contract remains explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.extraMath C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_swu_startup C.jet_secp_swu_first_candidate C.jet_secp_swu_second_candidate
  C.jet_secp_swu_third_candidate C.jet_secp_swu_before_selection C.jet_secp_swu_roots
  C.jet_secp_swu_select_exec C.jet_secp_swu_selected_literal C.jet_secp_swu_parity
  C.jet_secp_swu_literal C.jet_secp_swu_literal_bridge C.jet_secp_field_odd_words C.jet_secp_swu_word_parity C.jet_secp_root_chain_numeric C.jet_secp_root_check
  C.jet_secp_root_function_literal C.jet_secp_field_cmov C.jet_secp_ge_set_xy_separate
  C.jet_secp_field_negate_separate C.jet_secp_field_mul_small C.jet_secp_square_columns
  C.jet_secp_square_spec_bridge C.jet_secp_rescale_literal C.jet_secp_multiply_normalize_bridge
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_statement_prefix C.jet_secp_fns
  C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_reader_rho root_chain_candidate literal_swu_candidates rescale_field_output.

Lemma swu_root_selection_separated (bi bw ba bx bj bb bc bA bB bC by1 by2 by3:block) :
  NoDup [bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3] -> NoDup [ba;bb;bc;by1;by2;by3].
Proof.
  intro Sep.
  pose proof (@NoDup_app_remove_l block [bi;bw] [ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3] Sep) as S0.
  pose proof (@NoDup_remove_1 block [ba] [bj;bb;bc;bA;bB;bC;by1;by2;by3] bx S0) as S1.
  pose proof (@NoDup_remove_1 block [ba] [bb;bc;bA;bB;bC;by1;by2;by3] bj S1) as S2.
  pose proof (@NoDup_remove_1 block [ba;bb;bc] [bB;bC;by1;by2;by3] bA S2) as S3.
  pose proof (@NoDup_remove_1 block [ba;bb;bc] [bC;by1;by2;by3] bB S3) as S4.
  exact (@NoDup_remove_1 block [ba;bb;bc] [by1;by2;by3] bC S4).
Qed.
Lemma exec_swu_construct_call e le m mf bp ba by1 :
  e!_secp256k1_ge_set_xy=None -> le!_ge=Some (Vptr bp Ptrofs.zero) ->
  e!_x1=Some (ba,curve_fe_type) -> e!_y1=Some (by1,curve_fe_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_xy)
    [Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr by1 Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_construct_call E0 le mf Out_normal.
Proof.
  intros Fun Ge X Y Call;unfold swu_construct_call;eapply exec_curve_call with
    (vargs:=[Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr by1 Ptrofs.zero]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_Etempvar;exact Ge|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact X|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact Y|reflexivity|constructor].
  - exact Call.
Qed.

Theorem exec_swu_body_words w t e le m bp bi bw ba bx bj bb bc bA bB bC by1 by2 by3 bt :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  plain_env e -> e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_negc=None ->
  e!_secp256k1_fe_mul_int=None -> e!_secp256k1_fe_negate=None ->
  e!_secp256k1_fe_add_int=None -> e!_secp256k1_fe_inv_var=None ->
  e!_secp256k1_fe_add=None -> e!_d=None -> e!_secp256k1_fe_sqrt_var=None ->
  e!_secp256k1_fe_cmov=None -> e!_secp256k1_ge_set_xy=None -> e!_secp256k1_fe_is_odd=None ->
  e!_wd=Some (bw,curve_fe_type) -> e!_x1=Some (ba,curve_fe_type) ->
  e!_x3d=Some (bx,curve_fe_type) -> e!_jinv=Some (bj,curve_fe_type) ->
  e!_x2=Some (bb,curve_fe_type) -> e!_x3=Some (bc,curve_fe_type) ->
  e!_alphain=Some (bA,curve_fe_type) -> e!_betain=Some (bB,curve_fe_type) ->
  e!_gammain=Some (bC,curve_fe_type) -> e!_y1=Some (by1,curve_fe_type) ->
  e!_y2=Some (by2,curve_fe_type) -> e!_y3=Some (by3,curve_fe_type) -> e!_tmp=Some (bt,curve_fe_type) ->
  le!_t=Some (Vptr bi Ptrofs.zero) -> le!_ge=Some (Vptr bp Ptrofs.zero) ->
  NoDup [bp;bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3;bt] -> swu_startup m -> root_words_match w t ->
  fe_at m bi 0 (words5 w) ->
  Forall (fun b=>Mem.range_perm m b 0 40 Cur Freeable) [bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3;bt] ->
  Mem.range_perm m bp 0 88 Cur Freeable -> exists lef mf x y,
  Clight2.exec_stmt secp_ge e le m (fn_body f_shallue_van_de_woestijne) E0 lef mf Out_normal /\
  fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\
  Mem.load Mint32 mf bp 80=Some (Vint Int.zero) /\ Mem.range_perm mf bp 0 88 Cur Freeable /\
  Forall (fun b=>Mem.range_perm mf b 0 40 Cur Freeable) [bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3;bt] /\
  square_input_bounds x /\ square_input_bounds y /\
  (rescale_field_output x,rescale_field_output y)=swu_words_literal_output w t /\
  swu_startup mf /\
  lframe (fun b _=>~In b [bp;bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3;bt]) m mf /\ readonly_preserved m mf.
Proof.
  intros Count Plain ES EM EN EC EG EA EI EAdd ED ERoot EMove ESet EOdd EW EX EXD EJ EX2 EX3 EAlpha EBeta EGamma
    EY1 EY2 EY3 ET T Ge Sep Ready Match Input Free FP.
  apply NoDup_cons_iff in Sep;destruct Sep as [PointOutside PoolSep].
  assert (RootSep:NoDup [bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3]) by
    (exact (@NoDup_app_remove_r block [bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3] [bt] PoolSep)).
  assert (TempOutside:~In bt [bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3]).
  { pose proof (@NoDup_remove_2 block [bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3] [] bt PoolSep) as OutsideTmp.
    rewrite app_nil_r in OutsideTmp;exact OutsideTmp. }
  assert (RootFree:Forall (fun b=>Mem.range_perm m b 0 40 Cur Freeable)
    [bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3]).
  { rewrite Forall_forall in *;intros b Member;apply Free;clear -Member;cbn [In] in *;tauto. }
  destruct (exec_swu_through_roots e le m bi bw ba bx bj bb bc bA bB bC by1 by2 by3 w t Count Plain
    ES EM EN EC EG EA EI EAdd ED ERoot EW EX EXD EJ EX2 EX3 EAlpha EBeta EGamma EY1 EY2 EY3 T
    RootSep Ready Match Input RootFree)
    as (inv & m1 & Roots & I1 & X1 & X2 & X3 & Y1 & Y2 & Y3 & Free1Root & Bounds & TightY & Ready1 & F1 & R1 & Literal).
  set (alpha:=root_check_flag (swu_alpha_words w inv)).
  set (beta:=root_check_flag (swu_beta_words w inv)).
  set (sx:=swu_selected_words alpha beta (swu_input_first_words w inv)
    (swu_second_words (swu_input_first_words w inv)) (swu_input_third_words w inv)).
  set (sy:=swu_selected_words alpha beta (root_chain_candidate (swu_alpha_words w inv))
    (root_chain_candidate (swu_beta_words w inv)) (root_chain_candidate (swu_gamma_words w inv))).
  set (le1:=swu_selection_temps w inv le).
  assert (A:le1!_alphaquad=Some (Vint (cmov_int alpha))) by (apply swu_roots_temps_alpha).
  assert (B:le1!_betaquad=Some (Vint (cmov_int beta))) by (apply swu_roots_temps_beta).
  assert (SelectSep:NoDup [ba;bb;bc;by1;by2;by3]) by (eapply swu_root_selection_separated;exact RootSep).
  pose proof Free1Root as All1;rewrite Forall_forall in All1.
  assert (FreeSelect:Forall (fun b=>Mem.range_perm m1 b 0 40 Cur Freeable) [ba;bb;bc;by1;by2;by3]).
  { rewrite Forall_forall;intros b Member;apply All1;clear -Member;cbn [In] in *;tauto. }
  destruct (exec_swu_select alpha beta e le1 m1 ba bb bc by1 by2 by3
    (swu_input_first_words w inv) (swu_second_words (swu_input_first_words w inv)) (swu_input_third_words w inv)
    (root_chain_candidate (swu_alpha_words w inv)) (root_chain_candidate (swu_beta_words w inv))
    (root_chain_candidate (swu_gamma_words w inv)) EMove EX EX2 EX3 EY1 EY2 EY3 A B SelectSep
    X1 X2 X3 Y1 Y2 Y3 FreeSelect) as (m2 & Select & XS & YS & Free2Select & F2 & R2).
  assert (PointRoot:~In bp [bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3]) by
    (intro Member;apply PointOutside;clear -Member;cbn [In] in *;tauto).
  assert (PointSelect:~In bp [ba;bb;bc;by1;by2;by3]) by
    (intro Member;apply PointOutside;clear -Member;cbn [In] in *;tauto).
  assert (TempSelect:~In bt [ba;bb;bc;by1;by2;by3]) by
    (intro Member;apply TempOutside;clear -Member;cbn [In] in *;tauto).
  assert (InputSelect:~In bi [ba;bb;bc;by1;by2;by3]).
  { pose proof RootSep as S;apply NoDup_cons_iff in S;destruct S as [Outside Tail].
    intro Member;apply Outside;clear -Member;cbn [In] in *;tauto. }
  assert (FP1:Mem.range_perm m1 bp 0 88 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact FP|exact F1|intros;exact PointRoot]).
  assert (FP2:Mem.range_perm m2 bp 0 88 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact FP1|exact F2|intros;exact PointSelect]).
  assert (FT0:Mem.range_perm m bt 0 40 Cur Freeable).
  { rewrite Forall_forall in Free;apply Free;do 13 right;left;reflexivity. }
  assert (FT1:Mem.range_perm m1 bt 0 40 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact FT0|exact F1|intros;exact TempOutside]).
  assert (Free1:Forall (fun b=>Mem.range_perm m1 b 0 40 Cur Freeable)
    [bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3;bt]).
  { apply Forall_app with (l1:=[bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3]) (l2:=[bt]);
      split;[exact Free1Root|constructor;[exact FT1|constructor] ]. }
  assert (Free2:Forall (fun b=>Mem.range_perm m2 b 0 40 Cur Freeable)
    [bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3;bt]).
  { rewrite Forall_forall in Free1,Free2Select|-*;intros b Member.
    destruct (in_dec Pos.eq_dec b [ba;bb;bc;by1;by2;by3]) as [Touched|Outside].
    - apply Free2Select;exact Touched.
    - eapply curve_keep_free;[lia|apply Free1;exact Member|exact F2|intros;exact Outside]. }
  assert (I2:fe_at m2 bi 0 (words5 w)) by
    (eapply curve_keep_field_range;[reflexivity|exact I1|exact F2|intros;exact InputSelect]).
  assert (Ge1:le1!_ge=Some (Vptr bp Ptrofs.zero)).
  { unfold le1,swu_selection_temps;rewrite swu_roots_temps_other by discriminate;exact Ge. }
  assert (T1:le1!_t=Some (Vptr bi Ptrofs.zero)).
  { unfold le1,swu_selection_temps;rewrite swu_roots_temps_other by discriminate;exact T. }
  assert (PX:bp<>ba) by (intro Same;apply PointSelect;subst;left;reflexivity).
  assert (PY:bp<>by1) by (intro Same;apply PointSelect;subst;do 3 right;left;reflexivity).
  destruct (eval_ge_set_xy_separate sx sy m2 bp ba by1 PX PY XS YS FP2)
    as (m3 & Construct & XG & YG & Flag & FP3 & Perm3 & F3 & R3).
  assert (I3:fe_at m3 bi 0 (words5 w)) by
    (eapply curve_keep_field_range;[reflexivity|exact I2|exact F3|];
     intros;intro Same;apply PointRoot;subst;left;reflexivity).
  assert (Free3:Forall (fun b=>Mem.range_perm m3 b 0 40 Cur Freeable)
    [bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3;bt]).
  { rewrite Forall_forall in Free2|-*;intros b Member pos Range;
      apply (proj2 (Perm3 b pos Cur Freeable));apply Free2;assumption. }
  pose proof Free3 as All3;rewrite Forall_forall in All3.
  assert (ParitySep:NoDup [bi;bt;bp]).
  { constructor.
    - intros [Same | [Same | Empty] ].
      + apply TempOutside;left;symmetry;exact Same.
      + apply PointOutside;left;symmetry;exact Same.
      + exact Empty.
    - constructor.
      + intros [Same | Empty].
        * apply PointOutside;do 13 right;left;symmetry;exact Same.
        * exact Empty.
      + constructor;[intro Empty;exact Empty|constructor]. }
  pose proof Bounds as AllBounds;rewrite Forall_forall in AllBounds.
  pose proof TightY as AllTight;rewrite Forall_forall in AllTight.
  assert (XSBounds:square_input_bounds sx).
  { unfold sx;apply swu_selected_property.
    - apply AllBounds;left;reflexivity.
    - apply AllBounds;right;left;reflexivity.
    - apply AllBounds;right;right;left;reflexivity. }
  assert (YSTight:mul_small_input_bounds sy).
  { unfold sy;apply swu_selected_property.
    - apply AllTight;left;reflexivity.
    - apply AllTight;right;left;reflexivity.
    - apply AllTight;right;right;left;reflexivity. }
  destruct (exec_swu_words_parity w sy e le1 m3 bi bt bp EG EOdd EMove ET Ge1 T1 ParitySep YSTight I3 YG
    (All3 bi ltac:(left;reflexivity)) (All3 bt ltac:(do 13 right;left;reflexivity)) FP3)
    as (mf & Parity & YF & FIF & FTF & FPF & F4 & R4).
  assert (XFinal:fe_at mf bp 0 (words5 sx)).
  { eapply curve_keep_field_range;[reflexivity|exact XG|exact F4|];intros pos Range.
    split;[intro Same;apply PointRoot;subst;left;reflexivity|].
    split;[intro Same;apply PointOutside;subst;do 13 right;left;reflexivity|right;left;lia]. }
  assert (V3:Mem.valid_block m3 bp) by (eapply Mem.perm_valid_block;apply (FP3 0);lia).
  assert (FlagFinal:Mem.load Mint32 mf bp 80=Some (Vint Int.zero)).
  { rewrite (proj1 F4 Mint32 bp 80 V3);[exact Flag|];intros pos Range;change (80<=pos<84) in Range.
    split;[intro Same;apply PointRoot;subst;left;reflexivity|].
    split;[intro Same;apply PointOutside;subst;do 13 right;left;reflexivity|right;right;lia]. }
  assert (FreeFinal:Forall (fun b=>Mem.range_perm mf b 0 40 Cur Freeable)
    [bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3;bt]).
  { rewrite Forall_forall;intros b Member;destruct (Pos.eq_dec b bi) as [->|NI];[exact FIF|].
    destruct (Pos.eq_dec b bt) as [->|NT];[exact FTF|].
    eapply curve_keep_free;[lia|apply All3;exact Member|exact F4|];intros;split;[exact NI|].
    split;[exact NT|left;intro Same;apply PointOutside;subst;exact Member]. }
  assert (Selected:(rescale_field_output sx,rescale_field_output sy)=swu_selected_candidate t).
  { pose proof (swu_selected_matches_literal t alpha beta (swu_input_first_words w inv)
      (swu_second_words (swu_input_first_words w inv)) (swu_input_third_words w inv)
      (root_chain_candidate (swu_alpha_words w inv)) (root_chain_candidate (swu_beta_words w inv))
      (root_chain_candidate (swu_gamma_words w inv))) as MatchSelect.
    destruct (@literal_swu_candidates Alg.CoreFunSem t) as [a c];cbn zeta in Literal,MatchSelect.
    destruct Literal as (MX1 & MX2 & MX3 & VY1 & VY2 & VY3 & CA & CB & CC).
    exact (MatchSelect MX1 MX2 MX3 VY1 VY2 VY3 CA CB). }
  assert (ReadOnly:readonly_preserved m mf) by
    (eapply preserved_trans;[exact R1|];eapply preserved_trans;[exact R2|];
     eapply preserved_trans;[exact R3|exact R4]).
  exists (swu_words_parity_temps w le1),mf,sx,(swu_words_parity w sy);split.
  - rewrite swu_through_roots_source,swu_select_source,swu_parity_source.
    eapply exec_statement_prefix_then_last;[exact Roots|].
    eapply exec_statement_prefix_then_last;[exact Select|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m3) (le1:=le1);
      [eapply exec_swu_construct_call;eassumption|exact Parity].
  - split;[exact XFinal|];split;[exact YF|];split;[exact FlagFinal|];split;[exact FPF|];
      split;[exact FreeFinal|];split;[exact XSBounds|];split.
    + unfold swu_words_parity;destruct (field_words_odd w).
      * exact (proj2 (negate_sep_numeric sy YSTight)).
      * intros i Index;pose proof (YSTight i Index);destruct (Nat.eqb i 4);lia.
    + split;[unfold swu_words_literal_output;rewrite (swu_words_parity_matches_literal w sx sy YSTight),Selected;reflexivity|];split;
        [eapply swu_startup_preserved;[exact Ready|exact ReadOnly] | ];split;[|exact ReadOnly].
      eapply lframe_trans with (m2:=m1).
      { eapply lframe_implies;[exact F1|];intros b pos Outside Valid;clear -Outside;cbn [In] in *;tauto. }
      eapply lframe_trans with (m2:=m2).
      { eapply lframe_implies;[exact F2|];intros b pos Outside Valid;clear -Outside;cbn [In] in *;tauto. }
      eapply lframe_trans with (m2:=m3).
      { eapply lframe_implies;[exact F3|];intros b pos Outside Valid;intro Same;apply Outside;subst;left;reflexivity. }
      eapply lframe_implies;[exact F4|];intros b pos Outside Valid;repeat split.
      * intro Same;apply Outside;subst;right;left;reflexivity.
      * intro Same;apply Outside;subst;do 14 right;left;reflexivity.
      * left;intro Same;apply Outside;subst;left;reflexivity.
Qed.

(** Preserve the original canonical-reader statement as a specialization. *)
Theorem exec_swu_body t e le m bp bi bw ba bx bj bb bc bA bB bC by1 by2 by3 bt :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  plain_env e -> e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_negc=None ->
  e!_secp256k1_fe_mul_int=None -> e!_secp256k1_fe_negate=None ->
  e!_secp256k1_fe_add_int=None -> e!_secp256k1_fe_inv_var=None ->
  e!_secp256k1_fe_add=None -> e!_d=None -> e!_secp256k1_fe_sqrt_var=None ->
  e!_secp256k1_fe_cmov=None -> e!_secp256k1_ge_set_xy=None -> e!_secp256k1_fe_is_odd=None ->
  e!_wd=Some (bw,curve_fe_type) -> e!_x1=Some (ba,curve_fe_type) ->
  e!_x3d=Some (bx,curve_fe_type) -> e!_jinv=Some (bj,curve_fe_type) ->
  e!_x2=Some (bb,curve_fe_type) -> e!_x3=Some (bc,curve_fe_type) ->
  e!_alphain=Some (bA,curve_fe_type) -> e!_betain=Some (bB,curve_fe_type) ->
  e!_gammain=Some (bC,curve_fe_type) -> e!_y1=Some (by1,curve_fe_type) ->
  e!_y2=Some (by2,curve_fe_type) -> e!_y3=Some (by3,curve_fe_type) -> e!_tmp=Some (bt,curve_fe_type) ->
  le!_t=Some (Vptr bi Ptrofs.zero) -> le!_ge=Some (Vptr bp Ptrofs.zero) ->
  NoDup [bp;bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3;bt] -> swu_startup m ->
  fe_at m bi 0 (words5 (square_reader_rho t)) ->
  Forall (fun b=>Mem.range_perm m b 0 40 Cur Freeable) [bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3;bt] ->
  Mem.range_perm m bp 0 88 Cur Freeable -> exists lef mf x y,
  Clight2.exec_stmt secp_ge e le m (fn_body f_shallue_van_de_woestijne) E0 lef mf Out_normal /\
  fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\
  Mem.load Mint32 mf bp 80=Some (Vint Int.zero) /\ Mem.range_perm mf bp 0 88 Cur Freeable /\
  Forall (fun b=>Mem.range_perm mf b 0 40 Cur Freeable) [bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3;bt] /\
  square_input_bounds x /\ square_input_bounds y /\
  (rescale_field_output x,rescale_field_output y)=@literal_swu Alg.CoreFunSem t /\
  swu_startup mf /\
  lframe (fun b _=>~In b [bp;bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3;bt]) m mf /\ readonly_preserved m mf.
Proof.
  intros Count Plain ES EM EN EC EG EA EI EAdd ED ERoot EMove ESet EOdd EW EX EXD EJ EX2 EX3 EAlpha EBeta EGamma
    EY1 EY2 EY3 ET T Ge Sep Ready Input Free FP.
  destruct (exec_swu_body_words (square_reader_rho t) t e le m bp bi bw ba bx bj bb bc bA bB bC by1 by2 by3 bt
    Count Plain ES EM EN EC EG EA EI EAdd ED ERoot EMove ESet EOdd EW EX EXD EJ EX2 EX3 EAlpha EBeta EGamma
    EY1 EY2 EY3 ET T Ge Sep Ready (root_reader_matches t) Input Free FP)
    as (lef & mf & x & y & Run & X & Y & Flag & FPF & FreeF & BX & BY & Literal & ReadyF & Frame & Readonly).
  rewrite swu_words_literal_output_reader in Literal.
  exists lef,mf,x,y;repeat first [assumption|split].
Qed.
