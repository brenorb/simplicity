(** Original square/two-products/add-one computation of the third SWU
    candidate. The storage theorem executes the unchanged C calls and
    derives their numeric result; no execution or result oracle is used. *)
From Coq Require Import ZArith Znumtheory List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep
  Integers Memory Values Events Maps.
Require Import C.extraMath C.modinv C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_swu_startup C.jet_secp_swu_candidates
  C.jet_secp_swu_initial C.jet_secp_swu_joint_setup C.jet_secp_swu_first_candidate
  C.jet_secp_swu_second_candidate C.jet_secp_swu_constant_product
  C.jet_secp_field_pair_multiply C.jet_secp_field_mul_small C.jet_secp_field_add_int
  C.jet_secp_field_sum_bounds C.jet_secp_square_columns C.jet_secp_square_numeric
  C.jet_secp_square_separate_caller C.jet_secp_multiply_normalize_bridge
  C.jet_secp_multiply_finish_product C.jet_secp_curve_statements C.jet_secp_curve_frame
  C.jet_secp_statement_prefix C.jet_secp_fns C.jet_secp_closed_helpers
  C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma swu_add_int_scaled c w :
  0<=Int.signed c<=8 -> mul_small_input_bounds w ->
  field_scaled_bounds 2 (add_int_words c w).
Proof.
  intros C Bounds i Index;destruct (Nat.eqb i 0) eqn:Zero.
  - apply Nat.eqb_eq in Zero;subst i;unfold field_scaled_bounds.
    rewrite add_int_unsigned_zero by
      (pose proof (Bounds 0%nat ltac:(lia));
       pose proof (Int64.unsigned_range_2 (w 0%nat));cbn [Nat.eqb] in *;
       change Int64.max_unsigned with 18446744073709551615;lia).
    pose proof (Bounds 0%nat ltac:(lia));cbn [Nat.eqb] in *;lia.
  - unfold add_int_words;rewrite Zero;pose proof (Bounds i Index).
    destruct (Nat.eqb i 4);lia.
Qed.

Definition swu_third_square := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
  [curve_local_address _x3;curve_local_address _wd].
Definition swu_third_multiply (inv:bool) :=
  curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
    [curve_local_address _x3;curve_local_address _x3;
     curve_local_address (if inv then _jinv else _wd)].
Definition swu_third_add := curve_call _secp256k1_fe_add_int f_secp256k1_fe_add_int None
  [curve_local_address _x3;Econst_int (Int.repr 1) tint].
Definition swu_third_statements :=
  [swu_third_square;swu_third_multiply false;swu_third_multiply true;swu_third_add].
Definition swu_third_prefix := statement_sequence swu_third_statements Sskip.
Definition swu_after_third_candidate := match swu_after_second_candidate with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ rest)))=>rest | _=>Sskip end.
Lemma swu_third_source : swu_after_second_candidate=
  statement_sequence swu_third_statements swu_after_third_candidate.
Proof. reflexivity. Qed.
Definition swu_third_product w inv :=
  field_pair_product (field_pair_product (square_words w) w) inv.
Definition swu_third_words w inv := add_int_words (Int.repr 1) (swu_third_product w inv).

Lemma exec_swu_third_square_call e le m mf bc bw :
  e!_secp256k1_fe_sqr=None -> e!_x3=Some (bc,curve_fe_type) -> e!_wd=Some (bw,curve_fe_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr bc Ptrofs.zero;Vptr bw Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_third_square E0 le mf Out_normal.
Proof.
  intros Fun C W Call;unfold swu_third_square;eapply exec_curve_call with
    (vargs:=[Vptr bc Ptrofs.zero;Vptr bw Ptrofs.zero]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact C|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact W|reflexivity|constructor].
  - exact Call.
Qed.
Lemma exec_swu_third_multiply_call (inv:bool) e le m mf bc br :
  e!_secp256k1_fe_mul=None -> e!_x3=Some (bc,curve_fe_type) ->
  e!(if inv then _jinv else _wd)=Some (br,curve_fe_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr bc Ptrofs.zero;Vptr bc Ptrofs.zero;Vptr br Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m (swu_third_multiply inv) E0 le mf Out_normal.
Proof.
  intros Fun C R Call;unfold swu_third_multiply;eapply exec_curve_call with
    (vargs:=[Vptr bc Ptrofs.zero;Vptr bc Ptrofs.zero;Vptr br Ptrofs.zero]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact C|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact C|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact R|reflexivity|constructor].
  - exact Call.
Qed.
Lemma exec_swu_third_add_call e le m mf bc :
  e!_secp256k1_fe_add_int=None -> e!_x3=Some (bc,curve_fe_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add_int)
    [Vptr bc Ptrofs.zero;Vint (Int.repr 1)] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_third_add E0 le mf Out_normal.
Proof.
  intros Fun C Call;unfold swu_third_add;eapply exec_curve_call with
    (vargs:=[Vptr bc Ptrofs.zero;Vint (Int.repr 1)]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact C|reflexivity|].
    eapply eval_Econs;[constructor|reflexivity|constructor].
  - exact Call.
Qed.

Theorem exec_swu_third_candidate e le m bc bw bj w inv :
  e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_add_int=None ->
  e!_x3=Some (bc,curve_fe_type) -> e!_wd=Some (bw,curve_fe_type) -> e!_jinv=Some (bj,curve_fe_type) ->
  NoDup [bc;bw;bj] -> swu_startup m -> square_input_bounds w -> square_input_bounds inv ->
  fe_at m bw 0 (words5 w) -> fe_at m bj 0 (words5 inv) ->
  Mem.range_perm m bc 0 40 Cur Freeable -> Mem.range_perm m bw 0 40 Cur Freeable ->
  Mem.range_perm m bj 0 40 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m swu_third_prefix E0 le mf Out_normal /\
  fe_at mf bc 0 (words5 (swu_third_words w inv)) /\
  fe_at mf bw 0 (words5 w) /\ fe_at mf bj 0 (words5 inv) /\
  Mem.range_perm mf bc 0 40 Cur Freeable /\ Mem.range_perm mf bw 0 40 Cur Freeable /\
  Mem.range_perm mf bj 0 40 Cur Freeable /\ field_scaled_bounds 2 (swu_third_words w inv) /\
  square_input_bounds (swu_third_words w inv) /\
  eqm feP (radix_value (swu_third_words w inv))
    (radix_value w*radix_value w*radix_value w*radix_value inv+1) /\
  swu_startup mf /\ lframe (fun b _=>b<>bc /\ b<>bw /\ b<>bj) m mf /\ readonly_preserved m mf.
Proof.
  intros ES EM EA EC EW EJ Sep Ready BW BI W J FC FW FJ.
  assert (Pairs:bc<>bw /\ bc<>bj /\ bw<>bj) by
    (repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
  destruct Pairs as [CW [CJ WJ]].
  destruct (eval_square_separate_from_storage w m bc bw BW FC W FW CW)
    as (m1 & Square & C1 & FC1 & W1 & FW1 & VQ & B1 & F1).
  assert (J1:fe_at m1 bj 0 (words5 inv)) by
    (eapply curve_keep_field_range;[reflexivity|exact J|exact F1|];intros;split;congruence).
  assert (FJ1:Mem.range_perm m1 bj 0 40 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact FJ|exact F1|];intros;split;congruence).
  destruct (eval_field_pair_multiply (square_words w) w m1 bc bw B1 BW CW C1 W1 FC1 FW1)
    as (m2 & Mul1 & C2 & W2 & FC2 & FW2 & V1 & B2 & T2 & F2).
  assert (J2:fe_at m2 bj 0 (words5 inv)) by
    (eapply curve_keep_field_range;[reflexivity|exact J1|exact F2|];intros;split;congruence).
  assert (FJ2:Mem.range_perm m2 bj 0 40 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact FJ1|exact F2|];intros;split;congruence).
  destruct (eval_field_pair_multiply (field_pair_product (square_words w) w) inv m2 bc bj
    B2 BI CJ C2 J2 FC2 FJ2)
    as (m3 & Mul2 & C3 & J3 & FC3 & FJ3 & V2 & B3 & T3 & F3).
  assert (W3:fe_at m3 bw 0 (words5 w)) by
    (eapply curve_keep_field_range;[reflexivity|exact W2|exact F3|];intros;split;congruence).
  assert (FW3:Mem.range_perm m3 bw 0 40 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact FW2|exact F3|];intros;split;congruence).
  assert (Tight:mul_small_input_bounds (swu_third_product w inv)) by
    (unfold swu_third_product;intros i Index;exact (proj2 (T3 i Index))).
  destruct (eval_field_add_int_small (Int.repr 1) (swu_third_product w inv) m3 bc
    ltac:(change (0<=1<=8);lia) Tight C3 FC3)
    as (mf & Add & CF & FCF & AddValue & OutBounds & F4).
  assert (WF:fe_at mf bw 0 (words5 w)) by
    (eapply curve_keep_field_range;[reflexivity|exact W3|exact F4|];intros;congruence).
  assert (JF:fe_at mf bj 0 (words5 inv)) by
    (eapply curve_keep_field_range;[reflexivity|exact J3|exact F4|];intros;congruence).
  assert (FWF:Mem.range_perm mf bw 0 40 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact FW3|exact F4|];intros;congruence).
  assert (FJF:Mem.range_perm mf bj 0 40 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact FJ3|exact F4|];intros;congruence).
  assert (RQ:readonly_preserved m m1) by
    (eapply secp_closed_function_preserved;[exact swu_square_closed|reflexivity|exact Square]).
  assert (R1:readonly_preserved m1 m2) by
    (eapply secp_closed_function_preserved;[exact swu_product_closed|reflexivity|exact Mul1]).
  assert (R2:readonly_preserved m2 m3) by
    (eapply secp_closed_function_preserved;[exact swu_product_closed|reflexivity|exact Mul2]).
  assert (RA:readonly_preserved m3 mf) by
    (eapply (secp_closed_function_preserved f_secp256k1_fe_add_int);[reflexivity|reflexivity|exact Add]).
  assert (ReadOnly:readonly_preserved m mf) by
    (eapply preserved_trans;[exact RQ|];eapply preserved_trans;[exact R1|];
     eapply preserved_trans;[exact R2|exact RA]).
  assert (ReadyF:swu_startup mf) by (eapply swu_startup_preserved;eassumption).
  assert (Scaled:field_scaled_bounds 2 (swu_third_words w inv)) by
    (apply swu_add_int_scaled;[change (0<=1<=8);lia|exact Tight]).
  rewrite field_prime_matches_normalizer in VQ,V1,V2.
  assert (Value:eqm feP (radix_value (swu_third_words w inv))
    (radix_value w*radix_value w*radix_value w*radix_value inv+1)).
  { unfold swu_third_words;rewrite AddValue;change (Int.signed (Int.repr 1)) with 1.
    apply Zplus_eqm;[|reflexivity];eapply eqm_trans;[exact V2|].
    apply Zmult_eqm;[|reflexivity];eapply eqm_trans;[exact V1|].
    apply Zmult_eqm;[exact VQ|reflexivity]. }
  exists mf;split.
  - unfold swu_third_prefix,swu_third_statements;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m1);
      [eapply exec_swu_third_square_call;eassumption|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m2);
      [eapply (exec_swu_third_multiply_call false);eassumption|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m3);
      [eapply (exec_swu_third_multiply_call true);eassumption|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mf);
      [eapply exec_swu_third_add_call;eassumption|apply exec_Sskip].
  - split;[exact CF|];split;[exact WF|];split;[exact JF|];split;[exact FCF|];split;[exact FWF|];
      split;[exact FJF|];split;[exact Scaled|];split;[exact OutBounds|];split;[exact Value|];
      split;[exact ReadyF|];split.
    + eapply lframe_trans with (m2:=m1).
      * eapply lframe_implies;[exact F1|];intros b pos [NC [NW NJ]] Valid;split;assumption.
      * eapply lframe_trans with (m2:=m2).
        { eapply lframe_implies;[exact F2|];intros b pos [NC [NW NJ]] Valid;split;assumption. }
        eapply lframe_trans with (m2:=m3).
        { eapply lframe_implies;[exact F3|];intros b pos [NC [NW NJ]] Valid;split;assumption. }
        eapply lframe_implies;[exact F4|];intros b pos [NC Rest] Valid;exact NC.
    + exact ReadOnly.
Qed.

Lemma swu_setup_wd_square w : square_input_bounds w ->
  square_input_bounds (swu_setup_wd (square_words w)) /\
  eqm feP (radix_value (swu_setup_wd (square_words w))) (radix_value w*radix_value w+8).
Proof.
  intro Bounds.
  assert (Tight:mul_small_input_bounds (square_words w)) by
    (intros i Index;exact (proj2 (square_output_bounds w Bounds i Index))).
  split.
  - apply add_int_bounds;[change (0<=8<=8);lia|exact Tight].
  - unfold swu_setup_wd;rewrite add_int_radix.
    + change (Int.signed (Int.repr 8)) with 8;apply Zplus_eqm;[|reflexivity].
      pose proof (square_output_numeric w Bounds) as Square;
        rewrite field_prime_matches_normalizer in Square;exact Square.
    + pose proof (Tight 0%nat ltac:(lia));
      pose proof (Int64.unsigned_range_2 (square_words w 0%nat));cbn [Nat.eqb] in *;
        change (Int.signed (Int.repr 8)) with 8;
        change Int64.max_unsigned with 18446744073709551615;lia.
Qed.
Lemma swu_third_spec_match t wd inv value :
  eqm feP (radix_value wd) (t*t+8) -> radix_value inv=swu_joint_inverse t ->
  eqm feP value (radix_value wd*radix_value wd*radix_value wd*radix_value inv+1) ->
  eqm feP value (swu_c_candidate3 t).
Proof.
  intros W I V;eapply eqm_trans;[exact V|];rewrite I;unfold swu_c_candidate3.
  replace (1+(t*t+8)^3*swu_joint_inverse t) with
    ((t*t+8)*(t*t+8)*(t*t+8)*swu_joint_inverse t+1) by ring.
  apply Zplus_eqm;[|reflexivity];apply Zmult_eqm;[|reflexivity].
  apply Zmult_eqm;[apply Zmult_eqm;exact W|exact W].
Qed.

Definition swu_input_third_words w inv := swu_third_words (swu_setup_wd (square_words w)) inv.
Definition swu_through_third_statements := swu_through_second_statements++swu_third_statements.
Definition swu_through_third := statement_sequence swu_through_third_statements Sskip.
Lemma swu_through_third_source : fn_body f_shallue_van_de_woestijne=
  statement_sequence swu_through_third_statements swu_after_third_candidate.
Proof. reflexivity. Qed.

Theorem exec_swu_through_third e le m bt bw ba bx bj bb bc w :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  plain_env e -> e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_negc=None ->
  e!_secp256k1_fe_mul_int=None -> e!_secp256k1_fe_negate=None ->
  e!_secp256k1_fe_add_int=None -> e!_secp256k1_fe_inv_var=None ->
  e!_secp256k1_fe_add=None -> e!_d=None ->
  e!_wd=Some (bw,curve_fe_type) -> e!_x1=Some (ba,curve_fe_type) ->
  e!_x3d=Some (bx,curve_fe_type) -> e!_jinv=Some (bj,curve_fe_type) ->
  e!_x2=Some (bb,curve_fe_type) -> e!_x3=Some (bc,curve_fe_type) ->
  le!_t=Some (Vptr bt Ptrofs.zero) -> NoDup [bt;bw;ba;bx;bj;bb;bc] ->
  swu_startup m -> square_input_bounds w -> fe_at m bt 0 (words5 w) ->
  Forall (fun b=>Mem.range_perm m b 0 40 Cur Freeable) [bt;bw;ba;bx;bj;bb;bc] -> exists inv mf,
  Clight2.exec_stmt secp_ge e le m swu_through_third E0 le mf Out_normal /\
  fe_at mf bt 0 (words5 w) /\ fe_at mf bw 0 (words5 (swu_setup_wd (square_words w))) /\
  fe_at mf ba 0 (words5 (swu_input_first_words w inv)) /\
  fe_at mf bx 0 (words5 (swu_setup_x3d (square_words w))) /\ fe_at mf bj 0 (words5 inv) /\
  fe_at mf bb 0 (words5 (swu_second_words (swu_input_first_words w inv))) /\
  fe_at mf bc 0 (words5 (swu_input_third_words w inv)) /\
  Forall (fun b=>Mem.range_perm mf b 0 40 Cur Freeable) [bt;bw;ba;bx;bj;bb;bc] /\
  square_input_bounds inv /\ field_scaled_bounds 2 (swu_input_first_words w inv) /\
  square_input_bounds (swu_input_first_words w inv) /\
  square_input_bounds (swu_second_words (swu_input_first_words w inv)) /\
  field_scaled_bounds 2 (swu_input_third_words w inv) /\
  square_input_bounds (swu_input_third_words w inv) /\
  eqm feP (radix_value (swu_input_first_words w inv)) (swu_c_candidate1 (radix_value w)) /\
  eqm feP (radix_value (swu_second_words (swu_input_first_words w inv))) (swu_c_candidate2 (radix_value w)) /\
  eqm feP (radix_value (swu_input_third_words w inv)) (swu_c_candidate3 (radix_value w)) /\
  radix_value inv=swu_joint_inverse (radix_value w) /\ swu_startup mf /\
  lframe (fun b _=>~In b [bt;bw;ba;bx;bj;bb;bc]) m mf /\ readonly_preserved m mf.
Proof.
  intros Count Plain ES EM EN EC EG EA EI EAdd ED EW EX EXD EJ EX2 EX3 T Sep Ready Bounds Input Free.
  assert (SepS:NoDup [bt;bw;ba;bx;bj;bb]) by
    (repeat rewrite NoDup_cons_iff in Sep;repeat rewrite NoDup_cons_iff;
     cbn [In] in *;intuition (try constructor;congruence)).
  assert (FreeS0:Forall (fun b=>Mem.range_perm m b 0 40 Cur Freeable) [bt;bw;ba;bx;bj;bb]).
  { rewrite Forall_forall in *;intros b Member;apply Free;cbn [In] in *;tauto. }
  destruct (exec_swu_through_second e le m bt bw ba bx bj bb w Count Plain ES EM EN EC EG EA EI
    EAdd ED EW EX EXD EJ EX2 T SepS Ready Bounds Input FreeS0)
    as (inv & ms & Start & TS & WS & AS & XS & JS & BS & FreeS & JBounds & AScaled & ABounds &
      BBounds & FirstSpec & SecondSpec & JNumeric & ReadyS & FS & RS).
  assert (NotBC:~In bc [bt;bw;ba;bx;bj;bb]) by
    (repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence).
  assert (FC:Mem.range_perm m bc 0 40 Cur Freeable).
  { rewrite Forall_forall in Free;apply Free;cbn;tauto. }
  assert (FCS:Mem.range_perm ms bc 0 40 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact FC|exact FS|];intros;exact NotBC).
  assert (SepC:NoDup [bc;bw;bj]) by
    (repeat rewrite NoDup_cons_iff in Sep;repeat rewrite NoDup_cons_iff;
     cbn [In] in *;intuition (try constructor;congruence)).
  pose proof FreeS as AllFree;rewrite Forall_forall in AllFree.
  assert (FWS:Mem.range_perm ms bw 0 40 Cur Freeable) by (apply AllFree;cbn;tauto).
  assert (FJS:Mem.range_perm ms bj 0 40 Cur Freeable) by (apply AllFree;cbn;tauto).
  destruct (swu_setup_wd_square w Bounds) as [WBounds WNumeric].
  destruct (exec_swu_third_candidate e le ms bc bw bj (swu_setup_wd (square_words w)) inv
    ES EM EA EX3 EW EJ SepC ReadyS WBounds JBounds WS JS FCS FWS FJS)
    as (mf & Third & CF & WF & JF & FCF & FWF & FJF & CScaled & CBounds & Value3 & ReadyF & FThird & RThird).
  assert (Safe:forall b,In b [bt;ba;bx;bb] -> b<>bc /\ b<>bw /\ b<>bj).
  { intros b Member;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence. }
  assert (Keep:forall b rho,In b [bt;ba;bx;bb] ->
    fe_at ms b 0 (words5 rho) -> fe_at mf b 0 (words5 rho)).
  { intros b rho Member Field;eapply curve_keep_field_range.
    - reflexivity.
    - exact Field.
    - exact FThird.
    - intros;apply Safe;exact Member. }
  assert (KeepFree:forall b,In b [bt;ba;bx;bb] -> Mem.range_perm mf b 0 40 Cur Freeable).
  { intros b Member;eapply curve_keep_free;[lia| |exact FThird|].
    - apply AllFree;cbn [In] in *;tauto.
    - intros;apply Safe;exact Member. }
  assert (TF:fe_at mf bt 0 (words5 w)) by (eapply Keep;[cbn;tauto|exact TS]).
  assert (AF:fe_at mf ba 0 (words5 (swu_input_first_words w inv))) by
    (eapply Keep;[cbn;tauto|exact AS]).
  assert (XF:fe_at mf bx 0 (words5 (swu_setup_x3d (square_words w)))) by
    (eapply Keep;[cbn;tauto|exact XS]).
  assert (BF:fe_at mf bb 0 (words5 (swu_second_words (swu_input_first_words w inv)))) by
    (eapply Keep;[cbn;tauto|exact BS]).
  assert (FreeFinal:Forall (fun b=>Mem.range_perm mf b 0 40 Cur Freeable) [bt;bw;ba;bx;bj;bb;bc]).
  { repeat constructor;first [exact FWF|exact FJF|exact FCF|apply KeepFree;cbn;tauto]. }
  assert (Spec3:eqm feP (radix_value (swu_input_third_words w inv))
    (swu_c_candidate3 (radix_value w))) by
    (eapply swu_third_spec_match;[exact WNumeric|exact JNumeric|exact Value3]).
  exists inv,mf;split.
  - unfold swu_through_third,swu_through_third_statements.
    change (Clight2.exec_stmt secp_ge e le m
      (statement_sequence swu_through_second_statements swu_third_prefix) E0 le mf Out_normal).
    eapply exec_statement_prefix_then_last;[exact Start|exact Third].
  - split;[exact TF|];split;[exact WF|];split;[exact AF|];split;[exact XF|];split;[exact JF|];
      split;[exact BF|];split;[exact CF|];split;[exact FreeFinal|];split;[exact JBounds|];
      split;[exact AScaled|];split;[exact ABounds|];split;[exact BBounds|];split;[exact CScaled|];
      split;[exact CBounds|];split;[exact FirstSpec|];split;[exact SecondSpec|];split;[exact Spec3|];
      split;[exact JNumeric|];split;[exact ReadyF|];split.
    + eapply lframe_trans with (m2:=ms).
      * eapply lframe_implies;[exact FS|];intros b pos NotIn Valid;cbn [In] in *;tauto.
      * eapply lframe_implies;[exact FThird|];intros b pos NotIn Valid;
          repeat split;intro Same;apply NotIn;subst;cbn;tauto.
    + eapply preserved_trans;[exact RS|exact RThird].
Qed.
