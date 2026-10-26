(** The original seven-iteration odd-multiple-table loop. The recurrence
    records exact machine limbs; relating it to scalarTable5 is a separate
    obligation, not an assumed execution or a replacement specification. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_odd_table_iteration C.jet_secp_mixed_body_loose C.jet_secp_mixed_body_ratio_slice
 C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge C.jet_secp_curve_frame
 C.jet_secp_field_read_preservation C.jet_secp_slice_permissions
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge mixed_mode_body_x_words mixed_mode_body_y_words mixed_mode_body_z_words
 mixed_mode_body_flag mixed_mode_slice_ratio_words.

Record odd_table_state := {
 odd_table_xs:nat->nat->int64; odd_table_ys:nat->nat->int64; odd_table_ratios:nat->nat->int64;
 odd_table_x:nat->int64; odd_table_y:nat->int64; odd_table_z:nat->int64; odd_table_flag:int
}.
Definition odd_table_replace (xs:nat->nat->int64) j w k := if Nat.eq_dec k j then w else xs k.
Definition odd_table_next s u v j :=
 let x:=mixed_mode_body_x_words true (odd_table_flag s) (odd_table_x s) (odd_table_y s) (odd_table_z s) u v in
 let y:=mixed_mode_body_y_words true (odd_table_flag s) (odd_table_x s) (odd_table_y s) (odd_table_z s) u v in
 let z:=mixed_mode_body_z_words true (odd_table_flag s) (odd_table_x s) (odd_table_y s) (odd_table_z s) u v in
 let ratio:=mixed_mode_slice_ratio_words true (odd_table_flag s) (odd_table_x s) (odd_table_y s) (odd_table_z s) u v in
 {|odd_table_xs:=odd_table_replace (odd_table_xs s) j x;
   odd_table_ys:=odd_table_replace (odd_table_ys s) j y;
   odd_table_ratios:=odd_table_replace (odd_table_ratios s) j ratio;
   odd_table_x:=x;odd_table_y:=y;odd_table_z:=z;
   odd_table_flag:=mixed_mode_body_flag true (odd_table_flag s) (odd_table_x s) (odd_table_y s) (odd_table_z s) u v|}.
Fixpoint odd_table_walk n j s u v := match n with
 | O=>s | S k=>odd_table_walk k (S j) (odd_table_next s u v j) u v end.
Definition odd_table_prefix m br bz n s := forall j,(j<n)%nat ->
 fe_at m br (88*Z.of_nat j) (words5 (odd_table_xs s j)) /\
 fe_at m br (88*Z.of_nat j+40) (words5 (odd_table_ys s j)) /\
 Mem.load Mint32 m br (88*Z.of_nat j+80)=Some (Vint Int.zero) /\
 fe_at m bz (40*Z.of_nat j) (words5 (odd_table_ratios s j)).
Definition odd_table_prefix_bounds n s := forall j,(j<n)%nat ->
 square_input_bounds (odd_table_xs s j) /\ square_input_bounds (odd_table_ys s j) /\
 square_input_bounds (odd_table_ratios s j).
Definition odd_table_accumulator m ba s :=
 fe_at m ba 0 (words5 (odd_table_x s)) /\ fe_at m ba 40 (words5 (odd_table_y s)) /\
 fe_at m ba 80 (words5 (odd_table_z s)) /\ Mem.load Mint32 m ba 120=Some (Vint (odd_table_flag s)).
Definition odd_table_accumulator_bounds s :=
 square_input_bounds (odd_table_x s) /\ square_input_bounds (odd_table_y s) /\ square_input_bounds (odd_table_z s).
Definition odd_table_loop_frame (br ba bg bz:block) (b:block) (_:Z) :=
 b<>br /\ b<>ba /\ b<>bg /\ b<>bz.
Definition odd_table_loop_guard := Ebinop Olt (Etempvar _i tint) (Etempvar _n tint) tint.

Lemma odd_table_loop_source : odd_table_loop=
 Sloop (Ssequence (Sifthenelse odd_table_loop_guard Sskip Sbreak) odd_table_loop_body) odd_table_increment.
Proof. reflexivity. Qed.
Lemma eval_odd_table_loop_guard e le m i : 0<=i<=8 ->
 le!_i=Some (Vint (Int.repr i)) -> le!_n=Some (Vint (Int.repr 8)) ->
 eval_expr secp_ge e le m odd_table_loop_guard (Vint (if Z.ltb i 8 then Int.one else Int.zero)).
Proof.
 intros Index I N;unfold odd_table_loop_guard;eapply eval_Ebinop;
  [apply eval_Etempvar;exact I|apply eval_Etempvar;exact N|].
 change (Some (Val.of_bool (Int.lt (Int.repr i) (Int.repr 8)))=
  Some (Vint (if Z.ltb i 8 then Int.one else Int.zero))).
 unfold Int.lt;rewrite !Int.signed_repr by
  (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
 destruct (Coqlib.zlt i 8),(Z.ltb_spec i 8);first [reflexivity|lia].
Qed.
Lemma exec_odd_table_loop_done e le m :
 le!_i=Some (Vint (Int.repr 8)) -> le!_n=Some (Vint (Int.repr 8)) ->
 Clight2.exec_stmt secp_ge e le m odd_table_loop E0 le m Out_normal.
Proof.
 intros I N;rewrite odd_table_loop_source;eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
 eapply exec_Sseq_2;[|discriminate].
 eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
 apply (eval_odd_table_loop_guard e le m 8);[lia|exact I|exact N].
Qed.
Lemma exec_odd_table_loop_join e le m i le1 m1 lef mf : 1<=i<8 ->
 le!_i=Some (Vint (Int.repr i)) -> le!_n=Some (Vint (Int.repr 8)) ->
 Clight2.exec_stmt secp_ge e le m odd_table_iteration E0 le1 m1 Out_normal ->
 Clight2.exec_stmt secp_ge e le1 m1 odd_table_loop E0 lef mf Out_normal ->
 Clight2.exec_stmt secp_ge e le m odd_table_loop E0 lef mf Out_normal.
Proof.
 intros Index I N Iteration Rest;unfold odd_table_iteration in Iteration.
 inversion Iteration;subst;[|contradiction].
 match goal with H:?t1 ** ?t2=E0 |- _ => destruct (Eapp_E0_inv t1 t2 H) as [-> ->] end.
 rewrite odd_table_loop_source in Rest|-*.
 eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0) (out1:=Out_normal).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m).
   + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|constructor].
     pose proof (eval_odd_table_loop_guard e le m i ltac:(lia) I N) as Guard.
     destruct (Z.ltb_spec i 8);[exact Guard|lia].
   + eassumption.
 - constructor.
 - eassumption.
 - exact Rest.
Qed.

Lemma odd_table_prefix_next m mf br ba bg bz n s u v : (n<8)%nat ->
 br<>ba -> br<>bg -> br<>bz -> bz<>ba -> bz<>bg ->
 odd_table_prefix m br bz n s -> Mem.range_perm m br 0 704 Cur Freeable ->
 fe_at mf br (88*Z.of_nat n) (words5 (odd_table_x (odd_table_next s u v n))) ->
 fe_at mf br (88*Z.of_nat n+40) (words5 (odd_table_y (odd_table_next s u v n))) ->
 Mem.load Mint32 mf br (88*Z.of_nat n+80)=Some (Vint Int.zero) ->
 fe_at mf bz (40*Z.of_nat n) (words5 (odd_table_ratios (odd_table_next s u v n) n)) ->
 lframe (odd_table_iteration_frame br ba bg bz (Z.of_nat n)) m mf ->
 odd_table_prefix mf br bz (S n) (odd_table_next s u v n).
Proof.
 intros Bound RA RG RZ ZA ZG Prefix FreeR X Y Flag Ratio Frame j Index.
 unfold odd_table_next;cbn [odd_table_xs odd_table_ys odd_table_ratios];unfold odd_table_replace.
 destruct (Nat.eq_dec j n) as [->|Different].
 - split;[exact X|];split;[exact Y|];split;[exact Flag|].
   cbn [odd_table_next odd_table_ratios] in Ratio;unfold odd_table_replace in Ratio;
    destruct (Nat.eq_dec n n);[exact Ratio|contradiction].
 - assert (Earlier:(j<n)%nat) by lia;destruct (Prefix j Earlier) as (XJ & YJ & FlagJ & RJ).
   assert (TableOutside:forall pos,88*Z.of_nat j<=pos<88*Z.of_nat j+84 ->
     odd_table_iteration_frame br ba bg bz (Z.of_nat n) br pos).
   { intros pos Range;unfold odd_table_iteration_frame;split;[exact RA|];split;[exact RG|];split;
      [right;left;lia|left;exact RZ]. }
   split.
   + eapply curve_keep_field_range;[reflexivity|exact XJ|exact Frame|];intros pos Range;apply TableOutside;lia.
   + split.
     * eapply curve_keep_field_range;[reflexivity|exact YJ|exact Frame|];intros pos Range;apply TableOutside;lia.
     * split.
       -- rewrite (proj1 Frame Mint32 br (88*Z.of_nat j+80));[exact FlagJ| |].
          ++ eapply Mem.perm_valid_block;apply (FreeR 0);lia.
          ++ intros pos Range;change (88*Z.of_nat j+80<=pos<88*Z.of_nat j+80+4) in Range;
               apply TableOutside;lia.
       -- eapply curve_keep_field_range;[reflexivity|exact RJ|exact Frame|].
          intros pos Range;unfold odd_table_iteration_frame;split;[exact ZA|];split;[exact ZG|];split;
           [left;congruence|right;left;lia].
Qed.

Theorem exec_odd_table_loop n : forall j, (1<=j)%nat -> (j+n=8)%nat ->
 forall e le m br ba bg bz s u v,
 NoDup [br;ba;bg;bz] ->
 e!_ai=Some (ba,Tstruct __6123 noattr) -> e!_d_ge=Some (bg,C.jet_secp_curve_statements.curve_ge_type) ->
 e!_secp256k1_gej_add_ge_var=None -> e!_secp256k1_ge_set_xy=None ->
 le!_pre_a=Some (Vptr br Ptrofs.zero) -> le!_zr=Some (Vptr bz Ptrofs.zero) ->
 le!_i=Some (Vint (Int.repr (Z.of_nat j))) -> le!_n=Some (Vint (Int.repr 8)) ->
 odd_table_prefix m br bz j s -> odd_table_prefix_bounds j s ->
 odd_table_accumulator m ba s -> odd_table_accumulator_bounds s ->
 square_input_bounds u -> square_input_bounds v ->
 fe_at m bg 0 (words5 u) -> fe_at m bg 40 (words5 v) -> Mem.load Mint32 m bg 80=Some (Vint Int.zero) ->
 Mem.range_perm m br 0 704 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable ->
 Mem.range_perm m bg 0 88 Cur Freeable -> Mem.range_perm m bz 0 320 Cur Freeable ->
 let sf:=odd_table_walk n j s u v in exists lef mf,
 Clight2.exec_stmt secp_ge e le m odd_table_loop E0 lef mf Out_normal /\
 lef!_i=Some (Vint (Int.repr 8)) /\ (forall id,id<>_i -> lef!id=le!id) /\
 odd_table_prefix mf br bz 8 sf /\ odd_table_prefix_bounds 8 sf /\
 odd_table_accumulator mf ba sf /\ odd_table_accumulator_bounds sf /\
 fe_at mf bg 0 (words5 u) /\ fe_at mf bg 40 (words5 v) /\ Mem.load Mint32 mf bg 80=Some (Vint Int.zero) /\
 Mem.range_perm mf br 0 704 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 Mem.range_perm mf bg 0 88 Cur Freeable /\ Mem.range_perm mf bz 0 320 Cur Freeable /\
 keeps_permissions m mf /\ lframe (odd_table_loop_frame br ba bg bz) m mf /\ readonly_preserved m mf.
Proof.
 induction n as [|n IH];intros j Start Length e le m br ba bg bz s u v Distinct AI DG AddGlobal WriteGlobal
  Table Ratios I N Prefix PrefixBounds Acc AccBounds BU BV U V Flag FreeR FreeA FreeG FreeZ;cbn [odd_table_walk].
 - assert (J:j=8%nat) by lia;subst j.
   exists le,m;split;[apply exec_odd_table_loop_done;assumption|];split;[exact I|];split;[intros;reflexivity|].
   repeat (first [assumption|apply keeps_permissions_refl|apply lframe_refl|apply preserved_refl|split]).
 - assert (Index:1<=Z.of_nat j<8) by lia.
   destruct Acc as (X & Y & Z & FlagA);destruct AccBounds as (BX & BY & BZ).
   destruct (exec_odd_table_iteration e le (odd_table_x s) (odd_table_y s) (odd_table_z s) u v (odd_table_flag s)
     m br ba bg bz (Z.of_nat j) Index Distinct AI DG AddGlobal WriteGlobal Table Ratios I
     BX BY BZ BU BV X Y Z FlagA U V Flag FreeR FreeA FreeG FreeZ)
    as (m1 & Iteration & X1 & Y1 & Z1 & FlagA1 & U1 & V1 & Flag1 & TX & TY & TFlag & Ratio1 &
      BX1 & BY1 & BZ1 & RatioBound & FreeR1 & FreeA1 & FreeG1 & FreeZ1 & Keep1 & Frame1 & Readonly1).
   set (s1:=odd_table_next s u v j).
   assert (Separate:br<>ba /\ br<>bg /\ br<>bz /\ bz<>ba /\ bz<>bg).
   { clear -Distinct;repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct;intuition congruence. }
   destruct Separate as (RA & RG & RZ & ZA & ZG).
   assert (Prefix1:odd_table_prefix m1 br bz (S j) s1).
   { eapply (odd_table_prefix_next m m1 br ba bg bz j s u v);try eassumption;[lia|].
     unfold odd_table_next;cbn [odd_table_ratios];unfold odd_table_replace;
       destruct (Nat.eq_dec j j);[exact Ratio1|contradiction]. }
   assert (PrefixBounds1:odd_table_prefix_bounds (S j) s1).
   { intros k Bound;unfold s1,odd_table_next;cbn [odd_table_xs odd_table_ys odd_table_ratios];
      unfold odd_table_replace;destruct (Nat.eq_dec k j) as [->|Different].
     - split;[exact BX1|];split;assumption.
     - apply PrefixBounds;lia. }
   assert (Acc1:odd_table_accumulator m1 ba s1) by
    (split;[exact X1|];split;[exact Y1|];split;[exact Z1|exact FlagA1]).
   assert (AccBounds1:odd_table_accumulator_bounds s1) by (split;[exact BX1|];split;assumption).
   set (le1:=odd_table_iteration_temps le (Z.of_nat j)).
   assert (Other:forall id,id<>_i -> le1!id=le!id) by
    (intros id Different;unfold le1,odd_table_iteration_temps;apply PTree.gso;exact Different).
   destruct (IH (S j) ltac:(lia) ltac:(lia) e le1 m1 br ba bg bz s1 u v Distinct AI DG AddGlobal WriteGlobal
     ltac:(rewrite Other by discriminate;exact Table) ltac:(rewrite Other by discriminate;exact Ratios)
     ltac:(unfold le1,odd_table_iteration_temps;rewrite PTree.gss,Nat2Z.inj_succ;f_equal;f_equal;lia)
     ltac:(rewrite Other by discriminate;exact N) Prefix1 PrefixBounds1 Acc1 AccBounds1 BU BV U1 V1 Flag1
     FreeR1 FreeA1 FreeG1 FreeZ1)
    as (lef & mf & Rest & IF & Others & PrefixF & PrefixBoundsF & AccF & AccBoundsF & UF & VF & FlagF &
      FreeRF & FreeAF & FreeGF & FreeZF & Keep2 & Frame2 & Readonly2).
   exists lef,mf;split.
   + eapply exec_odd_table_loop_join;[exact Index|exact I|exact N|exact Iteration|exact Rest].
   + split;[exact IF|];split;[intros id Different;rewrite Others by exact Different;apply Other;exact Different|].
     split;[exact PrefixF|];split;[exact PrefixBoundsF|];split;[exact AccF|];split;[exact AccBoundsF|];
      split;[exact UF|];split;[exact VF|];split;[exact FlagF|];split;[exact FreeRF|];split;[exact FreeAF|];
      split;[exact FreeGF|];split;[exact FreeZF|];split.
     * eapply keeps_permissions_trans;[exact Keep1|exact Keep2].
     * split.
       -- eapply lframe_trans;[|exact Frame2];eapply lframe_implies;[exact Frame1|].
          intros b pos (NR & NA & NG & NZ) Valid;split;[exact NA|];split;[exact NG|];split;left;assumption.
       -- eapply preserved_trans;[exact Readonly1|exact Readonly2].
Qed.
