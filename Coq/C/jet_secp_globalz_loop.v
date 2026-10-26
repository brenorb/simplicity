(** The complete original descending global-Z loop. Its exact limb result is
    a recursive composition of the already checked factor/scaling calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_globalz_iteration C.jet_secp_globalz_factor_call C.jet_secp_globalz_indexed_call
 C.jet_secp_generator_globalz_empty C.jet_secp_statement_prefix C.jet_secp_curve_statements
 C.jet_secp_ge_zinv_arithmetic C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_slice_permissions
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge globalz_factor_words ge_zinv_x_words ge_zinv_y_words.

Definition globalz_replace (xs:nat->nat->int64) j w k :=
 if Nat.eq_dec k j then w else xs k.
Fixpoint globalz_walk n xs ys ratios zs := match n with
 | O=>((xs,ys),zs)
 | S j=>let factor:=globalz_factor_words (Z.of_nat (S j)) zs (ratios (S j)) in
   globalz_walk j (globalz_replace xs j (ge_zinv_x_words (xs j) factor))
    (globalz_replace ys j (ge_zinv_y_words (ys j) factor)) ratios factor
 end.
Definition globalz_table_rep m br xs ys := forall j,(j<8)%nat ->
 fe_at m br (88*Z.of_nat j+0) (words5 (xs j)) /\
 fe_at m br (88*Z.of_nat j+40) (words5 (ys j)) /\
 Mem.load Mint32 m br (88*Z.of_nat j+80)=Some (Vint Int.zero).
Definition globalz_table_bounds xs ys := forall j,(j<8)%nat ->
 square_input_bounds (xs j) /\ square_input_bounds (ys j).
Definition globalz_ratios_rep m bz ratios := forall j,(j<8)%nat ->
 fe_at m bz (40*Z.of_nat j) (words5 (ratios j)).
Definition globalz_ratios_bounds ratios := forall j,(j<8)%nat -> square_input_bounds (ratios j).
Definition globalz_loop_guard := Ebinop Ogt (Etempvar _i tulong) (Econst_int Int.zero tint) tint.
Definition globalz_loop := snd (split_statement_last globalz_nonempty_branch).
Definition globalz_loop_frame (br bt bf bz:block) (bx:block) (_:Z) :=
 bx<>br /\ bx<>bt /\ bx<>bf /\ bx<>bz.

Lemma globalz_loop_source : globalz_loop=
 Sloop (Ssequence (Sifthenelse globalz_loop_guard Sskip Sbreak) globalz_indexed_loop_body) Sskip.
Proof. reflexivity. Qed.

Lemma eval_globalz_loop_guard e le m i : 0<=i<8 -> le!_i=Some (Vlong (Int64.repr i)) ->
 eval_expr secp_ge e le m globalz_loop_guard (Vint (if Z.eqb i 0 then Int.zero else Int.one)).
Proof.
 intros Index IndexTemp;unfold globalz_loop_guard.
 eapply eval_Ebinop;[apply eval_Etempvar;exact IndexTemp|constructor|].
 change (Some (Val.of_bool (Int64.ltu Int64.zero (Int64.repr i)))=
  Some (Vint (if Z.eqb i 0 then Int.zero else Int.one))).
 unfold Int64.ltu;rewrite Int64.unsigned_repr by
  (change Int64.max_unsigned with 18446744073709551615;lia).
 change (Int64.unsigned Int64.zero) with 0.
 destruct (Coqlib.zlt 0 i), (Z.eqb_spec i 0);first [reflexivity|lia].
Qed.

Lemma exec_globalz_loop_done e le m : le!_i=Some (Vlong Int64.zero) ->
 Clight2.exec_stmt secp_ge e le m globalz_loop E0 le m Out_normal.
Proof.
 intro IndexTemp;rewrite globalz_loop_source.
 eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
 eapply exec_Sseq_2;[|discriminate].
 eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
 apply (eval_globalz_loop_guard e le m 0);[lia|exact IndexTemp].
Qed.

Lemma exec_globalz_loop_join e le m i le1 m1 lef mf : 1<=i<8 ->
 le!_i=Some (Vlong (Int64.repr i)) ->
 Clight2.exec_stmt secp_ge e le m globalz_indexed_loop_body E0 le1 m1 Out_normal ->
 Clight2.exec_stmt secp_ge e le1 m1 globalz_loop E0 lef mf Out_normal ->
 Clight2.exec_stmt secp_ge e le m globalz_loop E0 lef mf Out_normal.
Proof.
 intros Index IndexTemp Body Rest;rewrite globalz_loop_source in Rest|-*.
 eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0) (le1:=le1) (m1:=m1)
  (le2:=le1) (m2:=m1) (out1:=Out_normal).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m).
   + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|constructor].
     pose proof (eval_globalz_loop_guard e le m i ltac:(lia) IndexTemp) as Guard.
     destruct (Z.eqb_spec i 0);[lia|exact Guard].
   + exact Body.
 - constructor.
 - constructor.
 - exact Rest.
Qed.

Lemma globalz_table_replace_rep m mf br bt bf bz xs ys j x y : (j<7)%nat ->
 br<>bt -> br<>bf -> br<>bz ->
 globalz_table_rep m br xs ys -> Mem.range_perm m br 0 704 Cur Freeable ->
 fe_at mf br (88*Z.of_nat j+0) (words5 x) -> fe_at mf br (88*Z.of_nat j+40) (words5 y) ->
 Mem.load Mint32 mf br (88*Z.of_nat j+80)=Some (Vint Int.zero) ->
 lframe (globalz_iteration_frame br bt bf bz (Z.of_nat (S j))) m mf ->
 globalz_table_rep mf br (globalz_replace xs j x) (globalz_replace ys j y).
Proof.
 intros Index AT AF AR Table Free X Y Flag Frame k Bound;unfold globalz_replace.
 destruct (Nat.eq_dec k j) as [->|Different];[split;[exact X|];split;[exact Y|exact Flag]|].
 destruct (Table k Bound) as (XK & YK & FlagK).
 assert (Separate:88*Z.of_nat k+84<=88*Z.of_nat j \/ 88*Z.of_nat j+84<=88*Z.of_nat k) by lia.
 assert (Outside:forall pos,88*Z.of_nat k<=pos<88*Z.of_nat k+84 ->
   globalz_iteration_frame br bt bf bz (Z.of_nat (S j)) br pos).
 { intros pos Range;unfold globalz_iteration_frame;split;[exact AT|];split;[exact AF|];split.
   - right;rewrite Nat2Z.inj_succ;destruct Separate;[left|right];lia.
   - left;exact AR. }
 split.
 - eapply curve_keep_field_range;[reflexivity|exact XK|exact Frame|];intros pos Range;apply Outside;lia.
 - split.
   + eapply curve_keep_field_range;[reflexivity|exact YK|exact Frame|];intros pos Range;apply Outside;lia.
   + assert (Valid:Mem.valid_block m br) by (eapply Mem.perm_valid_block;apply (Free 0);lia).
     rewrite (proj1 Frame Mint32 br (88*Z.of_nat k+80) Valid);[exact FlagK|].
     intros pos Range;change (88*Z.of_nat k+80<=pos<88*Z.of_nat k+80+4) in Range;apply Outside;lia.
Qed.

Theorem exec_globalz_loop n : (n<=7)%nat -> forall e le m br bt bf bz xs ys ratios zs,
 NoDup [br;bt;bf;bz] ->
 e!_tmpa=Some (bt,Tstruct __6123 noattr) -> e!_zs=Some (bf,curve_fe_type) ->
 e!_secp256k1_fe_mul=None -> e!_secp256k1_ge_set_gej_zinv=None ->
 le!_a=Some (Vptr br Ptrofs.zero) -> le!_zr=Some (Vptr bz Ptrofs.zero) ->
 le!_i=Some (Vlong (Int64.repr (Z.of_nat n))) -> le!_len=Some (Vlong (Int64.repr 8)) ->
 globalz_table_bounds xs ys -> globalz_ratios_bounds ratios -> square_input_bounds zs ->
 globalz_table_rep m br xs ys -> globalz_ratios_rep m bz ratios -> fe_at m bf 0 (words5 zs) ->
 Mem.range_perm m br 0 704 Cur Freeable -> Mem.range_perm m bt 0 128 Cur Freeable ->
 Mem.range_perm m bf 0 40 Cur Freeable -> Mem.range_perm m bz 0 320 Cur Freeable ->
 let '((xf,yf),zf):=globalz_walk n xs ys ratios zs in exists lef mf,
 Clight2.exec_stmt secp_ge e le m globalz_loop E0 lef mf Out_normal /\
 lef!_i=Some (Vlong Int64.zero) /\ (forall id,id<>_i -> lef!id=le!id) /\
 globalz_table_rep mf br xf yf /\ globalz_ratios_rep mf bz ratios /\ fe_at mf bf 0 (words5 zf) /\
 globalz_table_bounds xf yf /\ square_input_bounds zf /\
 Mem.range_perm mf br 0 704 Cur Freeable /\ Mem.range_perm mf bt 0 128 Cur Freeable /\
 Mem.range_perm mf bf 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 320 Cur Freeable /\
 keeps_permissions m mf /\ lframe (globalz_loop_frame br bt bf bz) m mf /\ readonly_preserved m mf.
Proof.
 induction n as [|j IH];intros Limit e le m br bt bf bz xs ys ratios zs Distinct Tmp Factor MulGlobal ScaleGlobal
  A Ratios IndexTemp Length TableBounds RatioBounds BZ Table RatiosRep Z FreeA FreeT FreeZ FreeR.
 - cbn [globalz_walk];exists le,m;split;[apply exec_globalz_loop_done;exact IndexTemp|];
    split;[exact IndexTemp|];split;[intros;reflexivity|];split;[exact Table|];split;[exact RatiosRep|];
    split;[exact Z|];split;[exact TableBounds|];split;[exact BZ|];split;[exact FreeA|];split;[exact FreeT|];
    split;[exact FreeZ|];split;[exact FreeR|];split;[intros b pos k p Perm;exact Perm|];
    split;[apply lframe_refl|apply preserved_refl].
 - pose proof (Table j ltac:(lia)) as (X & Y & Flag).
   destruct (TableBounds j ltac:(lia)) as (BX & BY).
   assert (Index:1<=Z.of_nat (S j)<8) by lia.
   assert (Prev:Z.of_nat (S j)-1=Z.of_nat j) by lia.
   destruct (exec_globalz_iteration e le (xs j) (ys j) zs (ratios (S j)) m br bt bf bz (Z.of_nat (S j))
     Index Distinct Tmp Factor MulGlobal ScaleGlobal A Ratios IndexTemp Length BX BY BZ
     (RatioBounds (S j) ltac:(lia)) ltac:(rewrite Prev;exact X) ltac:(rewrite Prev;exact Y)
     Z (RatiosRep (S j) ltac:(lia)) FreeA FreeT FreeZ FreeR)
    as (m1 & Body & XO & YO & FlagO & Literal & XT & YT & FlagT & Z1 & Ratio1 & BXO & BYO & BZ1
      & FreeA1 & FreeT1 & FreeZ1 & FreeR1 & Keep1 & Frame1 & Readonly1).
   rewrite Prev in XO,YO,FlagO.
   assert (AT:br<>bt /\ br<>bf /\ br<>bz).
   { inversion Distinct;subst;cbn [In] in *;intuition congruence. }
   set (factor:=globalz_factor_words (Z.of_nat (S j)) zs (ratios (S j))).
   set (xs1:=globalz_replace xs j (ge_zinv_x_words (xs j) factor)).
   set (ys1:=globalz_replace ys j (ge_zinv_y_words (ys j) factor)).
   assert (Table1:globalz_table_rep m1 br xs1 ys1).
   { eapply globalz_table_replace_rep;[lia|exact (proj1 AT)|exact (proj1 (proj2 AT))|exact (proj2 (proj2 AT))|
      exact Table|exact FreeA|exact XO|exact YO|exact FlagO|exact Frame1]. }
   assert (Bounds1:globalz_table_bounds xs1 ys1).
   { intros k Bound;unfold xs1,ys1,globalz_replace;destruct (Nat.eq_dec k j);[split;assumption|apply TableBounds;exact Bound]. }
   assert (Ratios1:globalz_ratios_rep m1 bz ratios).
   { assert (Others:bz<>bt /\ bz<>bf /\ bz<>br).
     { clear -Distinct;repeat match goal with H:NoDup (_::_) |- _=>inversion H;subst;clear H end;
        cbn [In] in *;intuition congruence. }
     intros k Bound;destruct (Nat.eq_dec k (S j)) as [->|Different];[exact Ratio1|].
     eapply curve_keep_field_range;[reflexivity|exact (RatiosRep k Bound)|exact Frame1|].
     intros pos Range;unfold globalz_iteration_frame;split;[exact (proj1 Others)|];
      split;[exact (proj1 (proj2 Others))|];split;[left;exact (proj2 (proj2 Others))|];right;
      assert (40*Z.of_nat k+40<=40*Z.of_nat (S j) \/ 40*Z.of_nat (S j)+40<=40*Z.of_nat k) by lia;
      intuition lia. }
   set (le1:=globalz_iteration_temps le (Z.of_nat (S j))).
   assert (Temps:forall id,id<>_i -> le1!id=le!id).
   { intros id NE;unfold le1,globalz_iteration_temps;rewrite PTree.gso by congruence;reflexivity. }
   assert (Index1:le1!_i=Some (Vlong (Int64.repr (Z.of_nat j)))).
   { unfold le1,globalz_iteration_temps;rewrite Prev;apply PTree.gss. }
   pose proof (IH ltac:(lia) e le1 m1 br bt bf bz xs1 ys1 ratios factor Distinct Tmp Factor MulGlobal ScaleGlobal
     ltac:(rewrite Temps by discriminate;exact A) ltac:(rewrite Temps by discriminate;exact Ratios) Index1
     ltac:(rewrite Temps by discriminate;exact Length) Bounds1 RatioBounds BZ1 Table1 Ratios1 Z1
     FreeA1 FreeT1 FreeZ1 FreeR1) as Rest.
   cbn [globalz_walk];fold factor xs1 ys1.
   destruct (globalz_walk j xs1 ys1 ratios factor) as [[xf yf] zf] eqn:Walk.
   destruct Rest as (lef & mf & Run & FinalIndex & FinalTemps & TableF & RatiosF & ZF & BoundsF & BZF
    & FreeAF & FreeTF & FreeZF & FreeRF & KeepF & FrameF & ReadonlyF).
   exists lef,mf;split;[eapply exec_globalz_loop_join;[exact Index|exact IndexTemp|exact Body|exact Run]|];
    split;[exact FinalIndex|];split.
   + intros id NE;rewrite FinalTemps,Temps by exact NE;reflexivity.
   + split;[exact TableF|];split;[exact RatiosF|];split;[exact ZF|];split;[exact BoundsF|];split;[exact BZF|];
      split;[exact FreeAF|];split;[exact FreeTF|];split;[exact FreeZF|];split;[exact FreeRF|];split.
     * intros b pos k p Perm;apply KeepF;apply Keep1;exact Perm.
     * split.
       -- eapply lframe_trans;[|exact FrameF];eapply lframe_implies;[exact Frame1|];
           intros b pos (NA & NT & NF & NR) Valid;split;[exact NT|];split;[exact NF|];split;left;assumption.
       -- eapply preserved_trans;[exact Readonly1|exact ReadonlyF].
Qed.
