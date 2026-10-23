(** Original A-infinity helper call, including all thirteen allocations/frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_zinv_function
 C.jet_secp_zinv_infinite C.jet_secp_zinv_infinite_products C.jet_secp_point_set_bit.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words.
Local Ltac allocated_valid := first [assumption |
 match goal with A : Mem.alloc _ _ _=(?mm,?bb) |- Mem.valid_block ?mm ?bb =>
   eapply Mem.valid_new_block;exact A end |
 match goal with A : Mem.alloc _ _ _=(?mm,_) |- Mem.valid_block ?mm _ =>
   eapply Mem.valid_block_alloc;[exact A|allocated_valid] end].
Local Ltac allocated_distinct := first [assumption | congruence |
 match goal with A : Mem.alloc _ _ _=(_,?bb) |- ?ba<>?bb =>
   let HE:=fresh "HE" in intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ A);rewrite <-HE;allocated_valid end |
 match goal with A : Mem.alloc _ _ _=(_,?ba) |- ?ba<>?bb =>
   let HE:=fresh "HE" in intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ A);rewrite HE;allocated_valid end].
Local Ltac allocated_perm HP := first [
 match goal with A : Mem.alloc _ _ _=(?mm,?bb) |- Mem.perm ?mm ?bb _ _ _ =>
   eapply Mem.perm_alloc_2;[exact A|exact HP] end |
 match goal with A : Mem.alloc _ _ _=(?mm,_) |- Mem.perm ?mm _ _ _ _ =>
   eapply Mem.perm_alloc_1;[exact A|allocated_perm HP] end].
Local Ltac allocated_frame :=
 lazymatch goal with |- lframe _ ?ma ?mb =>
  tryif constr_eq ma mb then apply lframe_refl else
  match goal with A : Mem.alloc ma _ _=(?mi,_) |- _ =>
   eapply lframe_trans with (m2:=mi);
    [apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact A|allocated_frame] end end.
Local Ltac separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with HC : _ /\ _ |- _ => destruct HC end;
 repeat match goal with HC : ~(?P \/ ?Q) |- _ =>
   let HP:=fresh "Different" in let HQ:=fresh "Different" in
   assert (HP:~P) by (intro;apply HC;left;assumption);
   assert (HQ:~Q) by (intro;apply HC;right;assumption);clear HC end.


Theorem eval_zinv_function_infinite u v inv aflag flag m bp ba bb :
 NoDup [bp;ba;bb] -> aflag<>Int.zero ->
 square_input_bounds u -> square_input_bounds v -> square_input_bounds inv ->
 Mem.load Mint32 m bp 120=Some (Vint aflag) -> Mem.load Mint32 m ba 80=Some (Vint flag) ->
 fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) -> fe_at m bb 0 (words5 inv) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bb 0 40 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_add_zinv_var)
 [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef /\
 fe_at mf bp 0 (words5 (point_mul_words u (square_words inv))) /\
 fe_at mf bp 40 (words5 (point_mul_words v (zinv_inverse_cube inv))) /\
 fe_at mf bp 80 (words5 (point_set_bit_words (Int.eq flag Int.zero))) /\
 Mem.load Mint32 mf bp 120=Some (Vint flag) /\
 fe_at mf ba 0 (words5 u) /\ fe_at mf ba 40 (words5 v) /\ fe_at mf bb 0 (words5 inv) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
 square_input_bounds (point_mul_words u (square_words inv)) /\
 square_input_bounds (point_mul_words v (zinv_inverse_cube inv)) /\
 square_input_bounds (point_set_bit_words (Int.eq flag Int.zero)) /\
 lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m mf.
Proof.
 intros SepInput ANZ BU BV BInv FlagA FlagB U V Inv PF AF InvF.
 separate_blocks SepInput.
 assert (HVP : Mem.valid_block m bp) by (eapply Mem.perm_valid_block;apply (PF 0);lia).
 assert (HVA : Mem.valid_block m ba) by (eapply Mem.perm_valid_block;apply (AF 0);lia).
 assert (HVInv : Mem.valid_block m bb) by (eapply Mem.perm_valid_block;apply (InvF 0);lia).
 destruct (Mem.alloc m 0 40) as (m1 & baz) eqn:A0.
 destruct (Mem.alloc m1 0 40) as (m2 & bz) eqn:A1.
 destruct (Mem.alloc m2 0 40) as (m3 & bu) eqn:A2.
 destruct (Mem.alloc m3 0 40) as (m4 & bv) eqn:A3.
 destruct (Mem.alloc m4 0 40) as (m5 & bs) eqn:A4.
 destruct (Mem.alloc m5 0 40) as (m6 & bt) eqn:A5.
 destruct (Mem.alloc m6 0 40) as (m7 & bh) eqn:A6.
 destruct (Mem.alloc m7 0 40) as (m8 & bi) eqn:A7.
 destruct (Mem.alloc m8 0 40) as (m9 & b2) eqn:A8.
 destruct (Mem.alloc m9 0 40) as (m10 & b3) eqn:A9.
 destruct (Mem.alloc m10 0 40) as (m11 & bk) eqn:A10.
 destruct (Mem.alloc m11 0 40) as (m12 & binv2) eqn:A11.
 destruct (Mem.alloc m12 0 40) as (mi & binv3) eqn:A12.
 assert (Sep : NoDup [bp;ba;bb;baz;bz;bu;bv;bs;bt;bh;bi;b2;b3;bk;binv2;binv3]).
 { repeat rewrite NoDup_cons_iff;repeat rewrite not_in_cons;
   repeat split;try apply NoDup_nil;try apply in_nil;allocated_distinct. }
 assert (Old : forall b,Mem.valid_block m b -> b<>baz /\ b<>bz /\ b<>bu /\ b<>bv /\ b<>bs /\ b<>bt /\ b<>bh /\ b<>bi /\ b<>b2 /\ b<>b3 /\ b<>bk /\ b<>binv2 /\ b<>binv3).
 { intros b HV;repeat split;allocated_distinct. }
 assert (FAlloc : lframe (fun _ _=>True) m mi) by allocated_frame.
 pose proof (field_at_lframe m mi ba 0 _ _ U FAlloc ltac:(intros;exact I)) as UI.
 pose proof (field_at_lframe m mi ba 40 _ _ V FAlloc ltac:(intros;exact I)) as VI.
 pose proof (field_at_lframe m mi bb 0 _ _ Inv FAlloc ltac:(intros;exact I)) as InvI.
 pose proof (curve_keep_free _ m mi bp 128 ltac:(lia) PF FAlloc ltac:(intros;exact I)) as PFI.
 pose proof (curve_keep_free _ m mi ba 88 ltac:(lia) AF FAlloc ltac:(intros;exact I)) as AFI.
 pose proof (curve_keep_free _ m mi bb 40 ltac:(lia) InvF FAlloc ltac:(intros;exact I)) as InvFI.
 assert (FlagAI : Mem.load Mint32 mi bp 120=Some (Vint aflag)).
 { rewrite (proj1 FAlloc Mint32 bp 120 HVP ltac:(intros;exact I));exact FlagA. }
 assert (FlagBI : Mem.load Mint32 mi ba 80=Some (Vint flag)).
 { rewrite (proj1 FAlloc Mint32 ba 80 HVA ltac:(intros;exact I));exact FlagB. }
 assert (F0I : Mem.range_perm mi baz 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F1I : Mem.range_perm mi bz 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F2I : Mem.range_perm mi bu 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F3I : Mem.range_perm mi bv 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F4I : Mem.range_perm mi bs 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F5I : Mem.range_perm mi bt 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F6I : Mem.range_perm mi bh 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F7I : Mem.range_perm mi bi 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F8I : Mem.range_perm mi b2 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F9I : Mem.range_perm mi b3 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F10I : Mem.range_perm mi bk 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F11I : Mem.range_perm mi binv2 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F12I : Mem.range_perm mi binv3 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 pose proof Sep as SepAll;separate_blocks Sep.
 assert (SepBody : NoDup [bp;ba;bb;binv2;binv3]).
 { clear - SepAll;separate_blocks SepAll;repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence. }
 destruct (exec_zinv_infinite_body u v inv aflag flag (zinv_helper_env baz bz bu bv bs bt bh bi b2 b3 bk binv2 binv3) (zinv_entry_temps bp ba bb) mi
 bp ba bb binv2 binv3 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl SepBody ANZ FlagAI FlagBI
 BU BV BInv UI VI InvI PFI AFI InvFI F11I F12I)
 as (mo & Body & XO & YO & ZO & FlagO & UO & VO & InvO & QO & CO & PFO & AFO & InvFO & FInv2O & FInv3O & BXO & BYO & BZO & FB).
 assert (F0O : Mem.range_perm mo baz 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F0I|exact FB|];intro pos;repeat split;congruence. }
 assert (F1O : Mem.range_perm mo bz 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F1I|exact FB|];intro pos;repeat split;congruence. }
 assert (F2O : Mem.range_perm mo bu 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F2I|exact FB|];intro pos;repeat split;congruence. }
 assert (F3O : Mem.range_perm mo bv 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F3I|exact FB|];intro pos;repeat split;congruence. }
 assert (F4O : Mem.range_perm mo bs 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F4I|exact FB|];intro pos;repeat split;congruence. }
 assert (F5O : Mem.range_perm mo bt 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F5I|exact FB|];intro pos;repeat split;congruence. }
 assert (F6O : Mem.range_perm mo bh 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F6I|exact FB|];intro pos;repeat split;congruence. }
 assert (F7O : Mem.range_perm mo bi 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F7I|exact FB|];intro pos;repeat split;congruence. }
 assert (F8O : Mem.range_perm mo b2 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F8I|exact FB|];intro pos;repeat split;congruence. }
 assert (F9O : Mem.range_perm mo b3 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F9I|exact FB|];intro pos;repeat split;congruence. }
 assert (F10O : Mem.range_perm mo bk 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F10I|exact FB|];intro pos;repeat split;congruence. }
 destruct (free_list_exists [(bt,0,40);(bs,0,40);(bi,0,40);(baz,0,40);(bv,0,40);(bu,0,40);(b2,0,40);(bh,0,40);(b3,0,40);(bk,0,40);(bz,0,40);(binv2,0,40);(binv3,0,40)] mo) as (mf & Free & Unchanged).
 - clear - SepAll;separate_blocks SepAll;cbn;repeat constructor;cbn;intuition congruence.
 - intros b lo hi Hin;cbn [In] in Hin.
   repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin] end;
    try contradiction;inversion Hin;subst b lo hi;assumption.
 - assert (FFree : lframe (fun b _=>b<>baz /\ b<>bz /\ b<>bu /\ b<>bv /\ b<>bs /\ b<>bt /\ b<>bh /\ b<>bi /\ b<>b2 /\ b<>b3 /\ b<>bk /\ b<>binv2 /\ b<>binv3) mo mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
     intros b pos (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12) HV;cbn;intuition congruence. }
 pose proof (field_at_lframe mo mf bp 0 _ _ XO FFree ltac:(intro pos;exact (Old bp HVP))) as XOF.
 pose proof (field_at_lframe mo mf bp 40 _ _ YO FFree ltac:(intro pos;exact (Old bp HVP))) as YOF.
 pose proof (field_at_lframe mo mf bp 80 _ _ ZO FFree ltac:(intro pos;exact (Old bp HVP))) as ZOF.
 pose proof (field_at_lframe mo mf ba 0 _ _ UO FFree ltac:(intro pos;exact (Old ba HVA))) as UOF.
 pose proof (field_at_lframe mo mf ba 40 _ _ VO FFree ltac:(intro pos;exact (Old ba HVA))) as VOF.
 pose proof (field_at_lframe mo mf bb 0 _ _ InvO FFree ltac:(intro pos;exact (Old bb HVInv))) as InvOF.
 pose proof (curve_keep_free _ mo mf bp 128 ltac:(lia) PFO FFree ltac:(intro pos;exact (Old bp HVP))) as PFOF.
 pose proof (curve_keep_free _ mo mf ba 88 ltac:(lia) AFO FFree ltac:(intro pos;exact (Old ba HVA))) as AFOF.
 pose proof (curve_keep_free _ mo mf bb 40 ltac:(lia) InvFO FFree ltac:(intro pos;exact (Old bb HVInv))) as InvFOF.
 assert (FlagF : Mem.load Mint32 mf bp 120=Some (Vint flag)).
   { rewrite (proj1 FFree Mint32 bp 120);[exact FlagO| |intros pos HP;exact (Old bp HVP)].
     eapply Mem.perm_valid_block;apply (PFO 0);lia. }
   assert (FrameOld : lframe (fun b _=>Mem.valid_block m b /\ b<>bp /\ b<>ba /\ b<>bb) m mf).
   { eapply lframe_trans.
     - eapply lframe_implies;[exact FAlloc|];intros;exact I.
     - eapply lframe_trans.
       + eapply lframe_implies;[exact FB|];intros b pos (HV & NP & NA & NB) HVI.
         destruct (Old b HV) as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12);repeat split;assumption.
       + eapply lframe_implies;[exact FFree|];intros b pos (HV & NP & NA & NB) HVO;exact (Old b HV). }
   assert (Frame : lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m mf).
   { eapply lframe_implies;[exact FrameOld|];intros b pos HP HV;split;assumption. }
   exists mf;split.
   + eapply eval_funcall_internal with (e:=zinv_helper_env baz bz bu bv bs bt bh bi b2 b3 bk binv2 binv3)
       (le1:=zinv_entry_temps bp ba bb)
       (le2:=zinv_infinite_temps (zinv_entry_temps bp ba bb) aflag flag)
       (m1:=mi) (m2:=mo) (out:=Out_return None).
     * eapply zinv_function_entry;eassumption.
     * exact Body.
     * reflexivity.
     * rewrite zinv_function_blocks;exact Free.
   + repeat first [assumption|split].
Qed.
