(** Complete original in-place gej_add_var call on bounded field representations:
    eleven real allocations, all body branches, actual void result and frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Word Simplicity.Ty Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_curve_statements C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_square_columns
 C.jet_secp_multiply_finish_product C.jet_secp_literal_gej_predicate C.jet_secp_square_spec_bridge C.jet_secp_multiply_normalize_bridge C.jet_secp_curve_frame
 C.jet_secp_field_read_preservation C.jet_secp_gej_add_finite_nonzero C.jet_secp_gej_add_generic_body
 C.jet_secp_gej_add_function_entry C.jet_secp_rescale_literal C.jet_secp_canonical_zero C.jet_secp_add_literal.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output literal_gej_add canonical_fe_is_zero.

Local Ltac allocated_valid := first [assumption |
  match goal with A : Mem.alloc _ _ _=(?mm,?bb) |- Mem.valid_block ?mm ?bb =>
    eapply Mem.valid_new_block;exact A end |
  match goal with A : Mem.alloc _ _ _=(?mm,_) |- Mem.valid_block ?mm _ =>
    eapply Mem.valid_block_alloc;[exact A|allocated_valid] end].
Local Ltac allocated_distinct := first [assumption |
  match goal with A : Mem.alloc _ _ _=(_,?bb) |- ?ba<>?bb =>
    let HE := fresh "HE" in intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ A);rewrite <-HE;allocated_valid end |
  match goal with A : Mem.alloc _ _ _=(_,?ba) |- ?ba<>?bb =>
    let HE := fresh "HE" in intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ A);rewrite HE;allocated_valid end].
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
Local Ltac separate_function_blocks Sep :=
  repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
  repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
  repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
    let HP := fresh "Sep" in let HQ := fresh "Sep" in
    assert (HP : ~P) by (intro;apply HS;left;assumption);
    assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.


Theorem eval_gej_add_generic (ax ay az bx byword bz : Ty.tySem (Word 8)) mx my mz mu mv mw m ba bb :
 ba<>bb ->
 square_input_bounds mx ->
 square_input_bounds my ->
 square_input_bounds mz ->
 square_input_bounds mu ->
 square_input_bounds mv ->
 square_input_bounds mw ->
 radix_value mx mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value my mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value mz mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value mu mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value mv mod feP=@toZ (WordToZ 8) byword mod feP ->
 radix_value mw mod feP=@toZ (WordToZ 8) bz mod feP ->
 Mem.load Mint32 m ba 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 Mem.load Mint32 m bb 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem bz)))) ->
 fe_at m ba 0 (words5 mx) -> fe_at m ba 40 (words5 my) ->
 fe_at m ba 80 (words5 mz) -> fe_at m bb 0 (words5 mu) ->
 fe_at m bb 40 (words5 mv) -> fe_at m bb 80 (words5 mw) ->
 Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bb 0 128 Cur Freeable -> exists mf x y z,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_add_var)
  [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero;Vlong Int64.zero] E0 mf Vundef /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
 Mem.load Mint32 mf ba 120=Some (Vint (bit_int (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem (@literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz))))))) /\
 Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bb 0 128 Cur Freeable /\
 square_input_bounds x /\ square_input_bounds y /\ square_input_bounds z /\
 ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=
 @literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz)) /\
 lframe (fun b _=>b<>ba /\ b<>bb) m mf.
Proof.
 intros SepAB BMX BMY BMZ BMU BMV BMW RMX RMY RMZ RMU RMV RMW FlagA FlagB X Y Z U V W FA FB.
 assert (VA : Mem.valid_block m ba) by (eapply Mem.perm_valid_block;apply (FA 0);lia).
 assert (VB : Mem.valid_block m bb) by (eapply Mem.perm_valid_block;apply (FB 0);lia).
 destruct (Mem.alloc m 0 40) as (m1 & b22) eqn:A22.
 destruct (Mem.alloc m1 0 40) as (m2 & b12) eqn:A12.
 destruct (Mem.alloc m2 0 40) as (m3 & bu) eqn:AU.
 destruct (Mem.alloc m3 0 40) as (m4 & bv) eqn:AV.
 destruct (Mem.alloc m4 0 40) as (m5 & bs) eqn:AS.
 destruct (Mem.alloc m5 0 40) as (m6 & bt) eqn:AT.
 destruct (Mem.alloc m6 0 40) as (m7 & bh) eqn:AH.
 destruct (Mem.alloc m7 0 40) as (m8 & bi) eqn:AI.
 destruct (Mem.alloc m8 0 40) as (m9 & b2) eqn:A2.
 destruct (Mem.alloc m9 0 40) as (m10 & b3) eqn:A3.
 destruct (Mem.alloc m10 0 40) as (mi & bk) eqn:AK.
 assert (Sep : NoDup [ba;bb;bu;bv;bs;bt;b12;b22;bh;bi;b2;b3;bk]).
 { repeat rewrite NoDup_cons_iff;repeat rewrite not_in_cons;
   repeat split;try apply NoDup_nil;try apply in_nil;allocated_distinct. }
 assert (Old : forall b, Mem.valid_block m b ->
 b<>b22 /\ b<>b12 /\ b<>bu /\ b<>bv /\ b<>bs /\ b<>bt /\ b<>bh /\ b<>bi /\ b<>b2 /\ b<>b3 /\ b<>bk).
 { intros b HV;repeat split;allocated_distinct. }
 assert (FAlloc : lframe (fun _ _=>True) m mi) by allocated_frame.
 pose proof (field_at_lframe m mi ba 0 _ _ X FAlloc ltac:(intros;exact Logic.I)) as XI.
 pose proof (field_at_lframe m mi ba 40 _ _ Y FAlloc ltac:(intros;exact Logic.I)) as YI.
 pose proof (field_at_lframe m mi ba 80 _ _ Z FAlloc ltac:(intros;exact Logic.I)) as ZI.
 pose proof (field_at_lframe m mi bb 0 _ _ U FAlloc ltac:(intros;exact Logic.I)) as UI.
 pose proof (field_at_lframe m mi bb 40 _ _ V FAlloc ltac:(intros;exact Logic.I)) as VI.
 pose proof (field_at_lframe m mi bb 80 _ _ W FAlloc ltac:(intros;exact Logic.I)) as WI.
 pose proof (curve_keep_free _ m mi ba 128 ltac:(lia) FA FAlloc ltac:(intros;exact Logic.I)) as FAI.
 pose proof (curve_keep_free _ m mi bb 128 ltac:(lia) FB FAlloc ltac:(intros;exact Logic.I)) as FBI.
 assert (FlagAI : Mem.load Mint32 mi ba 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az))))).
 { rewrite (proj1 FAlloc Mint32 ba 120 VA ltac:(intros;exact Logic.I));exact FlagA. }
 assert (FlagBI : Mem.load Mint32 mi bb 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem bz))))).
 { rewrite (proj1 FAlloc Mint32 bb 120 VB ltac:(intros;exact Logic.I));exact FlagB. }
 assert (F_b22 : Mem.range_perm mi b22 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F_b12 : Mem.range_perm mi b12 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F_bu : Mem.range_perm mi bu 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F_bv : Mem.range_perm mi bv 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F_bs : Mem.range_perm mi bs 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F_bt : Mem.range_perm mi bt 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F_bh : Mem.range_perm mi bh 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F_bi : Mem.range_perm mi bi 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F_b2 : Mem.range_perm mi b2 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F_b3 : Mem.range_perm mi b3 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 assert (F_bk : Mem.range_perm mi bk 0 40 Cur Freeable) by (intros pos HP;allocated_perm HP).
 destruct (exec_gej_add_body_generic (gej_add_helper_env b22 b12 bu bv bs bt bh bi b2 b3 bk)
   (gej_add_entry_temps ba bb) mi ba bb bu bv bs bt b12 b22 bh bi b2 b3 bk mx my mz mu mv mw ax ay az bx byword bz
   eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
   Sep FlagAI FlagBI BMX BMY BMZ BMU BMV BMW RMX RMY RMZ RMU RMV RMW XI YI ZI UI VI WI FAI FBI F_bu F_bv F_bs F_bt F_b12 F_b22 F_bh F_bi F_b2 F_b3 F_bk)
   as (mo & le2 & out & x & y & z & Body & Result & XO & YO & ZO & FlagO & FAO & FBO &
     FUO & FVO & FSO & FTO & F12O & F22O & FHO & FIO & F2O & F3O & FKO & BX & BY & BZ & Literal & FrameB).
 pose proof Sep as Sep0;separate_function_blocks Sep0.
 destruct (free_list_exists [(bt,0,40);(bs,0,40);(bi,0,40);(bv,0,40);(bu,0,40);(b2,0,40);(bh,0,40);(b3,0,40);(bk,0,40);(b22,0,40);(b12,0,40)] mo) as (mf & Free & Unchanged).
 - clear - Sep;separate_function_blocks Sep;cbn;repeat constructor;cbn;
     intro Hin;
     repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin] end;
     congruence.
 - intros b lo hi Hin;cbn [In] in Hin.
   repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin] end;
     try contradiction;inversion Hin;subst b lo hi;assumption.
 - assert (FFree : lframe (fun b _=>b<>b22 /\ b<>b12 /\ b<>bu /\ b<>bv /\ b<>bs /\ b<>bt /\ b<>bh /\ b<>bi /\ b<>b2 /\ b<>b3 /\ b<>bk) mo mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
     intros b pos (N_b22 & N_b12 & N_bu & N_bv & N_bs & N_bt & N_bh & N_bi & N_b2 & N_b3 & N_bk) HV;cbn;intuition congruence. }
   pose proof (field_at_lframe mo mf ba 0 _ _ XO FFree ltac:(intro pos;exact (Old ba VA))) as XF.
   pose proof (field_at_lframe mo mf ba 40 _ _ YO FFree ltac:(intro pos;exact (Old ba VA))) as YF.
   pose proof (field_at_lframe mo mf ba 80 _ _ ZO FFree ltac:(intro pos;exact (Old ba VA))) as ZF.
   pose proof (curve_keep_free _ mo mf ba 128 ltac:(lia) FAO FFree ltac:(intro pos;exact (Old ba VA))) as FAF.
   pose proof (curve_keep_free _ mo mf bb 128 ltac:(lia) FBO FFree ltac:(intro pos;exact (Old bb VB))) as FBF.
   assert (FlagF : Mem.load Mint32 mf ba 120=Some (Vint (bit_int (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem (@literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz)))))))).
   { rewrite (proj1 FFree Mint32 ba 120);[exact FlagO| |intros pos HP;exact (Old ba VA)].
     eapply Mem.perm_valid_block;apply (FAO 0);lia. }
   assert (FrameOld : lframe (fun b _=>Mem.valid_block m b /\ b<>ba /\ b<>bb) m mf).
   { eapply lframe_trans.
     - eapply lframe_implies;[exact FAlloc|];intros;exact Logic.I.
     - eapply lframe_trans.
       + eapply lframe_implies;[exact FrameB|];intros b pos (HV & NA & NB) HVI.
         destruct (Old b HV) as (N_b22 & N_b12 & N_bu & N_bv & N_bs & N_bt & N_bh & N_bi & N_b2 & N_b3 & N_bk).
         unfold gej_add_finite_nonzero_frame;repeat split;assumption.
       + eapply lframe_implies;[exact FFree|];intros b pos (HV & NA & NB) HVO;exact (Old b HV). }
   assert (Frame : lframe (fun b _=>b<>ba /\ b<>bb) m mf).
   { eapply lframe_implies;[exact FrameOld|];intros b pos HP HV;split;assumption. }
   exists mf,x,y,z;split.
   + eapply eval_funcall_internal with (e:=gej_add_helper_env b22 b12 bu bv bs bt bh bi b2 b3 bk)
       (le1:=gej_add_entry_temps ba bb) (le2:=le2) (m1:=mi) (m2:=mo) (out:=out).
     * eapply gej_add_function_entry;eassumption.
     * exact Body.
     * exact Result.
     * rewrite gej_add_function_blocks;exact Free.
   + repeat (first [assumption|split]).
Qed.
