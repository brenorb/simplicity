(** Original zinv function entry: all thirteen local allocations. *)
From Coq Require Import ZArith List Lia Sorting.Permutation.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_zinv_finite.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition zinv_helper_env baz bz bu bv bs bt bh bi b2 b3 bk binv2 binv3 := PTree.set _bzinv3 (binv3,curve_fe_type) (PTree.set _bzinv2 (binv2,curve_fe_type) (PTree.set _t (bk,curve_fe_type) (PTree.set _h3 (b3,curve_fe_type) (PTree.set _h2 (b2,curve_fe_type) (PTree.set _i (bi,curve_fe_type) (PTree.set _h (bh,curve_fe_type) (PTree.set _s2 (bt,curve_fe_type) (PTree.set _s1 (bs,curve_fe_type) (PTree.set _u2 (bv,curve_fe_type) (PTree.set _u1 (bu,curve_fe_type) (PTree.set _z12 (bz,curve_fe_type) (PTree.set _az (baz,curve_fe_type) (empty_env))))))))))))).
Definition zinv_entry_temps bp ba bb := PTree.set _bzinv (Vptr bb Ptrofs.zero)
 (PTree.set _b (Vptr ba Ptrofs.zero) (PTree.set _a (Vptr bp Ptrofs.zero)
 (PTree.set _r (Vptr bp Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_gej_add_zinv_var))))).
Lemma zinv_function_ok : fn_okb f_secp256k1_gej_add_zinv_var=true.
Proof. reflexivity. Qed.
Lemma zinv_function_entry m m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 mi bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk binv2 binv3 :
 Mem.alloc m 0 40=(m1,baz) ->
 Mem.alloc m1 0 40=(m2,bz) ->
 Mem.alloc m2 0 40=(m3,bu) ->
 Mem.alloc m3 0 40=(m4,bv) ->
 Mem.alloc m4 0 40=(m5,bs) ->
 Mem.alloc m5 0 40=(m6,bt) ->
 Mem.alloc m6 0 40=(m7,bh) ->
 Mem.alloc m7 0 40=(m8,bi) ->
 Mem.alloc m8 0 40=(m9,b2) ->
 Mem.alloc m9 0 40=(m10,b3) ->
 Mem.alloc m10 0 40=(m11,bk) ->
 Mem.alloc m11 0 40=(m12,binv2) ->
 Mem.alloc m12 0 40=(mi,binv3) ->
 function_entry2 secp_ge f_secp256k1_gej_add_zinv_var
 [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] m
 (zinv_helper_env baz bz bu bv bs bt bh bi b2 b3 bk binv2 binv3) (zinv_entry_temps bp ba bb) mi.
Proof.
 intros A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12;destruct (fn_okb_true _ zinv_function_ok) as (HN1 & HN2 & HD).
 constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
 eapply alloc_variables_cons with (m1:=m1) (b1:=baz);[exact A0|].
 eapply alloc_variables_cons with (m1:=m2) (b1:=bz);[exact A1|].
 eapply alloc_variables_cons with (m1:=m3) (b1:=bu);[exact A2|].
 eapply alloc_variables_cons with (m1:=m4) (b1:=bv);[exact A3|].
 eapply alloc_variables_cons with (m1:=m5) (b1:=bs);[exact A4|].
 eapply alloc_variables_cons with (m1:=m6) (b1:=bt);[exact A5|].
 eapply alloc_variables_cons with (m1:=m7) (b1:=bh);[exact A6|].
 eapply alloc_variables_cons with (m1:=m8) (b1:=bi);[exact A7|].
 eapply alloc_variables_cons with (m1:=m9) (b1:=b2);[exact A8|].
 eapply alloc_variables_cons with (m1:=m10) (b1:=b3);[exact A9|].
 eapply alloc_variables_cons with (m1:=m11) (b1:=bk);[exact A10|].
 eapply alloc_variables_cons with (m1:=m12) (b1:=binv2);[exact A11|].
 eapply alloc_variables_cons with (m1:=mi) (b1:=binv3);[exact A12|constructor].
Qed.

Lemma zinv_function_blocks baz bz bu bv bs bt bh bi b2 b3 bk binv2 binv3 :
 blocks_of_env secp_ge (zinv_helper_env baz bz bu bv bs bt bh bi b2 b3 bk binv2 binv3) =
 [(bt,0,40);(bs,0,40);(bi,0,40);(baz,0,40);(bv,0,40);(bu,0,40);(b2,0,40);(bh,0,40);(b3,0,40);(bk,0,40);(bz,0,40);(binv2,0,40);(binv3,0,40)].
Proof. reflexivity. Qed.
Lemma zinv_function_result x z u inv m :
 outcome_result_value (zinv_finite_out x z u inv) (fn_return f_secp256k1_gej_add_zinv_var) Vundef m.
Proof. unfold zinv_finite_out;destruct (Z.eqb _ 0);reflexivity. Qed.

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

Theorem eval_zinv_function_finite x y z u v inv m bp ba bb :
 NoDup [bp;ba;bb] ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v -> square_input_bounds inv ->
 Mem.load Mint32 m bp 120=Some (Vint Int.zero) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) -> fe_at m bb 0 (words5 inv) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bb 0 40 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_add_zinv_var)
 [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef /\
 fe_at mf bp 0 (words5 (zinv_finite_x x y z u v inv)) /\
 fe_at mf bp 40 (words5 (zinv_finite_y x y z u v inv)) /\
 fe_at mf bp 80 (words5 (zinv_finite_z x y z u v inv)) /\
 Mem.load Mint32 mf bp 120=Some (Vint (zinv_finite_flag x y z u v inv)) /\
 fe_at mf ba 0 (words5 u) /\ fe_at mf ba 40 (words5 v) /\ fe_at mf bb 0 (words5 inv) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
 square_input_bounds (zinv_finite_x x y z u v inv) /\ square_input_bounds (zinv_finite_y x y z u v inv) /\
 square_input_bounds (zinv_finite_z x y z u v inv) /\ lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m mf.
Proof.
 intros SepInput BX BY BZ BU BV BInv FlagA FlagB X Y ZAt U V Inv PF AF InvF.
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
 pose proof (field_at_lframe m mi bp 0 _ _ X FAlloc ltac:(intros;exact I)) as XI.
 pose proof (field_at_lframe m mi bp 40 _ _ Y FAlloc ltac:(intros;exact I)) as YI.
 pose proof (field_at_lframe m mi bp 80 _ _ ZAt FAlloc ltac:(intros;exact I)) as ZAtI.
 pose proof (field_at_lframe m mi ba 0 _ _ U FAlloc ltac:(intros;exact I)) as UI.
 pose proof (field_at_lframe m mi ba 40 _ _ V FAlloc ltac:(intros;exact I)) as VI.
 pose proof (field_at_lframe m mi bb 0 _ _ Inv FAlloc ltac:(intros;exact I)) as InvI.
 pose proof (curve_keep_free _ m mi bp 128 ltac:(lia) PF FAlloc ltac:(intros;exact I)) as PFI.
 pose proof (curve_keep_free _ m mi ba 88 ltac:(lia) AF FAlloc ltac:(intros;exact I)) as AFI.
 pose proof (curve_keep_free _ m mi bb 40 ltac:(lia) InvF FAlloc ltac:(intros;exact I)) as InvFI.
 assert (FlagAI : Mem.load Mint32 mi bp 120=Some (Vint Int.zero)).
 { rewrite (proj1 FAlloc Mint32 bp 120 HVP ltac:(intros;exact I));exact FlagA. }
 assert (FlagBI : Mem.load Mint32 mi ba 80=Some (Vint Int.zero)).
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
 assert (SepBody : NoDup [bp;ba;bb;baz;bz;bu;bv;bs;bt;bh;bi;b2;b3;bk]).
 { pose proof (@NoDup_remove_1 block [bp;ba;bb;baz;bz;bu;bv;bs;bt;bh;bi;b2;b3;bk;binv2] [] binv3 SepAll) as Without3.
   exact (@NoDup_remove_1 block [bp;ba;bb;baz;bz;bu;bv;bs;bt;bh;bi;b2;b3;bk] [] binv2 Without3). }
 assert (OwnedI : zinv_finite_owned mi bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk).
 { unfold zinv_finite_owned,C.jet_secp_zinv_start.zinv_start_owned;repeat first [assumption|split]. }
 destruct (exec_zinv_finite_body x y z u v inv (zinv_helper_env baz bz bu bv bs bt bh bi b2 b3 bk binv2 binv3) (zinv_entry_temps bp ba bb) mi
 bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl SepBody
 BX BY BZ BU BV BInv FlagAI FlagBI XI YI ZAtI UI VI InvI OwnedI)
 as (mo & Body & XO & YO & ZO & FlagO & UO & VO & InvO & OwnedO & BXO & BYO & BZO & FB).
 destruct OwnedO as ((PFO & AFO & InvFO & AZFO & ZFO & UFO & VFO & SFO & TFO) & HFO & IFO & F2O & F3O & FKO).
 assert (FInv2O : Mem.range_perm mo binv2 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F11I|exact FB|];intro pos;unfold zinv_finite_frame;
   repeat split;try (left;congruence);congruence. }
 assert (FInv3O : Mem.range_perm mo binv3 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F12I|exact FB|];intro pos;unfold zinv_finite_frame;
   repeat split;try (left;congruence);congruence. }
 destruct (free_list_exists [(bt,0,40);(bs,0,40);(bi,0,40);(baz,0,40);(bv,0,40);(bu,0,40);(b2,0,40);(bh,0,40);(b3,0,40);(bk,0,40);(bz,0,40);(binv2,0,40);(binv3,0,40)] mo) as (mf & Free & Unchanged).
 - clear - SepAll; cbn.
   assert (NDFree : NoDup [bt;bs;bi;baz;bv;bu;b2;bh;b3;bk;bz;binv2;binv3]).
   { pose proof (@NoDup_app_remove_l block [bp;ba;bb]
       [baz;bz;bu;bv;bs;bt;bh;bi;b2;b3;bk;binv2;binv3] SepAll) as Locals.
     eapply (@Permutation_NoDup block
       [baz;bz;bu;bv;bs;bt;bh;bi;b2;b3;bk;binv2;binv3]
       [bt;bs;bi;baz;bv;bu;b2;bh;b3;bk;bz;binv2;binv3]).
     - apply NoDup_Permutation_bis; [exact Locals|cbn;lia|].
       intros value HIn; cbn in HIn |- *; tauto.
     - exact Locals. }
   clear -NDFree.
   assert (Convert : forall xs : list block, NoDup xs -> list_norepet xs).
   { intros xs ND; induction ND; constructor; assumption. }
   exact (Convert _ NDFree).
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
 assert (FlagF : Mem.load Mint32 mf bp 120=Some (Vint (zinv_finite_flag x y z u v inv))).
   { rewrite (proj1 FFree Mint32 bp 120);[exact FlagO| |intros pos HP;exact (Old bp HVP)].
     eapply Mem.perm_valid_block;apply (PFO 0);lia. }
   assert (FrameOld : lframe (fun b _=>Mem.valid_block m b /\ b<>bp /\ b<>ba /\ b<>bb) m mf).
   { eapply lframe_trans.
     - eapply lframe_implies;[exact FAlloc|];intros;exact I.
     - eapply lframe_trans.
       + eapply lframe_implies;[exact FB|];intros b pos (HV & NP & NA & NB) HVI.
         destruct (Old b HV) as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12).
         unfold zinv_finite_frame;repeat split;try assumption;left;exact NA.
       + eapply lframe_implies;[exact FFree|];intros b pos (HV & NP & NA & NB) HVO;exact (Old b HV). }
   assert (Frame : lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m mf).
   { eapply lframe_implies;[exact FrameOld|];intros b pos HP HV;split;assumption. }
   exists mf;split.
   + eapply eval_funcall_internal with (e:=zinv_helper_env baz bz bu bv bs bt bh bi b2 b3 bk binv2 binv3)
       (le1:=zinv_entry_temps bp ba bb)
       (le2:=zinv_finite_temps (zinv_heads_temps (zinv_entry_temps bp ba bb)) x y z u v inv)
       (m1:=mi) (m2:=mo) (out:=zinv_finite_out x z u inv).
     * eapply zinv_function_entry;eassumption.
     * exact Body.
     * apply zinv_function_result.
     * rewrite zinv_function_blocks;exact Free.
   + repeat first [assumption|split].
Qed.
