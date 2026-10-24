(** Complete original SWU helper call, with actual function entry, thirteen
    local allocations and their original frees. The CTZ contract is explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.extraMath C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
  C.jet_secp_swu_body C.jet_secp_swu_startup C.jet_secp_swu_literal C.jet_secp_square_spec_bridge
  C.jet_secp_square_columns C.jet_secp_rescale_literal C.jet_secp_multiply_normalize_bridge
  C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_reader_rho rescale_field_output literal_swu.

Definition swu_function_env bw bx bj bt ba bb bc bA bB bC by1 by2 by3 :=
  PTree.set _y3 (by3,curve_fe_type)
  (PTree.set _y2 (by2,curve_fe_type)
  (PTree.set _y1 (by1,curve_fe_type)
  (PTree.set _gammain (bC,curve_fe_type)
  (PTree.set _betain (bB,curve_fe_type)
  (PTree.set _alphain (bA,curve_fe_type)
  (PTree.set _x3 (bc,curve_fe_type)
  (PTree.set _x2 (bb,curve_fe_type)
  (PTree.set _x1 (ba,curve_fe_type)
  (PTree.set _tmp (bt,curve_fe_type)
  (PTree.set _jinv (bj,curve_fe_type)
  (PTree.set _x3d (bx,curve_fe_type)
  (PTree.set _wd (bw,curve_fe_type) empty_env)))))))))))).
Definition swu_function_temps bp bi := PTree.set _t (Vptr bi Ptrofs.zero)
  (PTree.set _ge (Vptr bp Ptrofs.zero) (create_undef_temps (fn_temps f_shallue_van_de_woestijne))).
Lemma swu_function_ok : fn_okb f_shallue_van_de_woestijne=true.
Proof. reflexivity. Qed.
Lemma swu_function_entry m m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 mi
    bp bi bw bx bj bt ba bb bc bA bB bC by1 by2 by3 :
  Mem.alloc m 0 40=(m1,bw) -> Mem.alloc m1 0 40=(m2,bx) ->
  Mem.alloc m2 0 40=(m3,bj) -> Mem.alloc m3 0 40=(m4,bt) ->
  Mem.alloc m4 0 40=(m5,ba) -> Mem.alloc m5 0 40=(m6,bb) ->
  Mem.alloc m6 0 40=(m7,bc) -> Mem.alloc m7 0 40=(m8,bA) ->
  Mem.alloc m8 0 40=(m9,bB) -> Mem.alloc m9 0 40=(m10,bC) ->
  Mem.alloc m10 0 40=(m11,by1) -> Mem.alloc m11 0 40=(m12,by2) -> Mem.alloc m12 0 40=(mi,by3) ->
  function_entry2 secp_ge f_shallue_van_de_woestijne [Vptr bp Ptrofs.zero;Vptr bi Ptrofs.zero] m
    (swu_function_env bw bx bj bt ba bb bc bA bB bC by1 by2 by3) (swu_function_temps bp bi) mi.
Proof.
  intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13.
  destruct (fn_okb_true _ swu_function_ok) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
  eapply alloc_variables_cons with (m1:=m1) (b1:=bw);[exact A1|].
  eapply alloc_variables_cons with (m1:=m2) (b1:=bx);[exact A2|].
  eapply alloc_variables_cons with (m1:=m3) (b1:=bj);[exact A3|].
  eapply alloc_variables_cons with (m1:=m4) (b1:=bt);[exact A4|].
  eapply alloc_variables_cons with (m1:=m5) (b1:=ba);[exact A5|].
  eapply alloc_variables_cons with (m1:=m6) (b1:=bb);[exact A6|].
  eapply alloc_variables_cons with (m1:=m7) (b1:=bc);[exact A7|].
  eapply alloc_variables_cons with (m1:=m8) (b1:=bA);[exact A8|].
  eapply alloc_variables_cons with (m1:=m9) (b1:=bB);[exact A9|].
  eapply alloc_variables_cons with (m1:=m10) (b1:=bC);[exact A10|].
  eapply alloc_variables_cons with (m1:=m11) (b1:=by1);[exact A11|].
  eapply alloc_variables_cons with (m1:=m12) (b1:=by2);[exact A12|].
  eapply alloc_variables_cons with (m1:=mi) (b1:=by3);[exact A13|constructor].
Qed.

Lemma swu_function_blocks bw bx bj bt ba bb bc bA bB bC by1 by2 by3 :
  blocks_of_env secp_ge (swu_function_env bw bx bj bt ba bb bc bA bB bC by1 by2 by3)=
  [(bw,0,40);(bC,0,40);(by2,0,40);(by1,0,40);(by3,0,40);(bA,0,40);
   (bb,0,40);(ba,0,40);(bc,0,40);(bx,0,40);(bt,0,40);(bj,0,40);(bB,0,40)].
Proof. reflexivity. Qed.

Local Ltac swu_alloc_valid := first [assumption |
  match goal with Alloc : Mem.alloc _ _ _=(?mm,?bb) |- Mem.valid_block ?mm ?bb =>
    eapply Mem.valid_new_block;exact Alloc end |
  match goal with Alloc : Mem.alloc _ _ _=(?mm,_) |- Mem.valid_block ?mm _ =>
    eapply Mem.valid_block_alloc;[exact Alloc|swu_alloc_valid] end].
Local Ltac swu_alloc_distinct := first [assumption |
  match goal with Alloc : Mem.alloc _ _ _=(_,?bb) |- ?ba<>?bb =>
    let Same:=fresh "Same" in intro Same;
    apply (Mem.fresh_block_alloc _ _ _ _ _ Alloc);rewrite <-Same;swu_alloc_valid end |
  match goal with Alloc : Mem.alloc _ _ _=(_,?ba) |- ?ba<>?bb =>
    let Same:=fresh "Same" in intro Same;
    apply (Mem.fresh_block_alloc _ _ _ _ _ Alloc);rewrite Same;swu_alloc_valid end].
Local Ltac swu_alloc_perm Range := first [
  match goal with Alloc : Mem.alloc _ _ _=(?mm,?bb) |- Mem.perm ?mm ?bb _ _ _ =>
    eapply Mem.perm_alloc_2;[exact Alloc|exact Range] end |
  match goal with Alloc : Mem.alloc _ _ _=(?mm,_) |- Mem.perm ?mm _ _ _ _ =>
    eapply Mem.perm_alloc_1;[exact Alloc|swu_alloc_perm Range] end].
Local Ltac swu_alloc_frame := lazymatch goal with |- lframe _ ?ma ?mb =>
  tryif constr_eq ma mb then apply lframe_refl else
  match goal with Alloc : Mem.alloc ma _ _=(?mi,_) |- _ =>
    eapply lframe_trans with (m2:=mi);
      [apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc|swu_alloc_frame] end end.

Theorem eval_swu_function t m bp bi :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  bp<>bi -> swu_startup m -> fe_at m bi 0 (words5 (square_reader_rho t)) ->
  Mem.range_perm m bi 0 40 Cur Freeable -> Mem.range_perm m bp 0 88 Cur Freeable ->
  exists mf x y,
  Clight2.eval_funcall secp_ge m (Internal f_shallue_van_de_woestijne)
    [Vptr bp Ptrofs.zero;Vptr bi Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\
  Mem.load Mint32 mf bp 80=Some (Vint Int.zero) /\
  Mem.range_perm mf bi 0 40 Cur Freeable /\ Mem.range_perm mf bp 0 88 Cur Freeable /\
  square_input_bounds x /\ square_input_bounds y /\
  (rescale_field_output x,rescale_field_output y)=@literal_swu Alg.CoreFunSem t /\
  swu_startup mf /\ lframe (fun b _=>b<>bp /\ b<>bi) m mf /\ readonly_preserved m mf.
Proof.
  intros Count PI Ready Input FI FP.
  assert (VI:Mem.valid_block m bi) by (eapply Mem.perm_valid_block;apply (FI 0);lia).
  assert (VP:Mem.valid_block m bp) by (eapply Mem.perm_valid_block;apply (FP 0);lia).
  destruct (Mem.alloc m 0 40) as (m1 & bw) eqn:A1.
  destruct (Mem.alloc m1 0 40) as (m2 & bx) eqn:A2.
  destruct (Mem.alloc m2 0 40) as (m3 & bj) eqn:A3.
  destruct (Mem.alloc m3 0 40) as (m4 & bt) eqn:A4.
  destruct (Mem.alloc m4 0 40) as (m5 & ba) eqn:A5.
  destruct (Mem.alloc m5 0 40) as (m6 & bb) eqn:A6.
  destruct (Mem.alloc m6 0 40) as (m7 & bc) eqn:A7.
  destruct (Mem.alloc m7 0 40) as (m8 & bA) eqn:A8.
  destruct (Mem.alloc m8 0 40) as (m9 & bB) eqn:A9.
  destruct (Mem.alloc m9 0 40) as (m10 & bC) eqn:A10.
  destruct (Mem.alloc m10 0 40) as (m11 & by1) eqn:A11.
  destruct (Mem.alloc m11 0 40) as (m12 & by2) eqn:A12.
  destruct (Mem.alloc m12 0 40) as (mi & by3) eqn:A13.
  pose proof (swu_function_entry m m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 mi
    bp bi bw bx bj bt ba bb bc bA bB bC by1 by2 by3 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13) as Entry.
  assert (Sep:NoDup [bp;bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3;bt]).
  { repeat rewrite NoDup_cons_iff;repeat rewrite not_in_cons;
      repeat split;try apply NoDup_nil;try apply in_nil;swu_alloc_distinct. }
  assert (Old:forall b,Mem.valid_block m b -> forall other,
    In other [bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3;bt] -> b<>other).
  { intros b Valid other Member;cbn [In] in Member;
      repeat destruct Member as [<- | Member];try contradiction;swu_alloc_distinct. }
  assert (FrameA:lframe (fun _ _=>True) m mi) by swu_alloc_frame.
  assert (ROA:readonly_preserved m mi) by (eapply entry_preserved;exact Entry).
  assert (ReadyI:swu_startup mi) by (eapply swu_startup_preserved;[exact Ready|exact ROA]).
  pose proof (field_at_lframe m mi bi 0 _ _ Input FrameA ltac:(intros;exact Logic.I)) as InputI.
  pose proof (curve_keep_free _ m mi bi 40 ltac:(lia) FI FrameA ltac:(intros;exact Logic.I)) as FII.
  pose proof (curve_keep_free _ m mi bp 88 ltac:(lia) FP FrameA ltac:(intros;exact Logic.I)) as FPI.
  assert (FreeI:Forall (fun b=>Mem.range_perm mi b 0 40 Cur Freeable)
    [bi;bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3;bt]).
  { constructor;[exact FII|];rewrite Forall_forall;intros b Member;
      cbn [In] in Member;repeat destruct Member as [<- | Member];try contradiction.
    all: intros pos Range;swu_alloc_perm Range. }
  assert (Plain:plain_env (swu_function_env bw bx bj bt ba bb bc bA bB bC by1 by2 by3)) by
    (eapply entry_plain;[exact Entry|reflexivity]).
  pose proof (exec_swu_body t (swu_function_env bw bx bj bt ba bb bc bA bB bC by1 by2 by3)
    (swu_function_temps bp bi) mi bp bi bw ba bx bj bb bc bA bB bC by1 by2 by3 bt Count Plain) as Run.
  do 28 specialize (Run eq_refl).
  destruct (Run Sep ReadyI InputI FreeI FPI)
    as (lef & mo & x & y & Body & X & Y & Flag & FPO & FreeO & BX & BY & Literal & ReadyO & FrameB & ROB).
  pose proof FreeO as AllFree;rewrite Forall_forall in AllFree.
  destruct (free_list_exists
    [(bw,0,40);(bC,0,40);(by2,0,40);(by1,0,40);(by3,0,40);(bA,0,40);
     (bb,0,40);(ba,0,40);(bc,0,40);(bx,0,40);(bt,0,40);(bj,0,40);(bB,0,40)] mo)
    as (mf & Free & Unchanged).
  - cbn;repeat constructor;repeat rewrite not_in_cons;
      repeat split;try apply in_nil;swu_alloc_distinct.
  - intros b lo hi Member;cbn [In] in Member;
      repeat destruct Member as [Member | Member];try contradiction;
      inversion Member;subst b lo hi;apply AllFree;
      repeat (first [left;reflexivity|right]).
  - assert (FrameF:lframe
      (fun b _=>forall other,In other [bw;ba;bx;bj;bb;bc;bA;bB;bC;by1;by2;by3;bt] -> b<>other) mo mf).
    { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
      intros b pos Outside Valid Member;apply (Outside b);[|reflexivity].
      clear -Member;cbn [map fst snd In] in *;tauto. }
    pose proof (field_at_lframe mo mf bp 0 _ _ X FrameF ltac:(intros;exact (Old bp VP))) as XF.
    pose proof (field_at_lframe mo mf bp 40 _ _ Y FrameF ltac:(intros;exact (Old bp VP))) as YF.
    assert (FlagF:Mem.load Mint32 mf bp 80=Some (Vint Int.zero)).
    { rewrite (proj1 FrameF Mint32 bp 80 ltac:(eapply Mem.perm_valid_block;apply (FPO 0);lia)
        ltac:(intros;exact (Old bp VP)));exact Flag. }
    pose proof (curve_keep_free _ mo mf bi 40 ltac:(lia)
      (AllFree bi ltac:(left;reflexivity)) FrameF ltac:(intros;exact (Old bi VI))) as FIF.
    pose proof (curve_keep_free _ mo mf bp 88 ltac:(lia) FPO FrameF ltac:(intros;exact (Old bp VP))) as FPF.
    assert (ROF:readonly_preserved mo mf) by (eapply freelist_preserved;exact Free).
    assert (ReadOnly:readonly_preserved m mf) by
      (eapply preserved_trans;[exact ROA|];eapply preserved_trans;[exact ROB|exact ROF]).
    assert (FrameOld:lframe (fun b _=>Mem.valid_block m b /\ b<>bp /\ b<>bi) m mf).
    { eapply lframe_trans.
      - eapply lframe_implies;[exact FrameA|];intros;exact Logic.I.
      - eapply lframe_trans.
        + eapply lframe_implies;[exact FrameB|];intros b pos [Valid [NP NI]] _ Member.
          destruct Member as [Same | [Same | Member] ].
          * apply NP;symmetry;exact Same.
          * apply NI;symmetry;exact Same.
          * apply (Old b Valid b Member);reflexivity.
        + eapply lframe_implies;[exact FrameF|];intros b pos [Valid _] _;exact (Old b Valid). }
    exists mf,x,y;split.
    + eapply eval_funcall_internal with
        (e:=swu_function_env bw bx bj bt ba bb bc bA bB bC by1 by2 by3)
        (le1:=swu_function_temps bp bi) (le2:=lef) (m1:=mi) (m2:=mo) (out:=Out_normal).
      * exact Entry.
      * exact Body.
      * reflexivity.
      * rewrite swu_function_blocks;exact Free.
    + split;[exact XF|];split;[exact YF|];split;[exact FlagF|];split;[exact FIF|];split;[exact FPF|];
        split;[exact BX|];split;[exact BY|];split;[exact Literal|];split.
      * eapply swu_startup_preserved;[exact ReadyO|exact ROF].
      * split;[|exact ReadOnly];eapply lframe_implies;[exact FrameOld|];intros b pos Apart Valid;split;assumption.
Qed.
