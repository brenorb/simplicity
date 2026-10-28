(** Complete original linear_verify_1 on general valid input/output frames.
    Readers, short circuit, arithmetic, return and seven frees are derived. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_readBit_layout C.jet_frame_layout C.jet_frame_inv C.jet_input_layout C.jet_output_layout C.jet_encoding
 C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_linear_startup C.jet_secp_scalar_io_preserve C.jet_clight_internal_preserve
 C.jet_secp_linear_verify_literal C.jet_secp_linear_verify_public_support
 C.jet_secp_linear_verify_public_reads C.jet_secp_linear_verify_guards
 C.jet_secp_linear_verify_public_body C.jet_secp_linear_verify_arithmetic
 C.jet_secp_curve_literal C.jet_secp_literal_gej_predicate C.jet_secp_add_literal
 C.jet_secp_gej_negate_literal C.jet_secp_literal_add_program C.jet_secp_strauss_complete_program
 C.jet_secp_scalar_add_reader_support C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_canonical_scalar C.jet_toZ C.jet_memset_model.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_ge_is_on_curve literal_gej_is_infinity literal_gej_ge_add
 literal_ge_negate literal_fe_one256 literal_off_curve_linear_combination_1.

Lemma linear_verify_check_route raw ng ax ay bxword byword :
 Bit.toBool (@literal_linear_check Alg.CoreFunSem (((raw,(ax,ay)),ng),(bxword,byword)))=
 if andb (Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay)))
    (Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (bxword,byword))) then
 Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem
    (@literal_gej_ge_add Alg.CoreFunSem
     (@literal_off_curve_linear_combination_1 Alg.CoreFunSem
       ((raw,((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt)),ng),
      @literal_ge_negate Alg.CoreFunSem (bxword,byword)))) else false.
Proof.
 rewrite literal_linear_check_value.
 destruct (Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))),
  (Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (bxword,byword)));reflexivity.
Qed.
Local Ltac verifier_distinct Separate :=
 clear -Separate;unfold linear_verify_public_locals in Separate;
 repeat rewrite NoDup_cons_iff in Separate;repeat rewrite NoDup_cons_iff;
 cbn [In] in *;repeat split;try apply NoDup_nil;intuition congruence.

Theorem eval_linear_verify_initialized (Model:memset_model) v_env m0 bd base bs sbase bw edge cursor N bi inedge rc
 (raw ng ax ay bxword byword:Ty.tySem (Word 8)) :
 linear_startup m0 -> write_frame_at m0 bd base bw edge cursor N ->
 frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi inedge rc ->
 frame_input_cells_at m0 bi inedge rc (map Some (frame_input_word_bits raw)) ->
 frame_input_cells_at m0 bi inedge (rc+256) (map Some (frame_input_word_bits ax)) ->
 frame_input_cells_at m0 bi inedge (rc+512) (map Some (frame_input_word_bits ay)) ->
 frame_input_cells_at m0 bi inedge (rc+768) (map Some (frame_input_word_bits ng)) ->
 frame_input_cells_at m0 bi inedge (rc+1024) (map Some (frame_input_word_bits bxword)) ->
 frame_input_cells_at m0 bi inedge (rc+1280) (map Some (frame_input_word_bits byword)) ->
 0<=rc -> rc+1536<=Int64.max_unsigned -> exists mf,
 Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_linear_verify_1)
  [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] E0 mf
  (Vint (bit_int (Bit.toBool (@literal_linear_check Alg.CoreFunSem (((raw,(ax,ay)),ng),(bxword,byword)))))) /\
 finv m0 bd base bw edge cursor N bi mf
  (Bit.toBool (@literal_linear_check Alg.CoreFunSem (((raw,(ax,ay)),ng),(bxword,byword)))) [] /\
 lframe (fun b _=>~extA m0 bd bw bi b) m0 mf /\ linear_startup mf.
Proof.
 intros Ready Output Base Align Source Raw AX AY NG BX BY RC Max.
 rewrite !linear_verify_check_route.
 set (a:=Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))).
 set (b:=Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (bxword,byword))).
 set (c:=Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem
    (@literal_gej_ge_add Alg.CoreFunSem
     (@literal_off_curve_linear_combination_1 Alg.CoreFunSem
       ((raw,((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt)),ng),
      @literal_ge_negate Alg.CoreFunSem (bxword,byword))))).
 destruct (linear_verify_public_prepare v_env m0 bd base bs sbase bw edge cursor N bi inedge rc
  Output Base Align Source)
  as (mi & md & bl & ba & bb & bk & bg & br & bz & Entry & Copy & OwnedD & SourceD & Separate & Old & Sep & FinD & ReadD & PrepFrame).
 pose (le:=linear_verify_public_temps v_env bd base bs sbase).
 assert (ReadyD:linear_startup md) by (eapply linear_startup_readonly;[exact Ready|exact ReadD]).
 assert (ReadSeparate:NoDup [bk;ba;bg;bb;bl]) by (verifier_distinct Separate).
 assert (ReadSep:xsep (extA m0 bd bw bi) [(bk,0);(ba,0);(bg,0);(bb,0);(bl,0)]).
 { intros [|[|[|[|[|r]]]]] Index;
   [exact (Sep 3%nat ltac:(cbn;lia))|exact (Sep 1%nat ltac:(cbn;lia))|
    exact (Sep 4%nat ltac:(cbn;lia))|exact (Sep 2%nat ltac:(cbn;lia))|
    exact (Sep 0%nat ltac:(cbn;lia))|cbn in Index;lia]. }
 destruct (eval_linear_verify_public_reads m0 bd base bw edge cursor N bi inedge rc raw ng ax ay bxword byword
  md bk ba bg bb bl Output Raw AX AY NG BX BY RC Max
  (OwnedD bk 32 ltac:(clear;cbn [linear_verify_public_storage In];tauto))
  (OwnedD ba 88 ltac:(clear;cbn [linear_verify_public_storage In];tauto))
  (OwnedD bg 32 ltac:(clear;cbn [linear_verify_public_storage In];tauto))
  (OwnedD bb 88 ltac:(clear;cbn [linear_verify_public_storage In];tauto))
  (OwnedD bl 16 ltac:(clear;cbn [linear_verify_public_storage In];tauto)) SourceD ReadSeparate ReadSep FinD)
  as (m1 & m2 & m3 & mr & ScalarA & PointA & ScalarG & PointB & Input & InputNG & XA & YA & FlagA & XB & YB & FlagB & FK & FA & FG & FB & FL & SourceR & FinR & ReadFrame).
 assert (OwnedR:forall block hi,In (block,hi) (linear_verify_public_storage bl ba bb bk bg br bz) ->
  Mem.range_perm mr block 0 hi Cur Freeable).
 { intros block hi Slot;cbn [linear_verify_public_storage In] in Slot;
   repeat match type of Slot with _\/_=>destruct Slot as [Slot|Slot] end;try contradiction;
   inversion Slot;subst block hi;try assumption;
   (eapply curve_keep_free;[clear;lia|apply OwnedD;clear;cbn [linear_verify_public_storage In];tauto|exact ReadFrame|
    intros pos;repeat split;try (verifier_distinct Separate);
    first [exact (Sep 5%nat ltac:(cbn;lia))|exact (Sep 6%nat ltac:(cbn;lia))]]). }
 assert (ReadyR:linear_startup mr).
 { eapply linear_startup_readonly;[exact ReadyD|].
   eapply preserved_trans;[eapply scalar_reader_preserved;exact ScalarA|].
   eapply preserved_trans;[eapply linear_verify_point_reader_preserved;exact PointA|].
   eapply preserved_trans;[eapply scalar_reader_preserved;exact ScalarG|eapply linear_verify_point_reader_preserved;exact PointB]. }
 destruct (eval_linear_verify_guards le mr bl ba bb bk bg br bz ax ay bxword byword
  ltac:(verifier_distinct Separate) XA YA FlagA FA XB YB FlagB FB)
  as (mv & Guards & XAV & YAV & FlagAV & FAV & XBV & YBV & FlagBV & FBV & GuardFrame & GuardRead).
 fold a b in Guards.
 pose (lg:=linear_verify_guard_temps le a b).
 assert (ReadyV:linear_startup mv) by (eapply linear_startup_readonly;[exact ReadyR|exact GuardRead]).
 assert (OwnedV:forall block hi,In (block,hi) (linear_verify_public_storage bl ba bb bk bg br bz) ->
  Mem.range_perm mv block 0 hi Cur Freeable).
 { intros block hi Slot;cbn [linear_verify_public_storage In] in Slot;
   repeat match type of Slot with _\/_=>destruct Slot as [Slot|Slot] end;try contradiction;
   inversion Slot;subst block hi;try assumption;
   (eapply curve_keep_free;[clear;lia|apply OwnedR;clear;cbn [linear_verify_public_storage In];tauto|exact GuardFrame|
    intros pos;split;verifier_distinct Separate]). }
 assert (InputV:scalar_at mv bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))))
  by (eapply scalar_at_lframe;[exact Input|exact GuardFrame|intros;split;verifier_distinct Separate]).
 assert (InputNGV:scalar_at mv bg 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)))))
  by (eapply scalar_at_lframe;[exact InputNG|exact GuardFrame|intros;split;verifier_distinct Separate]).
 assert (GuardsOutside:lframe (fun block _=>~In block (linear_verify_public_locals bl ba bb bk bg br bz)) mr mv).
 { eapply lframe_implies;[exact GuardFrame|].
   intros block pos Outside Valid;clear -Outside;unfold linear_verify_public_locals in Outside;cbn [In] in Outside;split;intuition congruence. }
 assert (Body:exists mc lef,
  Clight2.exec_stmt secp_ge (linear_verify_public_env bl ba bb bk bg br bz) le mr
   (Ssequence linear_verify_guards linear_verify_branch) E0 lef mc
   (Out_return (Some (Vint (bit_int (if andb a b then c else false)),tint))) /\
  (forall block hi,In (block,hi) (linear_verify_public_storage bl ba bb bk bg br bz) ->
    Mem.range_perm mc block 0 hi Cur Freeable) /\ linear_startup mc /\
  lframe (fun block _=>~In block (linear_verify_public_locals bl ba bb bk bg br bz)) mr mc).
 { destruct (andb a b) eqn:Guard.
   - assert (OnA:Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=true).
     { apply andb_true_iff in Guard;exact (proj1 Guard). }
     assert (MathSeparate:NoDup [ba;bb;bk;bg;br;bz]) by (verifier_distinct Separate).
     assert (MathOwned:forall block hi,In (block,hi) (linear_verify_arithmetic_storage ba bb bk bg br bz) ->
      Mem.range_perm mv block 0 hi Cur Freeable).
     { intros block hi Slot;apply OwnedV;clear -Slot;cbn [linear_verify_arithmetic_storage In] in Slot;
       cbn [linear_verify_public_storage In];tauto. }
     destruct (eval_linear_verify_arithmetic Model raw ng ax ay bxword byword mv ba bb bk bg br bz
      ReadyV MathSeparate MathOwned InputV InputNGV XAV YAV FlagAV XBV YBV FlagBV OnA)
      as (ms & mn & mm & mc & SetCall & Neg & Mult & Add & Flag & MathOwnedF & MathReadyF & MathFrame).
     fold c in Flag.
     assert (OwnedC:forall block hi,In (block,hi) (linear_verify_public_storage bl ba bb bk bg br bz) ->
       Mem.range_perm mc block 0 hi Cur Freeable).
     { intros block hi [Slot|Slot].
       - injection Slot as <- <-;eapply curve_keep_free;
          [clear;lia|apply OwnedV;clear;cbn [linear_verify_public_storage In];tauto|exact MathFrame|].
         intros pos;verifier_distinct Separate.
       - apply MathOwnedF;exact Slot. }
     exists mc,(PTree.set _t'1 (Vint (bit_int c)) lg);split.
     + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mv) (le1:=lg);[exact Guards|].
       eapply exec_linear_verify_branch_true.
       * unfold lg;rewrite linear_verify_guard_result,Guard;reflexivity.
       * eapply exec_linear_verify_arithmetic_spine;[exact SetCall|exact Neg|exact Mult|exact Add|exact Flag].
     + split;[exact OwnedC|];split;[exact MathReadyF|].
       eapply lframe_trans;[exact GuardsOutside|].
       eapply lframe_implies;[exact MathFrame|].
       intros block pos Outside Valid;clear -Outside;unfold linear_verify_public_locals in Outside;cbn [In] in *;intuition congruence.
   - exists mv,lg;split.
     + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mv) (le1:=lg);[exact Guards|].
       eapply exec_linear_verify_branch_false;unfold lg;rewrite linear_verify_guard_result,Guard;reflexivity.
     + split;[exact OwnedV|];split;[exact ReadyV|exact GuardsOutside]. }
 destruct Body as (mc & lef & Suffix & OwnedC & ReadyC & BodyFrame).
 destruct (linear_verify_public_free mc bl ba bb bk bg br bz Separate OwnedC)
  as (mf & Free & FreeFrame & FreeRead).
 assert (After:lframe (fun block _=>~In block (linear_verify_public_locals bl ba bb bk bg br bz)) mr mf)
  by (eapply lframe_trans;[exact BodyFrame|exact FreeFrame]).
 assert (Ext:eqext m0 bd bw bi mr mf).
 { eapply lframe_implies;[exact After|].
   intros block pos [_ Valid] _;apply Old;exact Valid. }
 assert (FinalFalse:finv m0 bd base bw edge cursor N bi mf false [])
  by (eapply finv_stable;[exact Output|exact FinR|exact Ext]).
 exists mf;split.
 - eapply eval_funcall_internal with (e:=linear_verify_public_env bl ba bb bk bg br bz)
    (le1:=le) (le2:=lef) (m1:=mi) (m2:=mc)
    (out:=Out_return (Some (Vint (bit_int (if andb a b then c else false)),tint))).
   + exact Entry.
   + rewrite linear_verify_public_body_source;
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=le);[exact Copy|].
     eapply exec_linear_verify_read_spine;[exact ScalarA|exact PointA|exact ScalarG|exact PointB|exact Suffix].
   + change (tbool<>Tvoid /\ Cop.sem_cast (Vint (bit_int (if andb a b then c else false)))
      tint tbool mc=Some (Vint (bit_int (if andb a b then c else false)))).
     destruct (if andb a b then c else false);(split;[discriminate|reflexivity]).
   + exact Free.
 - split.
   + destruct FinalFalse as (Valid & Out & Cap & Effect & Failure).
     split;[exact Valid|];split;[exact Out|];split;[exact Cap|];split;[exact Effect|].
     intros _;apply Failure;reflexivity.
   + split;[|eapply linear_startup_readonly;[exact ReadyC|exact FreeRead]].
     assert (Whole:lframe (fun block _=>Mem.valid_block m0 block /\ ~extA m0 bd bw bi block) m0 mf).
     { eapply lframe_trans.
       - eapply lframe_implies;[exact PrepFrame|intros block pos [Valid Outside] _;apply Old;exact Valid].
       - eapply lframe_trans.
         + eapply lframe_implies;[exact ReadFrame|].
           intros block pos [Valid Outside] _;pose proof (Old block Valid) as Fresh;
            clear -Fresh Outside;unfold linear_verify_public_locals in Fresh;cbn [In] in Fresh;
            repeat split;intuition congruence.
         + eapply lframe_implies;[exact After|intros block pos [Valid Outside] _;apply Old;exact Valid]. }
     eapply lframe_implies;[exact Whole|intros block pos Outside Valid;split;assumption].
Qed.
