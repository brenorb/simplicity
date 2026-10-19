(** Full original-C public contract of [simplicity_fe_square] against the
    literal canonical [fe_square] ([iden &&& iden >>> fe_multiply]): actual
    entry, two local allocations, source copy, original reader, in-place
    squaring ([r = a]), wide writer, return and freeing. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_frame_inv C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_math C.jet_secp_fe_nv.
Require Import C.jet_secp_wrapper_run C.jet_secp_local_regions C.jet_secp_local_call.
Require Import C.jet_secp_public_copy C.jet_secp_public_body C.jet_secp_public_lifecycle C.jet_secp_normalize_local.
Require Import C.jet_secp_canonical_normalize C.jet_secp_negate_writer_bridge.
Require Import C.jet_secp_write_fe_wide_values C.jet_secp_write_fe_wide_exec.
Require Import C.jet_parallel_fe_sqr_run C.jet_parallel_fe_sqr_field.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 20.
Local Opaque literal_fe_square canonical_fe_normalize encode.

(** ** Squaring and writing after the original reader *)
Theorem eval_sqr_write_after_read_field m0 bd dbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word 8)) mr ba bl :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  fe_at mr ba 0 (map Int64.repr (fe_limbs_of
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)))) ->
  Mem.range_perm mr ba 0 40 Cur Freeable -> Mem.range_perm mr bl 0 16 Cur Freeable ->
  ba <> bl -> xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] 256
    (read_fe_rho (frame_input_word_bits value) rc) (read_fe_log bi (Ptrofs.repr edge)) mr ->
  exists mn mw,
    Clight2.eval_funcall secp_ge mr (Internal f_secp256k1_fe_sqr)
      [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero] E0 mn Vundef /\
    Clight2.eval_funcall secp_ge mn (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero] E0 mw Vundef /\
    finv m0 bd dbase bw outedge cursor N bi mw true
      (encode (@literal_fe_square Alg.CoreFunSem value)) /\
    Mem.range_perm mw ba 0 40 Cur Freeable /\ Mem.range_perm mw bl 0 16 Cur Freeable /\
    lframe (fun b pos => ~ foot [(ba,0)] (map rshape fe_sqr_regs) b pos) mr mn /\
    lframe (frame (extA m0 bd bw bi) [(ba,0)] local_write_initial_regs mn) mn mw.
Proof.
  intros HO HField HFreeA HFreeL HSeparate HS HI.
  change (Int64.repr rc = Int64.repr rc /\
    finv m0 bd dbase bw outedge cursor N bi mr false [] /\ 0 + 256 <= N /\ 0 <= 256) in HI.
  destruct HI as (_ & HFIN0 & HN & _).
  destruct (eval_fe_sqr_from_normalized_field mr ba value HField HFreeA)
    as (mn & t0 & t1 & t2 & t3 & t4 & HSqr & HOut & H0 & H1 & H2 & H3 & H4 & HOutput &
      HFreeA' & HSqrFrame).
  assert (HExt : lframe (fun b' _ => extA m0 bd bw bi b') mr mn).
  { eapply lframe_implies; [exact HSqrFrame|].
    intros b' pos HE HV (r & s & d & ch & HGet & HCell & HBlock & HRange).
    destruct r as [|r].
    - change (b' = ba) in HBlock. subst b'. exact (HS 0%nat ltac:(cbn; lia) HE).
    - cbn [fe_sqr_regs map nth_error] in HGet. destruct r; discriminate. }
  assert (HFIN : finv m0 bd dbase bw outedge cursor N bi mn false []).
  { eapply finv_stable; [exact HO|exact HFIN0|exact HExt]. }
  set (wrho := wide_fe_rho t0 t1 t2 t3 t4 rc).
  assert (HWI : invA m0 bd dbase bw outedge cursor N bi rc false [] 256 wrho [] mn).
  { change (Int64.repr rc = Int64.repr rc /\
      finv m0 bd dbase bw outedge cursor N bi mn false [] /\ 0 + 256 <= N /\ 0 <= 256).
    split; [reflexivity|]. split; [exact HFIN|]. split; [lia|lia]. }
  pose proof (wide_field_initial_rep t0 t1 t2 t3 t4 rc mn ba HOut HFreeA') as HRep.
  assert (HSW : xsep (extA m0 bd bw bi) [(ba,0)]).
  { intros r Hr. destruct r as [|r]; [exact (HS 0%nat ltac:(cbn; lia))|cbn in Hr; lia]. }
  destruct (eval_local_wide_write_fe m0 bd dbase bw outedge cursor N bi rc
    t0 t1 t2 t3 t4 false [] mn [(ba,0)] HO H0 H1 H2 H3 H4 HRep HSW HWI)
    as (mw & HWrite & HFinal & HFinalRep & HWriteFrame).
  rewrite HOutput in HFinal.
  change (finv m0 bd dbase bw outedge cursor N bi mw true
    (encode (@literal_fe_square Alg.CoreFunSem value))) in HFinal.
  pose proof (wide_local_final_freeable _ ba mw bd (Ptrofs.repr dbase) HFinalRep) as HFinalA.
  assert (HValidL : Mem.valid_block mr bl).
  { eapply Mem.perm_valid_block. apply (HFreeL 0). lia. }
  assert (HFreeLN : Mem.range_perm mn bl 0 16 Cur Freeable).
  { intros pos HP. apply (proj1 (proj2 HSqrFrame)); [exact HValidL| |apply HFreeL; exact HP].
    intros (r & s & d & ch & HGet & HCell & HBlock & HRange).
    destruct r as [|r].
    - change (bl = ba) in HBlock. congruence.
    - cbn [fe_sqr_regs map nth_error] in HGet. destruct r; discriminate. }
  assert (HValidLN : Mem.valid_block mn bl) by exact (proj2 (proj2 HSqrFrame) bl HValidL).
  assert (HFinalL : Mem.range_perm mw bl 0 16 Cur Freeable).
  { intros pos HP. apply (proj1 (proj2 HWriteFrame)); [exact HValidLN| |apply HFreeLN; exact HP].
    split; [exact HValidLN|]. split.
    - apply no_local_write_foot. congruence.
    - exact (HS 1%nat ltac:(cbn; lia)). }
  exists mn, mw. split; [exact HSqr|]. split; [exact HWrite|].
  split; [exact HFinal|]. split; [exact HFinalA|]. split; [exact HFinalL|].
  split; assumption.
Qed.

(** ** Statement shape *)
Definition secp_public_sqr_stmt : statement :=
  Scall None
    (Evar jets_secp._secp256k1_fe_sqr (Tfunction
      (Tcons (tptr secp_field_type) (Tcons (tptr secp_field_type) Tnil)) tvoid cc_default))
    [Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type);
     Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type)].
Definition secp_fe_sqr_rest : statement :=
  Ssequence secp_public_read_stmt
    (Ssequence secp_public_sqr_stmt
      (Ssequence secp_public_write_stmt
        (Sreturn (Some (Econst_int (Int.repr 1) tint))))).
Lemma secp_fe_sqr_body :
  fn_body f_simplicity_fe_square =
    Ssequence (Sassign (Evar jets_secp._src secp_frame_type)
      (Etempvar jets_secp._src secp_frame_type)) secp_fe_sqr_rest.
Proof. reflexivity. Qed.
Lemma secp_sqr_helper_symbols :
  Genv.find_symbol secp_ge jets_secp._secp256k1_fe_sqr =
    Some (secp_symbol_block jets_secp._secp256k1_fe_sqr) /\
  Genv.find_funct secp_ge
    (Vptr (secp_symbol_block jets_secp._secp256k1_fe_sqr) Ptrofs.zero) =
    Some (Internal f_secp256k1_fe_sqr).
Proof. vm_compute; split; reflexivity. Qed.
Lemma exec_secp_public_sqr le m mf bl ba :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (secp_public_env bl ba) le m
    secp_public_sqr_stmt E0 le mf Out_normal.
Proof.
  intro HCall; destruct secp_sqr_helper_symbols as [HS HF].
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block jets_secp._secp256k1_fe_sqr) Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero])
    (f := Internal f_secp256k1_fe_sqr) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
      * reflexivity.
      * apply eval_Enil.
  - exact HF.
  - reflexivity.
  - exact HCall.
Qed.

Theorem exec_secp_fe_sqr_rest_literal le m0 bd dbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word 8)) m ba bl :
  le!jets_secp._dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] 256
    (read_fe_rho (frame_input_word_bits value) rc) [] m ->
  exists mw,
    Clight2.exec_stmt secp_ge (secp_public_env bl ba) le m secp_fe_sqr_rest E0 le mw
      (Out_return (Some (Vint Int.one, tint))) /\
    finv m0 bd dbase bw outedge cursor N bi mw true
      (encode (@literal_fe_square Alg.CoreFunSem value)) /\
    Mem.range_perm mw ba 0 40 Cur Freeable /\ Mem.range_perm mw bl 0 16 Cur Freeable /\
    lframe (secp_locals_outside m0 bd bw bi ba bl) m mw.
Proof.
  intros HDst HOutput HInput HCursor HMax HFieldFree HFrameFree HFields HSeparate HSep HInv.
  destruct (eval_local_read_fe_canonical m0 bd dbase bw outedge cursor N bi edge rc value m ba bl
    HOutput HInput HCursor HMax HFieldFree HFrameFree HFields HSeparate HSep HInv)
    as [mr [HRead [HField [HFreeA [HFreeL [HReadInv HReadFrame]]]]]].
  destruct (eval_sqr_write_after_read_field m0 bd dbase bw outedge cursor N bi edge rc value mr ba bl
    HOutput HField HFreeA HFreeL HSeparate HSep HReadInv)
    as (mn & mw & HSqr & HWrite & HFinal & HFinalFreeA & HFinalFreeL & HSqrFrame & HWriteFrame).
  exists mw; split.
  - unfold secp_fe_sqr_rest.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := le).
    + apply exec_secp_public_read; exact HRead.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mn) (le1 := le).
      * apply exec_secp_public_sqr; exact HSqr.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mw) (le1 := le).
        -- apply exec_secp_public_write with (bd := bd) (dbase := dbase); assumption.
        -- apply exec_Sreturn_some; constructor.
  - split; [exact HFinal|]; split; [exact HFinalFreeA|]; split; [exact HFinalFreeL|].
    eapply lframe_trans.
    + eapply lframe_implies; [exact HReadFrame|].
      intros b pos [HA [HL HE]] HValid; split; [exact HValid|]; split; [|exact HE].
      apply no_local_read_foot; assumption.
    + eapply lframe_trans.
      * eapply lframe_implies; [exact HSqrFrame|].
        intros b pos [HA [HL HE]] HValid (r & s & d & ch & HGet & HCell & HBlock & HRange).
        destruct r as [|r].
        -- change (b = ba) in HBlock. contradiction.
        -- cbn [fe_sqr_regs map nth_error] in HGet. destruct r; discriminate.
      * eapply lframe_implies; [exact HWriteFrame|].
        intros b pos [HA [HL HE]] HValid; split; [exact HValid|]; split; [|exact HE].
        apply no_local_write_foot; assumption.
Qed.

(** ** Entry and whole call *)
Lemma secp_fe_square_entry v_env m ma mb bl ba bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma, bl) -> Mem.alloc ma 0 40 = (mb, ba) ->
  function_entry2 secp_ge f_simplicity_fe_square
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] m
    (secp_public_env bl ba) (secp_public_temps v_env bd dbase bs sbase) mb.
Proof.
  intros HA HB; constructor.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy; cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in Hxy; discriminate|congruence].
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma, bl)); exact HA.
    + eapply alloc_variables_cons with (m1 := mb) (b1 := ba).
      * change (Mem.alloc ma 0 40 = (mb, ba)); exact HB.
      * constructor.
  - reflexivity.
Qed.

Theorem eval_secp_fe_square_literal v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word 8)) :
  write_frame_at m0 bd dbase bw outedge cursor N -> 256 <= N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  exists mf,
    Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_fe_square)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] E0 mf (Vint Int.one) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (encode (@literal_fe_square Alg.CoreFunSem value)) /\
    lframe (fun b _ => ~ extA m0 bd bw bi b) m0 mf.
Proof.
  intros HOutput HCapacity HBase HAlign HFields HInput HCursor HMax.
  destruct (Mem.alloc m0 0 16) as [ma bl] eqn:HA.
  destruct (Mem.alloc ma 0 40) as [mb ba] eqn:HB.
  destruct (secp_prepare_public_locals v_env m0 ma bl ba mb bd dbase bs sbase bw outedge cursor N bi edge rc value
    HA HB HOutput HCapacity HBase HAlign HFields)
    as [mc [HCopy [HFreeA [HFreeL [HLocalFields [HSeparate [HSep [HInv [HPrepFrame [HFreshA HFreshL]]]]]]]]]].
  destruct (exec_secp_fe_sqr_rest_literal (secp_public_temps v_env bd dbase bs sbase)
    m0 bd dbase bw outedge cursor N bi edge rc value mc ba bl
    eq_refl HOutput HInput HCursor HMax HFreeA HFreeL HLocalFields HSeparate HSep HInv)
    as [mw [HRest [HFinal [HFinalFreeA [HFinalFreeL HRestFrame]]]]].
  destruct (secp_free_public_locals mw bl ba HSeparate HFinalFreeL HFinalFreeA)
    as [mf [HFree HFreeFrame]].
  assert (HFreeExt : eqext m0 bd bw bi mw mf).
  { eapply lframe_implies; [exact HFreeFrame|].
    intros b pos [_ HValid] _; split; intro HEqual; subst b; contradiction. }
  exists mf; split.
  - eapply eval_funcall_internal with (e := secp_public_env bl ba)
      (le1 := secp_public_temps v_env bd dbase bs sbase)
      (le2 := secp_public_temps v_env bd dbase bs sbase) (m1 := mb) (m2 := mw)
      (out := Out_return (Some (Vint Int.one, tint))).
    + eapply secp_fe_square_entry; eassumption.
    + rewrite secp_fe_sqr_body.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
        (le1 := secp_public_temps v_env bd dbase bs sbase); eassumption.
    + cbn; split; [discriminate|reflexivity].
    + exact HFree.
  - split.
    + eapply finv_stable; [exact HOutput|exact HFinal|exact HFreeExt].
    + assert (HOutside : lframe (fun b _ => Mem.valid_block m0 b /\ ~ extA m0 bd bw bi b) m0 mf).
      { eapply lframe_trans.
        - eapply lframe_implies; [exact HPrepFrame|].
          intros b pos [HValid _] _; split; intro HEqual; subst b; contradiction.
        - eapply lframe_trans.
          + eapply lframe_implies; [exact HRestFrame|].
            intros b pos [HValid HExt] _; unfold secp_locals_outside.
            split; [intro HEqual; subst b; contradiction|]; split; [intro HEqual; subst b; contradiction|exact HExt].
          + eapply lframe_implies; [exact HFreeFrame|].
            intros b pos [HValid _] _; split; intro HEqual; subst b; contradiction. }
      eapply lframe_implies; [exact HOutside|]; intros b pos HExt HValid; split; assumption.
Qed.

(** ** The standard public contract *)
Theorem fe_square_literal_local_spec :
  secp_jet_local_spec f_simplicity_fe_square (Word 8) (Word 8)
    (@literal_fe_square Alg.CoreFunSem).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HBase HAlign HSource HCursor HMax HInput HOutput.
  change (rc + 256 <= Int64.max_unsigned) in HMax.
  change (write_frame_at m bd dbase bw outedge cursor 256) in HOutput.
  rewrite encode_word in HInput.
  destruct (eval_secp_fe_square_literal env m bd dbase bs sbase bw outedge cursor 256 bi edge rc a
    HOutput ltac:(lia) HBase HAlign HSource HInput HCursor HMax)
    as (mf & HCall & HFinal & HFrame).
  destruct HFinal as (HV & HF & HN & (HCells & HPrefix & HFields & HLoads & HPerms) & Hw).
  rewrite encode_length in HFields, HLoads.
  exists mf. split; [exact HCall|]. split; [exact HCells|]. split; [exact HPrefix|].
  split; [exact HFields|].
  intros chunk bx ofs HValid HFrameOther HOutputOther.
  destruct (Pos.eq_dec bx bd) as [HD|HD];
    [apply HLoads; [split; [left; exact HD|exact HValid]|assumption|assumption]|].
  destruct (Pos.eq_dec bx bw) as [HW|HW];
    [apply HLoads; [split; [right; left; exact HW|exact HValid]|assumption|assumption]|].
  destruct (Pos.eq_dec bx bi) as [HI|HI];
    [apply HLoads; [split; [right; right; exact HI|exact HValid]|assumption|assumption]|].
  apply (proj1 HFrame); [exact HValid|]. intros pos HPos.
  unfold extA, fext; intros [[H|[H|H]] _]; contradiction.
Qed.

Print Assumptions secp_fe_square_entry.
Print Assumptions eval_secp_fe_square_literal.
Print Assumptions fe_square_literal_local_spec.
