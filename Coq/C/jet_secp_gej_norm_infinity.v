(** Complete original public gej_normalize call on its infinity branch.
    This restricted branch result is not registered as a complete jet proof. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.BitMachine.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.jet_exec C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv C.jet_encoding.
Require Import C.jet_word_repr C.jet_write_layout.
Require Import C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_curve_frame C.jet_secp_public_body.
Require Import C.jet_secp_wrapper_run C.jet_secp_canonical_zero C.jet_secp_read_gej_owned.
Require Import C.jet_secp_gej_predicate_body C.jet_secp_gej_norm_branch.
Require C.jet_elements_support_sha_tapdata_prep.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_fe_is_zero literal_gej_normalize Simplicity.Translate.encode.

Definition gej_norm_temps envv bd base bs sbase := PTree.set _env envv
  (PTree.set _src (Vptr bs (Ptrofs.repr sbase)) (PTree.set _dst (Vptr bd (Ptrofs.repr base))
    (create_undef_temps(fn_temps f_simplicity_gej_normalize)))).
Lemma gej_norm_fn_ok : fn_okb f_simplicity_gej_normalize=true.
Proof. reflexivity. Qed.
Lemma gej_norm_entry envv m ma mb mc bl bp br bd base bs sbase :
  Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 128=(mb,bp) -> Mem.alloc mb 0 88=(mc,br) ->
  function_entry2 secp_ge f_simplicity_gej_normalize
    [Vptr bd(Ptrofs.repr base);Vptr bs(Ptrofs.repr sbase);envv] m
    (gej_norm_env bl bp br) (gej_norm_temps envv bd base bs sbase) mc.
Proof.
  intros A1 A2 A3;destruct(fn_okb_true _ gej_norm_fn_ok) as (N1 & N2 & Disjoint).
  constructor;[exact N1|exact N2|exact Disjoint| |reflexivity].
  eapply alloc_variables_cons with (m1:=ma) (b1:=bl);[exact A1|].
  eapply alloc_variables_cons with (m1:=mb) (b1:=bp);[exact A2|].
  eapply alloc_variables_cons with (m1:=mc) (b1:=br);[exact A3|constructor].
Qed.

Lemma gej_norm_blocks bl bp br : blocks_of_env secp_ge (gej_norm_env bl bp br)=
  [(bl,0,16);(bp,0,128);(br,0,88)].
Proof. reflexivity. Qed.

Lemma exec_gej_norm_read le m mf bl bp br :
  Clight2.eval_funcall secp_ge m (Internal f_read_gej)
    [Vptr bp Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (gej_norm_env bl bp br) le m gej_predicate_read_stmt E0 le mf Out_normal.
Proof.
  intro Call;destruct gej_predicate_reader_symbol as (bf & Symbol & Funct).
  unfold gej_predicate_read_stmt;eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
    (f:=Internal f_read_gej) (vargs:=[Vptr bp Ptrofs.zero;Vptr bl Ptrofs.zero]) (vres:=Vundef).
  - reflexivity.
  - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact Symbol]|apply deref_loc_reference;reflexivity].
  - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
    eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
  - exact Funct.
  - reflexivity.
  - exact Call.
Qed.

Theorem eval_gej_normalize_infinity_public envv m0 bd base bs sbase bw edge cursor N bi inedge rc
    (x y z:Ty.tySem Word256) :
  write_frame_at m0 bd base bw edge cursor N -> 513<=N ->
  frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi inedge rc ->
  frame_input_cells_at m0 bi inedge rc (map Some(frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi inedge (rc+256) (map Some(frame_input_word_bits y)) ->
  frame_input_cells_at m0 bi inedge (rc+512) (map Some(frame_input_word_bits z)) ->
  0<=rc -> rc+768<=Int64.max_unsigned ->
  Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z)=true -> exists mf,
  Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_gej_normalize)
    [Vptr bd(Ptrofs.repr base);Vptr bs(Ptrofs.repr sbase);envv] E0 mf (Vint Int.one) /\
  finv m0 bd base bw edge cursor N bi mf true
    (Simplicity.Translate.encode(@literal_gej_normalize Alg.CoreFunSem ((x,y),z))) /\
  lframe (fun b _=>~extA m0 bd bw bi b) m0 mf.
Proof.
  intros Output Cap SrcBase SrcAlign [SrcEdge SrcOffset] InputX InputY InputZ RC RCMax Zero.
  destruct (Mem.alloc m0 0 16) as [ma bl] eqn:A1.
  destruct (Mem.alloc ma 0 128) as [mb bp] eqn:A2.
  destruct (Mem.alloc mb 0 88) as [mc br] eqn:A3.
  assert (Alloc:C.jet_elements_support_sha_tapdata_prep.alloc_list m0 [16;128;88]=(mc,[bl;bp;br])).
  { cbn [C.jet_elements_support_sha_tapdata_prep.alloc_list];rewrite A1,A2,A3;reflexivity. }
  destruct (C.jet_elements_support_sha_tapdata_prep.alloc_list_props _ _ _ _ Alloc)
    as ((XV & XL & XP & XA) & Fresh & ND & FA).
  inversion FA as [|? ? ? ? [FL VL] FA1];subst.
  inversion FA1 as [|? ? ? ? [FP VP] FA2];subst.
  inversion FA2 as [|? ? ? ? [FR VR] FA3];subst;clear FA FA1 FA2 FA3.
  assert (Distinct:bp<>bl /\ br<>bl /\ br<>bp).
  { pose proof ND as ND0;apply NoDup_cons_iff in ND0;destruct ND0 as [NL ND0].
    apply NoDup_cons_iff in ND0;destruct ND0 as [NP _].
    split;[intro E;apply NL;left;congruence|];split.
    - intro E;apply NL;right;left;congruence.
    - intro E;apply NP;left;congruence. }
  destruct Distinct as (PL & RL & RP).
  assert (Old:forall b,Mem.valid_block m0 b -> b<>bl /\ b<>bp /\ b<>br).
  { intros b V;pose proof(Fresh b V) as F;cbn [In] in F;split;[|split];intro E;apply F;
      [left|right;left|right;right;left];congruence. }
  assert (SrcValid:Mem.valid_block m0 bs) by (eapply load_valid;exact SrcEdge).
  assert (EdgeC:Mem.load Mptr mc bs sbase=Some(Vptr bi(Ptrofs.repr inedge)))
    by (rewrite XL by exact SrcValid;exact SrcEdge).
  assert (OffsetC:Mem.load Mint64 mc bs(sbase+8)=Some(Vlong(Int64.repr rc)))
    by (rewrite XL by exact SrcValid;exact SrcOffset).
  destruct (frame_loadbytes_at mc bs sbase _ _ EdgeC OffsetC) as (bytes & Bytes).
  pose proof(Mem.loadbytes_length _ _ _ _ _ Bytes) as BytesLen.
  assert (Writable:Mem.range_perm mc bl 0 (0+Z.of_nat(length bytes)) Cur Writable).
  { rewrite BytesLen;change(Mem.range_perm mc bl 0 16 Cur Writable).
    intros pos Hr;eapply Mem.perm_implies;[apply FL;exact Hr|constructor]. }
  destruct (Mem.range_perm_storebytes mc bl 0 bytes Writable) as (md & Store).
  pose proof (frame_copy_fields_at mc md bs sbase bl bytes _ _ Bytes Store EdgeC OffsetC) as LocalFields.
  assert (PrepFrame:lframe (fun b _=>b<>bl /\ b<>bp /\ b<>br) m0 md).
  { eapply lframe_trans.
    - eapply lframe_trans;[apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact A1|].
      eapply lframe_trans;apply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption.
    - apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|].
      intros pos Hr [NL _];apply NL;reflexivity. }
  assert (PrepExt:eqext m0 bd bw bi m0 md).
  { eapply lframe_implies;[exact PrepFrame|];intros b pos [_ V] _;apply Old;exact V. }
  assert (Fin:finv m0 bd base bw edge cursor N bi md false []).
  { eapply finv_stable;[exact Output|apply finv_init;exact Output|exact PrepExt]. }
  assert (FLD:Mem.range_perm md bl 0 16 Cur Freeable).
  { intros pos Hr;eapply Mem.perm_storebytes_1;[exact Store|apply FL;exact Hr]. }
  assert (FPD:Mem.range_perm md bp 0 128 Cur Freeable).
  { intros pos Hr;eapply Mem.perm_storebytes_1;[exact Store|apply FP;exact Hr]. }
  assert (FRD:Mem.range_perm md br 0 88 Cur Freeable).
  { intros pos Hr;eapply Mem.perm_storebytes_1;[exact Store|apply FR;exact Hr]. }
  assert (Sep:xsep (extA m0 bd bw bi) [(bp,0);(bl,0)]).
  { intros [|[|r]] Bound;cbn [blk bas lay nth fst snd];unfold extA,fext;
      [intros [_ V];apply(Fresh bp V);right;left;reflexivity|
       intros [_ V];apply(Fresh bl V);left;reflexivity|cbn in Bound;lia]. }
  assert (Inv:invA m0 bd base bw edge cursor N bi rc false [] 513
    (read_fe_rho(frame_input_word_bits x)rc) [] md).
  { split;[reflexivity|];split;[exact Fin|];split;[exact Cap|cbn;lia]. }
  destruct (eval_read_gej_canonical_owned m0 bd base bw edge cursor N 513 bi inedge rc
    x y z md bp bl Output InputX InputY InputZ RC RCMax FPD FLD LocalFields PL Sep Inv)
    as (mr & Read & Flag & SourceR & FPR & FLR & InvR & ReadFrame).
  rewrite Zero in Flag;change(Mem.load Mint32 mr bp 120=Some(Vint Int.one)) in Flag.
  destruct InvR as [_ [FinR _]].
  change(finv m0 bd base bw edge cursor N bi mr false []) in FinR.
  assert (NotR:~extA m0 bd bw bi br).
  { intros [_ V];apply(Fresh br V);right;right;left;reflexivity. }
  assert (FRR:Mem.range_perm mr br 0 88 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FRD|exact ReadFrame|];intros pos;split;[exact RP|];split;assumption. }
  set (le:=gej_norm_temps envv bd base bs sbase).
  destruct (exec_gej_norm_infinity_after_read m0 bd base bw edge cursor N bi le mr bl bp br
    ltac:(reflexivity) Output Cap FinR Flag) as (mw & Tail & Final & TailFrame).
  assert (Vd:Mem.valid_block m0 bd) by (exact(proj2(fext_bd m0 bd base bw edge cursor N bi Output))).
  assert (Vw:Mem.valid_block m0 bw) by (eapply bw_valid;[exact Output|lia]).
  destruct(Old bd Vd) as (DL & DP & DR);destruct(Old bw Vw) as (WL & WP & WR).
  assert (FLW:Mem.range_perm mw bl 0 16 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FLR|exact TailFrame|];intros;split;congruence. }
  assert (FPW:Mem.range_perm mw bp 0 128 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FPR|exact TailFrame|];intros;split;congruence. }
  assert (FRW:Mem.range_perm mw br 0 88 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FRR|exact TailFrame|];intros;split;congruence. }
  destruct (free_list_exists [(bl,0,16);(bp,0,128);(br,0,88)] mw) as (mf & Free & FreeUnchanged).
  { cbn;repeat constructor;cbn;intuition congruence. }
  { intros b lo hi [E|[E|[E|[]]]];injection E as <- <- <-;assumption. }
  assert (FreeFrame:lframe (fun b _=>b<>bl /\ b<>bp /\ b<>br) mw mf).
  { eapply lframe_implies;[apply lframe_unchanged;exact FreeUnchanged|].
    intros b pos (NL & NP & NR) Valid;cbn;intuition congruence. }
  assert (FreeExt:eqext m0 bd bw bi mw mf).
  { eapply lframe_implies;[exact FreeFrame|];intros b pos [_ V] _;apply Old;exact V. }
  assert (Copy:Clight2.exec_stmt secp_ge (gej_norm_env bl bp br) le mc
    (Sassign(Evar _src (Tstruct _frameItem noattr))(Etempvar _src (Tstruct _frameItem noattr))) E0 le md Out_normal).
  { assert (Unsigned:Ptrofs.unsigned(Ptrofs.repr sbase)=sbase)
      by (apply Ptrofs.unsigned_repr;unfold frame_base_valid in SrcBase;lia).
    eapply exec_Sassign_copy.
    - apply eval_Evar_local;reflexivity.
    - apply eval_Etempvar;reflexivity.
    - reflexivity.
    - eapply assign_loc_copy with (b':=bs) (ofs':=Ptrofs.repr sbase) (bytes:=bytes).
      + reflexivity.
      + intros _;change(8|Ptrofs.unsigned(Ptrofs.repr sbase));rewrite Unsigned;exact SrcAlign.
      + intros _;exists 0;reflexivity.
      + left;destruct(Old bs SrcValid) as [NS _];congruence.
      + change(Mem.loadbytes mc bs(Ptrofs.unsigned(Ptrofs.repr sbase))16=Some bytes);rewrite Unsigned;exact Bytes.
      + exact Store. }
  exists mf;split.
  - eapply eval_funcall_internal with (e:=gej_norm_env bl bp br) (le1:=le) (m1:=mc)
      (le2:=gej_norm_tagged le true) (m2:=mw) (out:=Out_return(Some(Vint Int.one,tint))).
    + eapply gej_norm_entry;eassumption.
    + rewrite gej_norm_body_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=le);[exact Copy|].
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le);[apply exec_gej_norm_read;exact Read|exact Tail].
    + cbn;split;[discriminate|reflexivity].
    + rewrite gej_norm_blocks;exact Free.
  - split.
    + rewrite literal_gej_normalize_value,Zero.
      change(finv m0 bd base bw edge cursor N bi mf true ([Some false]++repeat None 512)).
      eapply finv_stable;[exact Output|exact Final|exact FreeExt].
    + assert (Outside:lframe (fun b _=>Mem.valid_block m0 b /\ ~extA m0 bd bw bi b) m0 mf).
      { eapply lframe_trans.
        - eapply lframe_implies;[exact PrepFrame|];intros b pos [V _] _;apply Old;exact V.
        - eapply lframe_trans.
          + eapply lframe_implies;[exact ReadFrame|];intros b pos [V NE] _.
            destruct(Old b V) as (NL & NP & NR);split;[exact NP|];split;assumption.
          + eapply lframe_trans.
            * eapply lframe_implies;[exact TailFrame|];intros b pos [V NE] _;split;
                intro E;subst b;apply NE;split;[left;reflexivity|exact V|right;left;reflexivity|exact V].
            * eapply lframe_implies;[exact FreeFrame|];intros b pos [V _] _;apply Old;exact V. }
      eapply lframe_implies;[exact Outside|];intros b pos NE V;split;assumption.
Qed.

(** The same branch in the ordinary public frame/output contract. The explicit
    infinity premise is retained, so this is not an all-input jet registration. *)
Theorem gej_normalize_infinity_literal_local_spec envv m0 bd base bs sbase bw edge cursor bi inedge rc
    (x y z:Ty.tySem Word256) :
  frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi inedge rc ->
  0<=rc -> rc+768<=Int64.max_unsigned ->
  frame_input_cells_at m0 bi inedge rc
    (@Simplicity.Translate.encode (Ty.Prod(Ty.Prod Word256 Word256)Word256) ((x,y),z)) ->
  write_frame_at m0 bd base bw edge cursor 513 ->
  Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z)=true -> exists mf,
  Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_gej_normalize)
    [Vptr bd(Ptrofs.repr base);Vptr bs(Ptrofs.repr sbase);envv] E0 mf (Vint Int.one) /\
  frame_output_cells_at mf bw edge cursor
    (Simplicity.Translate.encode(@literal_gej_normalize Alg.CoreFunSem ((x,y),z))) /\
  write_prefix_at m0 mf bw edge cursor /\ frame_fields_at mf bd base bw edge (cursor-513) /\
  (forall ch b ofs,Mem.valid_block m0 b ->
    (b<>bd \/ ofs+size_chunk ch<=base+8 \/ base+16<=ofs) ->
    (b<>bw \/ ofs+size_chunk ch<=edge+8*((cursor-513)/64) \/ write_word_address edge cursor+8<=ofs) ->
    Mem.load ch mf b ofs=Mem.load ch m0 b ofs).
Proof.
  intros Base Align Source RC Max Input Output Zero.
  change(frame_input_cells_at m0 bi inedge rc
    ((Simplicity.Translate.encode x++Simplicity.Translate.encode y)++Simplicity.Translate.encode z)) in Input.
  rewrite !frame_input_cells_at_app,!app_length,!encode_word_length in Input.
  destruct Input as [[IX IY] IZ].
  change(frame_input_cells_at m0 bi inedge (rc+256)(Simplicity.Translate.encode y)) in IY.
  change(frame_input_cells_at m0 bi inedge (rc+512)(Simplicity.Translate.encode z)) in IZ.
  rewrite encode_word in IX,IY,IZ.
  destruct(eval_gej_normalize_infinity_public envv m0 bd base bs sbase bw edge cursor 513 bi inedge rc
    x y z Output ltac:(lia) Base Align Source IX IY IZ RC Max Zero)
    as (mf & Call & Inv & Frame).
  destruct Inv as (Valid & OutFrame & Capacity & (Cells & Prefix & Fields & Loads & Perms) & Written).
  rewrite Simplicity.Translate.encode_length in Fields,Loads.
  exists mf;split;[exact Call|];split;[exact Cells|];split;[exact Prefix|];split;[exact Fields|].
  intros ch b ofs V Hd Hw.
  destruct(Pos.eq_dec b bd) as [D|D];
    [apply Loads;[split;[left;exact D|exact V]|exact Hd|exact Hw]|].
  destruct(Pos.eq_dec b bw) as [W|W];
    [apply Loads;[split;[right;left;exact W|exact V]|exact Hd|exact Hw]|].
  destruct(Pos.eq_dec b bi) as [I|I];
    [apply Loads;[split;[right;right;exact I|exact V]|exact Hd|exact Hw]|].
  apply(proj1 Frame);[exact V|];intros pos Hp;unfold extA,fext;intros [[E|[E|E]] _];contradiction.
Qed.
