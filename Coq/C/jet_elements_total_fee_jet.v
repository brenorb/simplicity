(** The complete original total_fee C wrapper against its stored fee table.
    This is not yet the canonical fee-sum equivalence: construction and meaning
    of the sorted table, including the reported fee-classification boundary,
    remain separate obligations. The existing memcmp model is explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets_elements C.jet_elements_linkage.
Require Import C.jet_exec.
Require Import C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_input_layout C.jet_output_layout C.jet_write_layout C.jet_encoding C.jet_constant_layout.
Require Import C.jet_word32_chunks C.jet_nonce_local_common.
Require Import C.jet_elements_support_sha_compress_call C.jet_elements_support_sha_tapdata_prep.
Require Import C.jet_memcmp_model C.jet_elements_fee_lookup_table C.jet_elements_fee_lookup_sorted.
Require Import C.jet_elements_total_fee_read C.jet_elements_total_fee_suffix C.jet_elements_effects.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition total_fee_temps envv bd dbase bs sbase :=
  PTree.set _env envv (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps (fn_temps f_simplicity_total_fee)))).

Lemma total_fee_local_blocks bl ba : blocks_of_env elements_ge (total_fee_locals bl ba)=
  [(bl,0,16);(ba,0,32)].
Proof. vm_compute;reflexivity. Qed.

Lemma total_fee_entry envv m ma m0 bl ba bd dbase bs sbase :
  Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 32=(m0,ba) ->
  function_entry2 elements_ge f_simplicity_total_fee
    [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);envv] m
    (total_fee_locals bl ba) (total_fee_temps envv bd dbase bs sbase) m0.
Proof.
  intros A1 A2;constructor.
  - cbn;repeat constructor;cbn;intuition discriminate.
  - cbn;repeat constructor;cbn;intuition discriminate.
  - intros x y HX HY Hxy;cbn in HX,HY;
      repeat destruct HX as [HX|HX];try contradiction;
      repeat destruct HY as [HY|HY];try contradiction;subst x;subst y;
      vm_compute in Hxy;discriminate.
  - eapply alloc_variables_cons with (m1:=ma) (b1:=bl).
    + change (Mem.alloc m 0 16=(ma,bl));exact A1.
    + eapply alloc_variables_cons with (m1:=m0) (b1:=ba).
      * change (Mem.alloc ma 0 32=(m0,ba));exact A2.
      * constructor.
  - reflexivity.
Qed.

Lemma exec_total_fee_copy m mc bl ba bs sbase bytes le :
  frame_base_valid sbase -> (8|sbase) -> bl<>bs ->
  le!_src=Some(Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16=Some bytes -> Mem.storebytes m bl 0 bytes=Some mc ->
  Clight2.exec_stmt elements_ge (total_fee_locals bl ba) le m
    (Sassign(Evar _src total_fee_frame)(Etempvar _src total_fee_frame)) E0 le mc Out_normal.
Proof.
  intros Base Align Separate Src Bytes Store.
  assert (Unsigned:Ptrofs.unsigned(Ptrofs.repr sbase)=sbase).
  { apply Ptrofs.unsigned_repr;unfold frame_base_valid in Base;lia. }
  eapply exec_Sassign_copy.
  - apply eval_Evar_local;reflexivity.
  - apply eval_Etempvar;exact Src.
  - reflexivity.
  - eapply assign_loc_copy with (b':=bs) (ofs':=Ptrofs.repr sbase) (bytes:=bytes).
    + reflexivity.
    + intros _;change (8|Ptrofs.unsigned(Ptrofs.repr sbase));rewrite Unsigned;exact Align.
    + intros _;change (8|0);exists 0;reflexivity.
    + left;congruence.
    + change (Mem.loadbytes m bs (Ptrofs.unsigned(Ptrofs.repr sbase)) 16=Some bytes).
      rewrite Unsigned;exact Bytes.
    + exact Store.
Qed.

Theorem eval_total_fee_stored_table (Model:memcmp_model) m be ebase bt txbase tableval entries
  bd dbase bs sbase bi bw edge outedge cursor rc (a:Ty.tySem Word256) :
  frame_base_valid sbase -> (8|sbase) -> frame_fields_at m bs sbase bi edge rc ->
  0<=rc -> rc+256<=Int64.max_unsigned -> frame_input_cells_at m bi edge rc (encode a) ->
  write_frame_at m bd dbase bw outedge cursor 64 ->
  0<=ebase -> ebase+8<=Ptrofs.max_unsigned -> 0<=txbase -> txbase+720<=Ptrofs.max_unsigned ->
  Mem.load Mptr m be ebase=Some(Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mptr m bt (txbase+16)=Some tableval ->
  Mem.load Mint64 m bt (txbase+712)=Some(Vlong(Int64.repr(Z.of_nat(length entries)))) ->
  tableval<>Vundef -> total_fee_table_storage m tableval entries -> fee_lookup_sorted entries -> exists mf,
  Clight2.eval_funcall elements_ge m (Internal f_simplicity_total_fee)
    [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);Vptr be (Ptrofs.repr ebase)] E0 mf (Vint Int.one) /\
  frame_output_cells_at mf bw outedge cursor (total_fee_cells (total_fee_input_key(word32_chunks 3 a)) entries) /\
  write_prefix_at m mf bw outedge cursor /\
  frame_fields_at mf bd dbase bw outedge (cursor-64) /\
  (forall ch b ofs,Mem.valid_block m b ->
    (b<>bd \/ ofs+size_chunk ch<=dbase+8 \/ dbase+16<=ofs) ->
    (b<>bw \/ ofs+size_chunk ch<=outedge+8*((cursor-64)/64) \/ write_word_address outedge cursor+8<=ofs) ->
    Mem.load ch mf b ofs=Mem.load ch m b ofs).
Proof.
  intros SrcBase SrcAlign [SrcEdge SrcOffset] RC RCMax Input Out
    EnvBase EnvMax TxBase TxMax EnvTx Table Count Defined Storage Sorted.
  set (hs:=word32_chunks 3 a).
  assert (Len:length hs=8%nat) by (apply (word32_chunks_length 3)).
  assert (Words:forall i x,nth_error hs i=Some x -> frame_input_word_at m bi edge (rc+32*Z.of_nat i) x).
  { apply (frame_input_word32_chunks m bi edge rc 3 a);exact Input. }
  assert (Vi:Mem.valid_block m bi).
  { eapply nonce_input_cells_valid;[|exact Input].
    intro Empty;apply (f_equal (@length Cell)) in Empty;rewrite encode_length in Empty;discriminate. }
  assert (Vs:Mem.valid_block m bs) by (eapply load_valid_block;exact SrcEdge).
  pose proof Out as [DstBase [[DstEdge DstOffset] _]].
  assert (Vd:Mem.valid_block m bd) by (eapply load_valid_block;exact DstEdge).
  destruct (write_frame_at_head m bd dbase bw outedge cursor 64 ltac:(lia) Out)
    as (_ & _ & _ & initialword & InitialWord).
  assert (Vw:Mem.valid_block m bw) by (eapply load_valid_block;exact InitialWord).
  (* The two allocations are exactly fn_vars, not a different implementation. *)
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:A1.
  destruct (Mem.alloc ma 0 32) as [m0 ba] eqn:A2.
  assert (Alloc:alloc_list m [16;32]=(m0,[bl;ba])).
  { cbn [alloc_list];rewrite A1,A2;reflexivity. }
  destruct (alloc_list_props _ _ _ _ Alloc) as ((XV & XL & XP & XA) & Fresh & ND & FA).
  inversion FA as [|? ? ? ? [Psrc Vsrc] FA1];subst.
  inversion FA1 as [|? ? ? ? [Pkey Vkey] FA2];subst;clear FA FA1 FA2.
  assert (Separate:bl<>ba).
  { apply NoDup_cons_iff in ND;destruct ND as [N _];intro Eq;subst ba;apply N;left;reflexivity. }
  assert (NotOld:forall b,Mem.valid_block m b -> b<>bl /\ b<>ba).
  { intros b Hv;pose proof (Fresh b Hv) as N;cbn [In] in N;
      split;intro Eq;apply N;[left|right;left];congruence. }
  pose proof (NotOld bi Vi) as [Nibl Niba].
  pose proof (NotOld bs Vs) as [Nsbl Nsba].
  pose proof (NotOld bd Vd) as [Ndbl Ndba].
  pose proof (NotOld bw Vw) as [Nwbl Nwba].
  set (le:=total_fee_temps (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase).
  (* The by-value source parameter is copied into its allocated local. *)
  assert (SrcEdge0:Mem.load Mptr m0 bs sbase=Some(Vptr bi (Ptrofs.repr edge)))
    by (rewrite XL by exact Vs;exact SrcEdge).
  assert (SrcOffset0:Mem.load Mint64 m0 bs (sbase+8)=Some(Vlong(Int64.repr rc)))
    by (rewrite XL by exact Vs;exact SrcOffset).
  destruct (frame_loadbytes_at m0 bs sbase _ _ SrcEdge0 SrcOffset0) as [bytes Bytes].
  pose proof (Mem.loadbytes_length _ _ _ _ _ Bytes) as BytesLen.
  assert (CopyWritable:Mem.range_perm m0 bl 0 (0+Z.of_nat(length bytes)) Cur Writable).
  { rewrite BytesLen;change (Mem.range_perm m0 bl 0 16 Cur Writable).
    intros ofs Hr;eapply Mem.perm_implies;[apply Psrc;exact Hr|constructor]. }
  destruct (Mem.range_perm_storebytes m0 bl 0 bytes CopyWritable) as [mc CopyStore].
  destruct (frame_copy_fields_at m0 mc bs sbase bl bytes _ _ Bytes CopyStore SrcEdge0 SrcOffset0)
    as [LocalEdge LocalOffset].
  assert (Kc:forall ch b ofs,Mem.valid_block m b -> Mem.load ch mc b ofs=Mem.load ch m b ofs).
  { intros ch b ofs Hv;destruct (NotOld b Hv) as [Nbl Nba].
    erewrite Mem.load_storebytes_other;[apply XL;exact Hv|exact CopyStore|left;congruence]. }
  assert (Pc:forall b ofs k p,Mem.perm m0 b ofs k p -> Mem.perm mc b ofs k p).
  { intros b ofs k p Hp;eapply Mem.perm_storebytes_1;eauto. }
  assert (Copy:Clight2.exec_stmt elements_ge (total_fee_locals bl ba) le m0
    (Sassign(Evar _src total_fee_frame)(Etempvar _src total_fee_frame)) E0 le mc Out_normal).
  { apply (exec_total_fee_copy m0 mc bl ba bs sbase bytes le);
      [exact SrcBase|exact SrcAlign|congruence|reflexivity|exact Bytes|exact CopyStore]. }
  (* readHash derives the key which the original search actually compares. *)
  destruct (exec_total_fee_read bl ba le mc bi edge rc hs Len)
    as (m1 & Read & Array & Key & SourceNext & ReadLoads & ReadPerm & ReadValid).
  { intros ofs Hr;eapply Mem.perm_implies;[apply Pc,Pkey;exact Hr|constructor]. }
  { exact Separate. }
  { congruence. }
  { congruence. }
  { exact RC. }
  { exact RCMax. }
  { split;assumption. }
  { split;[|exists 1;reflexivity].
    intros ofs Hr;change (size_chunk Mint64) with 8 in Hr.
    eapply Mem.perm_implies;[apply Pc,Psrc;lia|constructor]. }
  { intros i x At;eapply frame_input_bits_at_preserved;[|exact(Words i x At)].
    intros ofs w Load;rewrite Kc by exact Vi;exact Load. }
  assert (K1:forall ch b ofs,Mem.valid_block m b -> Mem.load ch m1 b ofs=Mem.load ch m b ofs).
  { intros ch b ofs Hv;destruct(NotOld b Hv) as [Nbl Nba].
    rewrite ReadLoads by assumption;apply Kc;exact Hv. }
  assert (P1:forall b ofs k p,Mem.perm m0 b ofs k p -> Mem.perm m1 b ofs k p).
  { intros b ofs k p Hp;apply ReadPerm,Pc,Hp. }
  assert (Stored1:total_fee_table_storage m1 tableval entries).
  { eapply total_fee_storage_preserved;[exact Storage|].
    intros ch b ofs v Load;rewrite K1;[exact Load|eapply load_valid_block;exact Load]. }
  assert (Out1:write_frame_at m1 bd dbase bw outedge cursor 64).
  { eapply write_frame_at_preserved;[| |exact Out].
    - intros ch b ofs v Eq Load;rewrite K1;[exact Load|destruct Eq;subst;assumption].
    - intros b ofs k p Hp;apply P1,XP,Hp. }
  destruct (exec_total_fee_after_read Model bl ba le m1 be ebase bt txbase tableval
    (total_fee_input_key hs) entries bd dbase bw outedge cursor)
    as (m2 & Suffix & Cells & Prefix & Fields & Outside & Perm & Valid).
  { reflexivity. }
  { reflexivity. }
  { exact EnvBase. }
  { exact EnvMax. }
  { exact TxBase. }
  { exact TxMax. }
  { rewrite K1;[exact EnvTx|eapply load_valid_block;exact EnvTx]. }
  { rewrite K1;[exact Table|eapply load_valid_block;exact Table]. }
  { rewrite K1;[exact Count|eapply load_valid_block;exact Count]. }
  { exact Defined. }
  { apply total_fee_lookup_storage;assumption. }
  { exact Sorted. }
  { exact Out1. }
  (* All callees preserve ownership of both locals; the function frees both. *)
  destruct (free_list_blocks [(bl,0,16);(ba,0,32)] m2) as (mf & Free & FreeLoads & _ & _).
  { intros b lo hi At ofs Hr;apply Perm,P1.
    cbn [In] in At;destruct At as [Eq|[Eq|[]]];injection Eq as <- <- <-;
      [apply Psrc|apply Pkey];exact Hr. }
  { cbn [map fst];exact ND. }
  cbn [map fst] in FreeLoads.
  exists mf;split;[|split;[|split;[|split]]].
  - eapply eval_funcall_internal with (e:=total_fee_locals bl ba) (le1:=le) (m1:=m0)
      (le2:=total_fee_ready bt txbase tableval (Z.of_nat(length entries))
        (fee_lookup_value(total_fee_input_key hs)entries) le) (m2:=m2)
      (out:=Out_return(Some(Vint Int.one,tint))).
    + eapply total_fee_entry;eassumption.
    + rewrite total_fee_body_source.
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mc);[exact Copy|].
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m1);[exact Read|exact Suffix].
    + cbn;split;[discriminate|reflexivity].
    + rewrite total_fee_local_blocks;exact Free.
  - eapply frame_output_cells_preserved;[|exact Cells].
    intros ofs w Load;rewrite FreeLoads by (apply Fresh;exact Vw);exact Load.
  - eapply write_prefix_at_preserved;[| |exact Prefix].
    + intros ofs w Load;rewrite K1 by exact Vw;exact Load.
    + intros ofs w Load;rewrite FreeLoads by (apply Fresh;exact Vw);exact Load.
  - destruct Fields as [FinalEdge FinalOffset];split;
      rewrite FreeLoads by (apply Fresh;exact Vd);assumption.
  - intros ch b ofs Hv Hd Hw;rewrite FreeLoads by (apply Fresh;exact Hv).
    rewrite Outside by assumption;apply K1;exact Hv.
Qed.
