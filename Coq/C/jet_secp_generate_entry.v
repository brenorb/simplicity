(** Actual public generate entry, private source-frame copy and ownership.
    Reuse the shared allocation and frame-copy lemmas, with the original
    three local types and sizes. No initialized state is assumed afterward. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight Clightdefs ClightBigstep
  Integers Maps Memory Values Events.
Require Import C.jet_exec C.jet_sx_mem C.jet_sx_exec C.jet_sx_expr C.jet_sx_state
  C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout C.jet_output_layout
  C.jet_frame_inv C.jet_secp_frame C.jet_secp_linkage C.jets_secp
  C.jet_secp_public_copy C.jet_secp_owned_public_lifecycle C.jet_secp_local_regions
  C.jet_secp_generator_startup C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition generate_public_env (bl bp bn : block) :=
  PTree.set _ng__2 (bn,Tstruct __5826 noattr)
    (PTree.set _r (bp,Tstruct __6123 noattr)
      (PTree.set _src (bl,Tstruct _frameItem noattr) empty_env)).
Definition generate_copy := Sassign (Evar _src (Tstruct _frameItem noattr))
  (Etempvar _src (Tstruct _frameItem noattr)).

Lemma generate_public_entry envv m ma mb mc bl bp bn bd base bs sbase :
  Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 128=(mb,bp) -> Mem.alloc mb 0 32=(mc,bn) ->
  function_entry2 secp_ge f_simplicity_generate
    [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);envv] m
    (generate_public_env bl bp bn) (secp_public_temps envv bd base bs sbase) mc.
Proof.
  intros A B C;destruct (fn_okb_true f_simplicity_generate eq_refl) as (Vars & Params & Disjoint).
  constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
  eapply alloc_variables_cons with (m1:=ma) (b1:=bl);[exact A|].
  eapply alloc_variables_cons with (m1:=mb) (b1:=bp);[exact B|].
  eapply alloc_variables_cons with (m1:=mc) (b1:=bn);[exact C|constructor].
Qed.
Lemma generate_public_blocks bl bp bn : blocks_of_env secp_ge (generate_public_env bl bp bn)=
  [(bl,0,16);(bp,0,128);(bn,0,32)].
Proof. reflexivity. Qed.

Theorem generate_prepare envv m0 bd base bs sbase bw edge cursor N bi inedge rc :
  generator_startup m0 -> write_frame_at m0 bd base bw edge cursor N ->
  frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi inedge rc ->
  exists bl bp bn mc md,
    function_entry2 secp_ge f_simplicity_generate
      [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);envv] m0
      (generate_public_env bl bp bn) (secp_public_temps envv bd base bs sbase) mc /\
    Clight2.exec_stmt secp_ge (generate_public_env bl bp bn) (secp_public_temps envv bd base bs sbase)
      mc generate_copy E0 (secp_public_temps envv bd base bs sbase) md Out_normal /\
    Mem.range_perm md bl 0 16 Cur Freeable /\ Mem.range_perm md bp 0 128 Cur Freeable /\
    Mem.range_perm md bn 0 32 Cur Freeable /\ frame_fields_at md bl 0 bi inedge rc /\
    bp<>bl /\ bn<>bl /\ bp<>bn /\
    (forall b,Mem.valid_block m0 b -> b<>bp /\ b<>bn /\ b<>bl) /\
    xsep (extA m0 bd bw bi) [(bp,0);(bn,0);(bl,0)] /\
    finv m0 bd base bw edge cursor N bi md false [] /\ generator_startup md /\
    lframe (fun b _=>b<>bp /\ b<>bn /\ b<>bl) m0 md.
Proof.
  intros Ready Output Base Align Source.
  destruct (Mem.alloc m0 0 16) as [ma bl] eqn:AL.
  destruct (Mem.alloc ma 0 128) as [mb bp] eqn:AP.
  destruct (Mem.alloc mb 0 32) as [mc bn] eqn:AN.
  destruct (owned_public_alloc_fresh 128 m0 ma bl bp mb AL AP) as (NewL & NewP & PL).
  destruct (owned_public_alloc_freeable 128 m0 ma bl bp mb AL AP) as (FL & FP).
  assert (VL:Mem.valid_block mb bl) by (eapply Mem.perm_valid_block;exact (FL 0 ltac:(clear;lia))).
  assert (VP:Mem.valid_block mb bp) by (eapply Mem.perm_valid_block;exact (FP 0 ltac:(clear;lia))).
  assert (NL:bn<>bl) by (intro E;apply (Mem.fresh_block_alloc _ _ _ _ _ AN);rewrite E;exact VL).
  assert (PN:bp<>bn) by (intro E;apply (Mem.fresh_block_alloc _ _ _ _ _ AN);rewrite <-E;exact VP).
  assert (NewN:~Mem.valid_block m0 bn).
  { intro V;apply (Mem.fresh_block_alloc _ _ _ _ _ AN);eapply Mem.valid_block_alloc;
      [exact AP|];eapply Mem.valid_block_alloc;[exact AL|exact V]. }
  assert (Old:forall b,Mem.valid_block m0 b -> b<>bp /\ b<>bn /\ b<>bl).
  { intros b V;repeat split;intro E;subst b;contradiction. }
  assert (Allocated:lframe (fun _ _=>True) m0 mc).
  { eapply lframe_trans;[eapply owned_public_alloc_lframe;eassumption|].
    apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact AN. }
  assert (Src:frame_fields_at mc bs sbase bi inedge rc).
  { destruct Source as [Edge Cursor];pose proof (load_valid m0 Mptr bs sbase _ Edge) as Valid;
      split;rewrite (proj1 Allocated) by auto;assumption. }
  destruct Src as [Edge Cursor].
  destruct (frame_loadbytes_at mc bs sbase _ _ Edge Cursor) as (bytes & Load).
  pose proof (Mem.loadbytes_length _ _ _ _ _ Load) as Length.
  assert (FreeL:Mem.range_perm mc bl 0 16 Cur Freeable).
  { intros pos Range;eapply Mem.perm_alloc_1;[exact AN|apply FL;exact Range]. }
  assert (Writable:Mem.range_perm mc bl 0 (0+Z.of_nat (length bytes)) Cur Writable).
  { rewrite Length;apply freeable_range_writable;exact FreeL. }
  destruct (Mem.range_perm_storebytes mc bl 0 bytes Writable) as (md & Store).
  assert (Frame:lframe (fun b _=>b<>bp /\ b<>bn /\ b<>bl) m0 md).
  { eapply lframe_trans;[eapply lframe_implies;[exact Allocated|intros;exact I]|].
    apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|].
    intros pos Range (_ & _ & Other);apply Other;reflexivity. }
  assert (Ext:eqext m0 bd bw bi m0 md).
  { eapply lframe_implies;[exact Frame|];intros b pos [_ V] _;apply Old;exact V. }
  assert (U:Ptrofs.unsigned (Ptrofs.repr sbase)=sbase)
    by (apply Ptrofs.unsigned_repr;unfold frame_base_valid in Base;lia).
  exists bl,bp,bn,mc,md;split;[eapply generate_public_entry;eassumption|];split.
  - unfold generate_copy;eapply exec_Sassign_copy.
    + apply eval_Evar_local;reflexivity.
    + apply eval_Etempvar;unfold secp_public_temps;rewrite PTree.gso by discriminate;apply PTree.gss.
    + reflexivity.
    + eapply assign_loc_copy with (b':=bs) (ofs':=Ptrofs.repr sbase) (bytes:=bytes).
      * reflexivity.
      * intros _;change (8|Ptrofs.unsigned (Ptrofs.repr sbase));rewrite U;exact Align.
      * intros _;change (8|0);exists 0;reflexivity.
      * left;intro E;apply NewL;subst bs;exact (load_valid m0 Mptr bl sbase _ (proj1 Source)).
      * change (Mem.loadbytes mc bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16=Some bytes);rewrite U;exact Load.
      * exact Store.
  - split.
    { intros pos Range;eapply Mem.perm_storebytes_1;[exact Store|apply FreeL;exact Range]. }
    split.
    { intros pos Range;eapply Mem.perm_storebytes_1;[exact Store|];
        eapply Mem.perm_alloc_1;[exact AN|apply FP;exact Range]. }
    split.
    { intros pos Range;eapply Mem.perm_storebytes_1;[exact Store|];eapply Mem.perm_alloc_2;[exact AN|exact Range]. }
    split;[exact (frame_copy_fields_at mc md bs sbase bl bytes _ _ Load Store Edge Cursor)|].
    split;[exact PL|];split;[exact NL|];split;[exact PN|];split;[exact Old|];split.
    { intros [|[|[|r]]] Index;cbn [blk bas lay nth fst snd];unfold extA,fext;
        [intros [_ V];contradiction|intros [_ V];contradiction|intros [_ V];contradiction|cbn in Index;lia]. }
    split;[eapply finv_stable;[exact Output|apply finv_init;exact Output|exact Ext]|];split;[|exact Frame].
    apply (generator_startup_readonly m0 md Ready).
    eapply preserved_trans;[eapply alloc_preserved;exact AL|].
    eapply preserved_trans;[eapply alloc_preserved;exact AP|].
    eapply preserved_trans;[eapply alloc_preserved;exact AN|eapply storebytes_preserved;exact Store].
Qed.
