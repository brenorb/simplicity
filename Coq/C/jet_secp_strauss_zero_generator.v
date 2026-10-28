(** Original readonly zero generator scalar and its actual Strauss branch. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Integers Memory Values Globalenvs Events Maps.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_beta_global.
Require Import C.jet_clight_readonly_frame C.jet_secp_generator_zero_scalar.
Require Import C.jet_secp_scalar_get_b32_storage.
Import ListNotations Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition strauss_zero_block : block := secp_symbol_block _ng.
Definition strauss_zero_global_state m :=
 scalar_at m strauss_zero_block 0 [Int64.zero;Int64.zero;Int64.zero;Int64.zero] /\
 readonly_region_bounds m strauss_zero_block 0 32.

Lemma strauss_zero_symbol : Genv.find_symbol (genv_genv secp_ge) _ng=Some strauss_zero_block.
Proof. vm_compute;reflexivity. Qed.
Lemma strauss_zero_info : Genv.find_var_info (genv_genv secp_ge) strauss_zero_block=Some v_ng.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge strauss_zero_block.

Theorem strauss_zero_global_initializes m : Genv.init_mem jets_secp.prog=Some m ->
 strauss_zero_global_state m.
Proof.
 intro Init;pose proof strauss_zero_info as Info;rewrite beta_genv_projection in Info.
 destruct (Genv.init_mem_characterization jets_secp.prog _ Info Init) as (Range & Bounds & Loads & Bytes).
 change (Mem.range_perm m strauss_zero_block 0 32 Cur Readable) in Range.
 specialize (Loads eq_refl).
 change (Mem.load Mint64 m strauss_zero_block 0=Some (Vlong Int64.zero) /\
  Mem.load Mint64 m strauss_zero_block 8=Some (Vlong Int64.zero) /\
  Mem.load Mint64 m strauss_zero_block 16=Some (Vlong Int64.zero) /\
  Mem.load Mint64 m strauss_zero_block 24=Some (Vlong Int64.zero) /\ True) in Loads.
 split.
 - unfold scalar_at;split;[reflexivity|];split;[lia|];split;[exists 0;reflexivity|];split.
   + change (0+32<=18446744073709551615);lia.
   + split;[exact Range|].
     intros i w Nth;destruct i as [|[|[|[|i]]]];cbn [nth_error] in Nth;
      try (destruct i;discriminate Nth);injection Nth as <-;cbn [Z.of_nat Z.mul Z.add];tauto.
 - intros ofs k p;split.
   + intro Perm;exact (Bounds ofs k p Perm).
   + intros (Pos & Order);eapply Mem.perm_implies;[|exact Order].
     destruct k;[apply Mem.perm_cur_max|];apply Range;exact Pos.
Qed.

Lemma strauss_zero_global_valid m : strauss_zero_global_state m ->
 Mem.valid_block m strauss_zero_block.
Proof.
 intros ((Length & Base & Align & Hi & Readable & Loads) & Bounds).
 eapply Mem.perm_valid_block;apply (Readable 0);lia.
Qed.

Lemma strauss_zero_global_separate m b : strauss_zero_global_state m ->
 Mem.perm m b 0 Cur Freeable -> b<>strauss_zero_block.
Proof.
 intros (_ & Bounds) Free ->.
 destruct (proj1 (Bounds 0 Cur Freeable) Free) as (_ & Order);inversion Order.
Qed.

Lemma strauss_zero_global_unchanged m mf : strauss_zero_global_state m ->
 Mem.unchanged_on (fun b _=>b=strauss_zero_block) m mf -> strauss_zero_global_state mf.
Proof.
 intros State Unchanged;pose proof (strauss_zero_global_valid m State) as Valid.
 destruct State as ((Length & Base & Align & Hi & Readable & Loads) & Bounds).
 split.
 - unfold scalar_at;split;[exact Length|];split;[exact Base|];split;[exact Align|];split;[exact Hi|];split.
   + intros pos Range;eapply Mem.perm_unchanged_on;[exact Unchanged|reflexivity|apply Readable;exact Range].
   + intros i w Nth;eapply Mem.load_unchanged_on;
      [exact Unchanged|intros;reflexivity|exact (Loads i w Nth)].
 - intros ofs k p;split.
   + intro Perm;apply (proj1 (Bounds ofs k p)).
     eapply Mem.perm_unchanged_on_2;[exact Unchanged|reflexivity|exact Valid|exact Perm].
   + intro Pos; eapply Mem.perm_unchanged_on;
      [exact Unchanged|reflexivity|apply (proj2 (Bounds ofs k p));exact Pos].
Qed.

Lemma strauss_zero_global_alloc m mf lo hi b : strauss_zero_global_state m ->
 Mem.alloc m lo hi=(mf,b) -> strauss_zero_global_state mf /\ b<>strauss_zero_block.
Proof.
 intros State Alloc;pose proof (strauss_zero_global_valid m State) as Valid.
 split.
 - eapply strauss_zero_global_unchanged;[exact State|].
   eapply Mem.unchanged_on_implies;[eapply Mem.alloc_unchanged_on;exact Alloc|].
   intros block ofs At Old;exact Old.
 - intro E;subst b;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Valid).
Qed.

Lemma eval_strauss_zero_address e le m : e!_ng=None ->
 eval_expr secp_ge e le m (Eaddrof (Evar _ng (Tstruct __5826 noattr))
  (tptr (Tstruct __5826 noattr))) (Vptr strauss_zero_block Ptrofs.zero).
Proof.
 intro Local;apply eval_Eaddrof;apply eval_Evar_global;[exact Local|exact strauss_zero_symbol].
Qed.


Theorem strauss_zero_initialized_memory_exists :
 exists m,Genv.init_mem jets_secp.prog=Some m /\ strauss_zero_global_state m.
Proof.
 destruct beta_initialized_memory_exists as (m & Init & Beta).
 exists m;split;[exact Init|apply strauss_zero_global_initializes;exact Init].
Qed.

Require Import C.jet_sx_mem C.jet_memset_model C.jet_secp_scalar_get_b32_numeric C.jet_secp_strauss_generator_zero C.jet_secp_generator_split_call
 C.jet_secp_scalar_split128_literal C.jet_secp_canonical_scalar C.jet_toZ
 C.jet_clight_readonly C.jet_secp_scalar_add_reader_support.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.

Lemma strauss_zero_global_lframe m mf P :
 strauss_zero_global_state m -> lframe P m mf ->
 (forall pos,P strauss_zero_block pos) ->
 (forall pos k p,Mem.perm mf strauss_zero_block pos k p <-> Mem.perm m strauss_zero_block pos k p) ->
 strauss_zero_global_state mf.
Proof.
 intros [Storage Bounds] Frame Outside Perms;split.
 - eapply scalar_at_lframe;[exact Storage|exact Frame|exact Outside].
 - intros pos k p;rewrite Perms;apply Bounds.
Qed.

Theorem exec_strauss_zero_generator_branch (Model:memset_model) e le m b0 b128 bw0 bw128 bits :
 NoDup [b0;b128;bw0;bw128] ->
 e!_ng_1=Some (b0,Tstruct __5826 noattr) -> e!_ng_128=Some (b128,Tstruct __5826 noattr) ->
 e!_wnaf_ng_1=Some (bw0,tarray tint 129) -> e!_wnaf_ng_128=Some (bw128,tarray tint 129) ->
 e!_secp256k1_scalar_split_128=None -> e!_secp256k1_ecmult_wnaf=None ->
 le!_ng=Some (Vptr strauss_zero_block Ptrofs.zero) ->
 0<=bits<=129 -> le!_bits=Some (Vint (Int.repr bits)) ->
 strauss_zero_global_state m ->
 Mem.range_perm m b0 0 32 Cur Freeable -> Mem.range_perm m b128 0 32 Cur Freeable ->
 Mem.range_perm m bw0 0 516 Cur Freeable -> Mem.range_perm m bw128 0 516 Cur Freeable ->
 exists mf,
 Clight2.exec_stmt secp_ge e le m generator_scalar_branch E0 (strauss_zero_wnaf_temps le) mf Out_normal /\
 (strauss_zero_wnaf_temps le)!_bits=Some (Vint (Int.repr bits)) /\
 (strauss_zero_wnaf_temps le)!_bits_ng_1=Some (Vint Int.zero) /\
 (strauss_zero_wnaf_temps le)!_bits_ng_128=Some (Vint Int.zero) /\
 scalar_at mf b0 0 [Int64.zero;Int64.zero;Int64.zero;Int64.zero] /\
 scalar_at mf b128 0 [Int64.zero;Int64.zero;Int64.zero;Int64.zero] /\
 Mem.range_perm mf b0 0 32 Cur Freeable /\ Mem.range_perm mf b128 0 32 Cur Freeable /\
 Mem.range_perm mf bw0 0 516 Cur Freeable /\ Mem.range_perm mf bw128 0 516 Cur Freeable /\
 strauss_zero_global_state mf /\
 lframe (fun b _=>b<>b0 /\ b<>b128 /\ b<>bw0 /\ b<>bw128) m mf /\
 (forall old pos k p,Mem.valid_block m old -> (Mem.perm mf old pos k p <-> Mem.perm m old pos k p)).
Proof.
 intros Separate S0 S128 W0 W128 SplitSymbol WnafSymbol NG Bound Bits Global Free0 Free128 FreeW0 FreeW128.
 pose proof (proj1 Global) as GlobalStorage.
 destruct GlobalStorage as (_ & _ & _ & _ & SourceRead & SourceLoads).
 assert (LowHigh:b0<>b128).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence. }
 assert (LowGlobal:b0<>strauss_zero_block).
 { eapply strauss_zero_global_separate;[exact Global|apply (Free0 0);clear;lia]. }
 assert (HighGlobal:b128<>strauss_zero_block).
 { eapply strauss_zero_global_separate;[exact Global|apply (Free128 0);clear;lia]. }
 assert (WLowGlobal:bw0<>strauss_zero_block).
 { eapply strauss_zero_global_separate;[exact Global|apply (FreeW0 0);clear;lia]. }
 assert (WHighGlobal:bw128<>strauss_zero_block).
 { eapply strauss_zero_global_separate;[exact Global|apply (FreeW128 0);clear;lia]. }
 pose (value:=@Word.zero 8 Alg.CoreFunSem tt).
 assert (Normalized:@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)=0).
 { rewrite canonical_scalar_normalize_numeric;unfold value;rewrite Word.zero_correct;apply Z.mod_0_l;pose proof canonical_group_order_range;lia. }
 assert (Input:scalar_at m strauss_zero_block 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value))))).
 { rewrite Normalized;exact (proj1 Global). }
 destruct (exec_generator_scalar_split e le m value b0 b128 strauss_zero_block 0
  S0 S128 SplitSymbol NG LowHigh LowGlobal HighGlobal Free0 Free128 Input)
  as (ms & Split & Low & High & F0 & F128 & Blocks & Perms & FrameS).
 destruct (literal_scalar_split128_numeric value) as [LV HV].
 rewrite Normalized in LV,HV.
 change (@toZ (WordToZ 7) (literal_split128_low value)=0) in LV.
 change (@toZ (WordToZ 7) (literal_split128_high value)=0) in HV.
 rewrite LV in Low;rewrite HV in High.
 assert (Readback:readonly_readback m ms).
 { eapply (proj1 (clight_exec_readonly_readback secp_ge));exact Split. }
 assert (Readable:Mem.range_perm ms strauss_zero_block 0 32 Cur Readable).
 { intros pos Range;apply (proj2 (Perms _ _ _ _));exact (SourceRead pos Range). }
 assert (FrameG:lframe (fun b _=>b=strauss_zero_block) m ms).
 { eapply readonly_region_lframe;[apply strauss_zero_global_valid;exact Global|exact (proj2 Global)|exact Readable|exact Readback]. }
 assert (FrameSplit:lframe (fun b _=>b<>b0 /\ b<>b128) m ms).
 { eapply lframe_add_block;[exact FrameS|exact FrameG|intros b pos Other [L H];repeat split;assumption]. }
 assert (FW0:Mem.range_perm ms bw0 0 516 Cur Freeable).
 { intros pos Range;apply (proj2 (Perms _ _ _ _));apply FreeW0;exact Range. }
 assert (FW128:Mem.range_perm ms bw128 0 516 Cur Freeable).
 { intros pos Range;apply (proj2 (Perms _ _ _ _));apply FreeW128;exact Range. }
 destruct (exec_strauss_zero_wnaf_setup Model e le ms b0 b128 bw0 bw128 bits
  Separate S0 S128 W0 W128 WnafSymbol Bound Bits Low High FW0 FW128)
  as (mf & Setup & FinalBits & G1 & G128 & Fw0 & Fw128 & FrameW & PermW).
 assert (Valid0:Mem.valid_block ms b0) by (eapply Mem.perm_valid_block;apply (F0 0);clear;lia).
 assert (Valid128:Mem.valid_block ms b128) by (eapply Mem.perm_valid_block;apply (F128 0);clear;lia).
 assert (AllPerms:forall old pos k p,Mem.valid_block m old ->
  (Mem.perm mf old pos k p <-> Mem.perm m old pos k p)).
 { intros old pos k p Valid;rewrite (PermW old pos k p (proj2 (proj2 FrameS) old Valid));apply Perms. }
 assert (Frame:lframe (fun b _=>b<>b0 /\ b<>b128 /\ b<>bw0 /\ b<>bw128) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameSplit|intros b pos (L & H & WL & WH) _;split;assumption].
   - eapply lframe_implies;[exact FrameW|intros b pos (L & H & WL & WH) _;split;assumption]. }
 assert (GlobalF:strauss_zero_global_state mf).
 { eapply strauss_zero_global_lframe;[exact Global|exact Frame| |].
   - intros pos;repeat split;congruence.
   - intros;apply AllPerms;apply strauss_zero_global_valid;exact Global. }
 assert (LowF:scalar_at mf b0 0 [Int64.zero;Int64.zero;Int64.zero;Int64.zero]).
 { eapply scalar_at_lframe;[exact Low|exact FrameW|].
   intros pos;clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence. }
 assert (HighF:scalar_at mf b128 0 [Int64.zero;Int64.zero;Int64.zero;Int64.zero]).
 { eapply scalar_at_lframe;[exact High|exact FrameW|].
   intros pos;clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence. }
 assert (Owned0:Mem.range_perm mf b0 0 32 Cur Freeable).
 { intros pos Range;apply (proj2 (PermW b0 pos Cur Freeable Valid0));apply F0;exact Range. }
 assert (Owned128:Mem.range_perm mf b128 0 32 Cur Freeable).
 { intros pos Range;apply (proj2 (PermW b128 pos Cur Freeable Valid128));apply F128;exact Range. }
 assert (Present:Cop.bool_val (Vptr strauss_zero_block Ptrofs.zero) (tptr (Tstruct __5826 noattr)) m=Some true).
 { change ((if Mem.weak_valid_pointer m strauss_zero_block 0 then Some true else None)=Some true).
   assert (Weak:Mem.weak_valid_pointer m strauss_zero_block 0=true).
   { apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm.
     eapply Mem.perm_implies;[apply (SourceRead 0);clear;lia|apply perm_any_N]. }
   rewrite Weak;reflexivity. }
 exists mf;split.
 - rewrite generator_scalar_branch_source.
   eapply exec_Sifthenelse with (v1:=Vptr strauss_zero_block Ptrofs.zero) (b:=true).
   + apply eval_Etempvar;exact NG.
   + exact Present.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Split|exact Setup].
 - split;[exact FinalBits|];split;[exact G1|];split;[exact G128|];
   split;[exact LowF|];split;[exact HighF|];split;[exact Owned0|];split;[exact Owned128|];
   split;[exact Fw0|];split;[exact Fw128|];split;[exact GlobalF|];split;assumption.
Qed.
