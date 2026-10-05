(** Complete execution of [simplicity_bitcoin_make_tapleaf(version, cmr)]
    (bitcoin/ops.c) in the SHA translation unit: the result structure
    receives the tagged hash of the version byte, the byte 32 and the CMR.
    Conditional on [memcpy_model] and on the global tag name holding
    "TapLeaf". *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_bitmachine_rep.
Require Import C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_struct_copy_loads.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_ctx8_model.
Require Import C.jet_sha_compress_call.
Require Import C.jet_sha_be32_exec C.jet_sha_be32_write C.jet_sha_be64_exec.
Require Import C.jet_sha_compress_uchar C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec.
Require Import C.jet_sha_add_n_init C.jet_sha_add_n_calls C.jet_sha_uchar_exec C.jet_sha_hash_exec C.jet_sha_finalize_exec.
Require Import C.jet_sha_tapdata_prep C.jet_sha_ctx_abs C.jet_sha_ctxi C.jet_sha_tagged_ctx.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Definition tapleaf_tag_ints : list int := map Int.repr [84; 97; 112; 76; 101; 97; 102].

Definition sha_tapleaf_tag_ok (m : mem) : Prop :=
  forall i, (i < 7)%nat ->
    Mem.load Mint8unsigned m (sha_symbol_block _tagName__1) (Z.of_nat i) =
      Some (Vint (nth i tapleaf_tag_ints Int.zero)).

Definition make_tapleaf_regs (v : int) (cmr : list int) : list int :=
  snd (absorb_i ([v; Int.repr 32] ++ be_bytes cmr) (tagged_prefix tapleaf_tag_ints)
    (sha_pad (Int64.repr 98))).

Definition tl_env (bRes bT bC bC1 bR1 bR2 : block) : env :=
  PTree.set __res__2 (bR2, CTX) (PTree.set __res__1 (bR1, CTX) (PTree.set _ctx__1 (bC1, CTX)
    (PTree.set _ctx (bC, CTX) (PTree.set _tapleafTag (bT, MID)
      (PTree.set _result (bRes, MID) empty_env))))).

Definition tl_temps (vres vver vcmr : val) : temp_env :=
  PTree.set _cmr vcmr (PTree.set _version vver (PTree.set __res vres
    (create_undef_temps (fn_temps f_simplicity_bitcoin_make_tapleaf)))).

Lemma tl_tag_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _tagName__1 = Some (sha_symbol_block _tagName__1).
Proof. vm_compute; reflexivity. Qed.

Lemma tl_uchar_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_uchar = Some (sha_symbol_block _sha256_uchar).
Proof. vm_compute; reflexivity. Qed.
Lemma tl_uchar_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_uchar) Ptrofs.zero) =
    Some (Internal f_sha256_uchar).
Proof. vm_compute; reflexivity. Qed.

Lemma eval_local_mid_s e le m id b :
  e!id = Some (b, MID) ->
  eval_expr sha_ge e le m (Efield (Evar id MID) _s (tarray tuint 8)) (Vptr b Ptrofs.zero).
Proof.
  intros He. eapply eval_Elvalue.
  - eapply eval_Efield_struct with (delta := 0).
    + eapply eval_Elvalue; [apply eval_Evar_local; exact He|apply deref_loc_copy; reflexivity].
    + reflexivity.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
  - apply deref_loc_reference; reflexivity.
Qed.

Lemma tl_cast32 m : sem_cast (Vint (Int.repr 32)) tint tuchar m = Some (Vint (Int.repr 32)).
Proof. vm_compute. reflexivity. Qed.

Lemma tl_ext32 : Int.zero_ext 8 (Int.repr 32) = Int.repr 32.
Proof. vm_compute. reflexivity. Qed.

Lemma tl_blocks bRes bT bC bC1 bR1 bR2 :
  blocks_of_env sha_ge (tl_env bRes bT bC bC1 bR1 bR2) =
    [(bC1, 0, 88); (bC, 0, 88); (bR2, 0, 88); (bR1, 0, 88); (bT, 0, 32); (bRes, 0, 32)].
Proof. vm_compute. reflexivity. Qed.

Lemma tl_entry m m1 m2 m3 m4 m5 m6 bRes bT bC bC1 bR1 bR2 vres vver vcmr :
  Mem.alloc m 0 32 = (m1, bRes) -> Mem.alloc m1 0 32 = (m2, bT) -> Mem.alloc m2 0 88 = (m3, bC) ->
  Mem.alloc m3 0 88 = (m4, bC1) -> Mem.alloc m4 0 88 = (m5, bR1) -> Mem.alloc m5 0 88 = (m6, bR2) ->
  function_entry2 sha_ge f_simplicity_bitcoin_make_tapleaf [vres; vver; vcmr] m
    (tl_env bRes bT bC bC1 bR1 bR2) (tl_temps vres vver vcmr) m6.
Proof.
  intros A1 A2 A3 A4 A5 A6. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HY. contradiction.
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bRes); [change (Mem.alloc m 0 32 = (m1, bRes)); exact A1|].
    eapply alloc_variables_cons with (m1 := m2) (b1 := bT); [change (Mem.alloc m1 0 32 = (m2, bT)); exact A2|].
    eapply alloc_variables_cons with (m1 := m3) (b1 := bC); [change (Mem.alloc m2 0 88 = (m3, bC)); exact A3|].
    eapply alloc_variables_cons with (m1 := m4) (b1 := bC1); [change (Mem.alloc m3 0 88 = (m4, bC1)); exact A4|].
    eapply alloc_variables_cons with (m1 := m5) (b1 := bR1); [change (Mem.alloc m4 0 88 = (m5, bR1)); exact A5|].
    eapply alloc_variables_cons with (m1 := m6) (b1 := bR2); [change (Mem.alloc m5 0 88 = (m6, bR2)); exact A6|].
    constructor.
  - reflexivity.
Qed.

Local Opaque sha_ge.

Ltac nd6 :=
  repeat (apply NoDup_cons;
    [let HIn := fresh in intro HIn; cbn [In] in HIn;
     repeat (destruct HIn as [HIn|HIn]; [revert HIn; ne|]); exact HIn|]);
  apply NoDup_nil.

Theorem eval_make_tapleaf (Hmodel : memcpy_model) m bres ores (v : int) bcmr ocmr (cmr : list int) :
  Int.zero_ext 8 v = v ->
  0 <= ores -> ores + 32 <= Ptrofs.max_unsigned -> (4 | ores) ->
  Mem.range_perm m bres ores (ores + 32) Cur Writable ->
  length cmr = 8%nat -> Ptrofs.unsigned ocmr + 32 <= Ptrofs.max_unsigned ->
  (forall j, (j < 8)%nat ->
     Mem.load Mint32 m bcmr (Ptrofs.unsigned ocmr + 4 * Z.of_nat j) = Some (Vint (nth j cmr Int.zero))) ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  sha_tapleaf_tag_ok m ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_bitcoin_make_tapleaf)
      [Vptr bres (Ptrofs.repr ores); Vint v; Vptr bcmr ocmr] E0 m' Vundef /\
    (forall j, (j < 8)%nat ->
       Mem.load Mint32 m' bres (ores + 4 * Z.of_nat j) =
         Some (Vint (nth j (make_tapleaf_regs v cmr) Int.zero))) /\
    (forall ch b ofs, Mem.valid_block m b ->
       (b <> bres \/ ofs + size_chunk ch <= ores \/ ores + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros Hv Ho0 HoM HoA PRes Hcmr HcM HCmr Hdisp HMax HTag.
  set (TAG := sha_symbol_block _tagName__1) in *.
  assert (VG : Mem.valid_block m GC) by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m GM) by (eapply load_valid_block; exact HMax).
  assert (VT : Mem.valid_block m TAG) by (eapply load_valid_block; exact (HTag 0%nat ltac:(lia))).
  assert (Vcmr : Mem.valid_block m bcmr) by (eapply load_valid_block; exact (HCmr 0%nat ltac:(lia))).
  assert (Vres : Mem.valid_block m bres).
  { eapply Mem.perm_valid_block. apply (PRes ores). lia. }
  destruct (Mem.alloc m 0 32) as [ma1 bRes] eqn:A1.
  destruct (Mem.alloc ma1 0 32) as [ma2 bT] eqn:A2.
  destruct (Mem.alloc ma2 0 88) as [ma3 bC] eqn:A3.
  destruct (Mem.alloc ma3 0 88) as [ma4 bC1] eqn:A4.
  destruct (Mem.alloc ma4 0 88) as [ma5 bR1] eqn:A5.
  destruct (Mem.alloc ma5 0 88) as [m0 bR2] eqn:A6.
  assert (HAL : alloc_list m [32; 32; 88; 88; 88; 88] = (m0, [bRes; bT; bC; bC1; bR1; bR2])).
  { cbn [alloc_list]. rewrite A1, A2, A3, A4, A5, A6. reflexivity. }
  destruct (alloc_list_props _ _ _ _ HAL) as ((XV & XL & XP & XA) & FRh & ND & FA).
  inversion FA as [|? ? ? ? [PRes0 VRes0] FA1]; subst.
  inversion FA1 as [|? ? ? ? [PT0 VT0] FA2]; subst.
  inversion FA2 as [|? ? ? ? [PC0 VC0] FA3]; subst.
  inversion FA3 as [|? ? ? ? [PC10 VC10] FA4]; subst.
  inversion FA4 as [|? ? ? ? [PR10 VR10] FA5]; subst.
  inversion FA5 as [|? ? ? ? [PR20 VR20] FA6]; subst. clear FA FA1 FA2 FA3 FA4 FA5 FA6 HAL.
  apply NoDup_cons_iff in ND. destruct ND as [N1 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N2 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N3 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N4 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N5 _].
  assert (NDL : NoDup [bR2; bC; bT; bR1; bC1; bRes]) by nd6.
  assert (Fresh : forall b, Mem.valid_block m b -> ~ In b [bR2; bC; bT; bR1; bC1; bRes]).
  { intros b Hb HIn. apply (FRh b Hb). cbn [In] in HIn |- *. tauto. }
  pose proof (Fresh GC VG) as NG. pose proof (Fresh GM VM) as NM. pose proof (Fresh TAG VT) as NT.
  pose proof (Fresh bcmr Vcmr) as Ncmr. pose proof (Fresh bres Vres) as Nres.
  (* the tagged context *)
  destruct (tagged_ctx_mem Hmodel m0 bR2 bC bT bR1 bC1 bRes TAG tapleaf_tag_ints NDL
    (XV _ VG) (XV _ VM) (XV _ VT) NG NM NT VT0 PR20 PC0 PT0 PR10 PC10 PRes0)
    as (mi1 & bytes1 & m1 & m2 & m3 & mi2 & bytes2 & m4 & m5 & m6 &
        HInit1 & HLB1 & HSB1 & HUc & HFin & HInit2 & HLB2 & HSB2 & HHc5 & HHc6 & HA6 & HL6 & HP6 & HV6).
  { unfold sha_dispatch_ok. rewrite XL by exact VG. exact Hdisp. }
  { rewrite XL by exact VM. exact HMax. }
  { cbn. lia. }
  { intros i Hi. rewrite XL by exact VT. apply HTag. exact Hi. }
  change (Int64.repr (Z.of_nat (length tapleaf_tag_ints))) with (Int64.repr 7) in HUc, HFin.
  set (P := tagged_prefix tapleaf_tag_ints) in *.
  assert (K6 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m6 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite HL6; [apply XL; exact Hb|apply XV; exact Hb|apply Fresh; exact Hb]. }
  (* the version byte, the byte 32, the CMR *)
  pose proof (ctxi_uchar bC1 bRes ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) Hmodel
    m6 [] P v _ _ HA6 Hv) as HU7.
  cbv zeta in HU7. destruct HU7 as (m7 & HUc7 & HA7 & HL7 & HP7 & HV7).
  rewrite (absorb_i_small [v] [] P) in HA7 by (cbn; lia). cbn [fst snd app] in HA7.
  pose proof (ctxi_uchar bC1 bRes ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) Hmodel
    m7 [v] P (Int.repr 32) _ _ HA7 tl_ext32) as HU8.
  cbv zeta in HU8. destruct HU8 as (m8 & HUc8 & HA8 & HL8 & HP8 & HV8).
  rewrite (absorb_i_small [Int.repr 32] [v] P) in HA8 by (cbn; lia). cbn [fst snd app] in HA8.
  assert (V8 : forall b, Mem.valid_block m b -> Mem.valid_block m8 b).
  { intros b Hb. apply HV8, HV7, HV6, XV, Hb. }
  assert (K8 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m8 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. pose proof (Fresh b Hb) as Nb.
    rewrite HL8; [|apply HV7, HV6, XV, Hb|ne|ne].
    rewrite HL7; [|apply HV6, XV, Hb|ne|ne]. apply K6. exact Hb. }
  assert (HCmr8 : forall j, (j < 8)%nat ->
    Mem.load Mint32 m8 bcmr (Ptrofs.unsigned ocmr + 4 * Z.of_nat j) = Some (Vint (nth j cmr Int.zero))).
  { intros j Hj. rewrite K8 by exact Vcmr. apply HCmr. exact Hj. }
  pose proof (ctxi_hash bC1 bRes ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) Hmodel
    m8 bcmr ocmr [v; Int.repr 32] P cmr _ _ HA8 Hcmr HcM HCmr8) as HH9.
  cbv zeta in HH9. destruct HH9 as (m9 & HHc9 & HA9 & HL9 & HP9 & HV9).
  assert (HbC : length (be_bytes cmr) = 32%nat) by (rewrite be_bytes_length, Hcmr; reflexivity).
  rewrite (absorb_i_small (be_bytes cmr) [v; Int.repr 32] P) in HA9 by (rewrite HbC; cbn; lia).
  cbn [fst snd] in HA9.
  change (Int64.add (Int64.add (Int64.add (Int64.repr 64) (Int64.repr 1)) (Int64.repr 1)) (Int64.repr 32))
    with (Int64.repr 98) in HA9.
  destruct (ctxi_finalize bC1 bRes ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) Hmodel
    m9 _ P _ _ HA9) as (m10 & HFin10 & HReg10 & HL10 & HP10 & HV10).
  fold (make_tapleaf_regs v cmr) in HReg10.
  assert (V10 : forall b, Mem.valid_block m b -> Mem.valid_block m10 b).
  { intros b Hb. apply HV10, HV9, V8, Hb. }
  assert (K10 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m10 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. pose proof (Fresh b Hb) as Nb.
    rewrite HL10; [|apply HV9, V8, Hb|ne|ne].
    rewrite HL9; [|apply V8, Hb|ne|ne]. apply K8. exact Hb. }
  assert (P10 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m10 b ofs k p).
  { intros b ofs k p Hp.
    assert (Hp6 : Mem.perm m6 b ofs k p) by (apply HP6, Hp).
    assert (Hp7 : Mem.perm m7 b ofs k p) by (apply HP7; [eapply Mem.perm_valid_block; exact Hp6|exact Hp6]).
    assert (Hp8 : Mem.perm m8 b ofs k p) by (apply HP8; [eapply Mem.perm_valid_block; exact Hp7|exact Hp7]).
    assert (Hp9 : Mem.perm m9 b ofs k p) by (apply HP9; [eapply Mem.perm_valid_block; exact Hp8|exact Hp8]).
    apply HP10; [eapply Mem.perm_valid_block; exact Hp9|exact Hp9]. }
  (* the result copy *)
  assert (PRd : Mem.range_perm m10 bRes 0 32 Cur Readable).
  { intros ofs Hr. eapply Mem.perm_implies; [apply P10, PRes0, Hr|constructor]. }
  destruct (Mem.range_perm_loadbytes m10 bRes 0 32 PRd) as (bytes & HB).
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as HBL.
  assert (PWr : Mem.range_perm m10 bres ores (ores + Z.of_nat (length bytes)) Cur Writable).
  { rewrite HBL. change (Z.of_nat (Z.to_nat 32)) with 32. intros ofs Hr. apply P10, XP, PRes, Hr. }
  destruct (Mem.range_perm_storebytes m10 bres ores bytes PWr) as (m11 & HS).
  assert (HB11 : Mem.loadbytes m11 bres ores 32 = Some bytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ HS) as H. rewrite HBL in H. exact H. }
  assert (HoU : Ptrofs.unsigned (Ptrofs.repr ores) = ores) by (apply Ptrofs.unsigned_repr; lia).
  (* freeing the locals *)
  destruct (free_list_blocks
    [(bC1, 0, 88); (bC, 0, 88); (bR2, 0, 88); (bR1, 0, 88); (bT, 0, 32); (bRes, 0, 32)] m11)
    as (mf & HFL & HLf & HPf & HVf).
  { intros b lo hi HIn ofs Hr. eapply Mem.perm_storebytes_1; [exact HS|]. apply P10.
    cbn [In] in HIn.
    destruct HIn as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <- <-;
      [apply PC10|apply PC0|apply PR20|apply PR10|apply PT0|apply PRes0]; exact Hr. }
  { cbn [map fst]. nd6. }
  cbn [map fst] in HLf, HPf.
  assert (HNl : forall b, Mem.valid_block m b -> ~ In b [bC1; bC; bR2; bR1; bT; bRes]).
  { intros b Hb HIn. apply (FRh b Hb). cbn [In] in HIn |- *. tauto. }
  set (e := tl_env bRes bT bC bC1 bR1 bR2).
  set (le := tl_temps (Vptr bres (Ptrofs.repr ores)) (Vint v) (Vptr bcmr ocmr)).
  exists mf. split; [|split; [|split; [|split]]].
  - eapply eval_funcall_internal with (e := e) (le1 := le) (m1 := m0) (le2 := le) (m2 := m11)
      (out := Out_return None).
    + eapply tl_entry; eassumption.
    + unfold f_simplicity_bitcoin_make_tapleaf. cbn [fn_body].
      assert (HInitCall : forall ma mb idres idarr br ba,
        e!idres = Some (br, CTX) -> e!idarr = Some (ba, MID) ->
        Clight2.eval_funcall sha_ge ma (Internal jets.f_sha256_init)
          [Vptr br Ptrofs.zero; Vptr ba (Ptrofs.repr 0)] E0 mb Vundef ->
        Clight2.exec_stmt sha_ge e le ma
          (Scall None (Evar _sha256_init
            (Tfunction (Tcons CTXP (Tcons (tptr tuint) Tnil)) tvoid
              {| cc_vararg := None; cc_unproto := false; cc_structret := true |}))
            [Eaddrof (Evar idres CTX) CTXP; Efield (Evar idarr MID) _s (tarray tuint 8)])
          E0 le mb Out_normal).
      { intros ma mb idres idarr br ba H1 H2 HC.
        change le with (set_opttemp None Vundef le) at 2.
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_init) Ptrofs.zero)
          (vargs := [Vptr br Ptrofs.zero; Vptr ba Ptrofs.zero]) (f := Internal jets.f_sha256_init).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact tap_init_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact H1|reflexivity|].
          eapply eval_Econs; [apply eval_local_mid_s; exact H2|reflexivity|apply eval_Enil].
        - exact tap_init_funct.
        - reflexivity.
        - exact HC. }
      assert (HHashCall : forall ma mb (arg : expr) bt ot,
        eval_expr sha_ge e le ma arg (Vptr bt ot) -> typeof arg = tptr MID ->
        Clight2.eval_funcall sha_ge ma (Internal f_sha256_hash) [Vptr bC1 (Ptrofs.repr 0); Vptr bt ot] E0 mb Vundef ->
        Clight2.exec_stmt sha_ge e le ma
          (Scall None (Evar _sha256_hash (Tfunction (Tcons CTXP (Tcons (tptr MID) Tnil)) tvoid cc_default))
            [Eaddrof (Evar _ctx__1 CTX) CTXP; arg]) E0 le mb Out_normal).
      { intros ma mb arg bt ot HE HTy HC. change le with (set_opttemp None Vundef le) at 2.
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_hash) Ptrofs.zero)
          (vargs := [Vptr bC1 Ptrofs.zero; Vptr bt ot]) (f := Internal f_sha256_hash).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_hash_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
          eapply eval_Econs; [exact HE|rewrite HTy; reflexivity|apply eval_Enil].
        - exact sha_hash_funct.
        - reflexivity.
        - exact HC. }
      assert (HFinCall : forall ma mb id bx vr,
        e!id = Some (bx, CTX) ->
        Clight2.eval_funcall sha_ge ma (Internal f_sha256_finalize) [Vptr bx (Ptrofs.repr 0)] E0 mb vr ->
        Clight2.exec_stmt sha_ge e le ma
          (Scall None (Evar _sha256_finalize (Tfunction (Tcons CTXP Tnil) tbool cc_default))
            [Eaddrof (Evar id CTX) CTXP]) E0 le mb Out_normal).
      { intros ma mb id bx vr H1 HC. change le with (set_opttemp None vr le) at 2.
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_finalize) Ptrofs.zero)
          (vargs := [Vptr bx Ptrofs.zero]) (f := Internal f_sha256_finalize).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_finalize_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact H1|reflexivity|apply eval_Enil].
        - exact sha_finalize_funct.
        - reflexivity.
        - exact HC. }
      assert (HUcharCall : forall ma mb (arg : expr) x vr,
        eval_expr sha_ge e le ma arg (Vint x) -> sem_cast (Vint x) (typeof arg) tuchar ma = Some (Vint x) ->
        Clight2.eval_funcall sha_ge ma (Internal f_sha256_uchar) [Vptr bC1 (Ptrofs.repr 0); Vint x] E0 mb vr ->
        Clight2.exec_stmt sha_ge e le ma
          (Scall None (Evar _sha256_uchar (Tfunction (Tcons CTXP (Tcons tuchar Tnil)) tbool cc_default))
            [Eaddrof (Evar _ctx__1 CTX) CTXP; arg]) E0 le mb Out_normal).
      { intros ma mb arg x vr HE HCast HC. change le with (set_opttemp None vr le) at 2.
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_uchar) Ptrofs.zero)
          (vargs := [Vptr bC1 Ptrofs.zero; Vint x]) (f := Internal f_sha256_uchar).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact tl_uchar_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
          eapply eval_Econs; [exact HE|exact HCast|apply eval_Enil].
        - exact tl_uchar_funct.
        - reflexivity.
        - exact HC. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m3).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m1).
        - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mi1).
          + apply (HInitCall m0 mi1 __res__2 _tapleafTag bR2 bT eq_refl eq_refl HInit1).
          + eapply (exec_ctx_struct_copy e le mi1 m1 _ctx __res__2 bC bR2 bytes1);
              [reflexivity|reflexivity|ne|exact HLB1|exact HSB1].
        - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m2).
          + match type of HUc with Clight2.eval_funcall _ _ _ _ _ _ ?vr =>
              change le with (set_opttemp None vr le) at 2 end.
            eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_uchars) Ptrofs.zero)
              (vargs := [Vptr bC Ptrofs.zero; Vptr TAG Ptrofs.zero; Vlong (Int64.repr 7)])
              (f := Internal f_sha256_uchars).
            * reflexivity.
            * eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_uchars_symbol]|].
              apply deref_loc_reference; reflexivity.
            * eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
              eapply eval_Econs.
              -- eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact tl_tag_symbol]|].
                 apply deref_loc_reference; reflexivity.
              -- reflexivity.
              -- eapply eval_Econs with (v1 := Vlong (Int64.repr 7)); [|reflexivity|apply eval_Enil].
                 eapply eval_Ebinop; [apply eval_Esizeof|apply eval_Econst_int|reflexivity].
            * exact sha_uchars_funct.
            * reflexivity.
            * exact HUc.
          + exact (HFinCall m2 m3 _ctx bC _ eq_refl HFin). }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m4).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mi2).
        - apply (HInitCall m3 mi2 __res__1 _result bR1 bRes eq_refl eq_refl HInit2).
        - eapply (exec_ctx_struct_copy e le mi2 m4 _ctx__1 __res__1 bC1 bR1 bytes2);
            [reflexivity|reflexivity|ne|exact HLB2|exact HSB2]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m5).
      { apply (HHashCall m4 m5 _ bT Ptrofs.zero); [|reflexivity|exact HHc5].
        eapply eval_Eaddrof; apply eval_Evar_local; reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m6).
      { apply (HHashCall m5 m6 _ bT Ptrofs.zero); [|reflexivity|exact HHc6].
        eapply eval_Eaddrof; apply eval_Evar_local; reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m7).
      { eapply (HUcharCall m6 m7 _ v); [apply eval_Etempvar; reflexivity| |exact HUc7].
        change (Some (Vint (Int.zero_ext 8 v)) = Some (Vint v)). rewrite Hv. reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m8).
      { eapply (HUcharCall m7 m8 _ (Int.repr 32)); [apply eval_Econst_int|apply tl_cast32|exact HUc8]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m9).
      { apply (HHashCall m8 m9 _ bcmr ocmr); [apply eval_Etempvar; reflexivity|reflexivity|exact HHc9]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m10).
      { exact (HFinCall m9 m10 _ctx__1 bC1 _ eq_refl HFin10). }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m11).
      { eapply exec_Sassign with (v2 := Vptr bRes Ptrofs.zero) (v := Vptr bRes Ptrofs.zero).
        - eapply eval_Ederef. apply eval_Etempvar. reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_copy; reflexivity].
        - reflexivity.
        - eapply assign_loc_copy with (bytes := bytes).
          + reflexivity.
          + intros _. exists 0. reflexivity.
          + intros _. change (4 | Ptrofs.unsigned (Ptrofs.repr ores)). rewrite HoU. exact HoA.
          + left. ne.
          + exact HB.
          + rewrite HoU. exact HS. }
      apply exec_Sreturn_none.
    + reflexivity.
    + unfold e. rewrite tl_blocks. exact HFL.
  - intros j Hj. rewrite HLf by (apply HNl; exact Vres).
    apply (equal_loadbytes_field Mint32 m10 m11 bRes bres 0 ores 32 (4 * Z.of_nat j) bytes).
    + lia.
    + change (size_chunk Mint32) with 4. lia.
    + exact HB.
    + exact HB11.
    + change (align_chunk Mint32) with 4. apply Z.divide_add_r; [exact HoA|exists (Z.of_nat j); lia].
    + apply HReg10. exact Hj.
  - intros ch b ofs Hb Hr. rewrite HLf by (apply HNl; exact Hb).
    rewrite (Mem.load_storebytes_other _ _ _ _ _ HS).
    + apply K10. exact Hb.
    + rewrite HBL. change (Z.of_nat (Z.to_nat 32)) with 32.
      destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; exact Hr|right; right; exact Hr].
  - intros b ofs k p Hp. apply HPf; [apply HNl; eapply Mem.perm_valid_block; exact Hp|].
    eapply Mem.perm_storebytes_1; [exact HS|]. apply P10, XP, Hp.
  - intros b Hb. apply HVf. eapply Mem.storebytes_valid_block_1; [exact HS|]. apply V10, Hb.
Qed.
