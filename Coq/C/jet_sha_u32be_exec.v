(** Complete execution of [sha256_u32be(ctx, x)] in the SHA translation
    unit, mirroring [jet_sha_be64_exec].  Conditional on [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_ctx8_model C.jet_sha_compress_call.
Require Import C.jet_sha_be32_exec C.jet_sha_be32_write C.jet_sha_be64_exec.
Require Import C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Lemma sha_u32be_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_u32be = Some (sha_symbol_block _sha256_u32be).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_u32be_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_u32be) Ptrofs.zero) =
    Some (Internal f_sha256_u32be).
Proof. vm_compute; reflexivity. Qed.

Definition u32_env (bb : block) : env := PTree.set _buf (bb, tarray tuchar 4) empty_env.
Definition u32_temps (bx : block) (cbase : Z) (x : int64) : temp_env :=
  PTree.set _x (Vlong x) (PTree.set _ctx (Vptr bx (Ptrofs.repr cbase))
    (create_undef_temps (fn_temps f_sha256_u32be))).

Lemma u32_blocks bb : blocks_of_env sha_ge (u32_env bb) = [(bb, 0, 4)].
Proof. vm_compute. reflexivity. Qed.

Lemma u32_entry m m1 bb bx cbase x :
  Mem.alloc m 0 4 = (m1, bb) ->
  function_entry2 sha_ge f_sha256_u32be [Vptr bx (Ptrofs.repr cbase); Vlong x] m
    (u32_env bb) (u32_temps bx cbase x) m1.
Proof.
  intros HA. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros a b HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bb).
    + change (Mem.alloc m 0 4 = (m1, bb)); exact HA.
    + constructor.
  - reflexivity.
Qed.

Local Opaque sha_ge.

Theorem eval_sha256_u32be (Hmodel : memcpy_model) m bx cbase bo obase
    (l regs : list int) (c x : int64) (ovf : bool) :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned -> 0 <= obase -> obase + 32 <= Ptrofs.max_unsigned ->
  bo <> bx ->
  sha_symbol_block _simplicity_sha256_compression <> bx ->
  sha_symbol_block _simplicity_sha256_compression <> bo ->
  length regs = 8%nat ->
  Mem.load Mptr m bx cbase = Some (Vptr bo (Ptrofs.repr obase)) ->
  Mem.load Mint64 m bx (cbase + 8) = Some (Vlong c) ->
  Int64.unsigned c mod 64 = Z.of_nat (length l) ->
  Mem.load Mint8unsigned m bx (cbase + 80) = Some (Vint (bit_int ovf)) ->
  (forall i, (i < length l)%nat ->
     Mem.load Mint8unsigned m bx (cbase + 16 + Z.of_nat i) = Some (Vint (nth i l Int.zero))) ->
  (forall i, (i < 8)%nat ->
     Mem.load Mint32 m bo (obase + 4 * Z.of_nat i) = Some (Vint (nth i regs Int.zero)) /\
     Mem.valid_access m Mint32 bo (obase + 4 * Z.of_nat i) Writable) ->
  sha_dispatch_ok m ->
  Mem.load Mint64 m (sha_symbol_block _sha256_max_counter) 0 = Some (Vlong sha_max_counter) ->
  Mem.range_perm m bx (cbase + 8) (cbase + 81) Cur Writable -> (8 | cbase) ->
  let bs := c_be32_bytes x in
  let ovf' := uc_overflow ovf c (Int64.repr 4) in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_u32be)
      [Vptr bx (Ptrofs.repr cbase); Vlong x] E0 m' (Vint (bit_int (negb ovf'))) /\
    Mem.load Mptr m' bx cbase = Some (Vptr bo (Ptrofs.repr obase)) /\
    Mem.load Mint64 m' bx (cbase + 8) = Some (Vlong (Int64.add c (Int64.repr 4))) /\
    Mem.load Mint8unsigned m' bx (cbase + 80) = Some (Vint (bit_int ovf')) /\
    (forall i, (i < length (fst (absorb_i l regs bs)))%nat ->
       Mem.load Mint8unsigned m' bx (cbase + 16 + Z.of_nat i) =
         Some (Vint (nth i (fst (absorb_i l regs bs)) Int.zero))) /\
    (forall i, (i < 8)%nat ->
       Mem.load Mint32 m' bo (obase + 4 * Z.of_nat i) =
         Some (Vint (nth i (snd (absorb_i l regs bs)) Int.zero))) /\
    (forall ch b ofs, Mem.valid_block m b ->
       (b <> bx \/ ofs + size_chunk ch <= cbase + 8 \/ cbase + 81 <= ofs) ->
       (b <> bo \/ ofs + size_chunk ch <= obase \/ obase + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros Hcb HcM Hob HoM Hox Hgx Hgo Hr HOut HCnt HMod HOvf HBlk HRegs Hdisp HMax HPerm HAl bs ovf'.
  destruct (Mem.alloc m 0 4) as [m1 bb] eqn:A1.
  pose proof (mext_alloc _ _ _ _ _ A1) as (XV & XL & XP & XA).
  assert (Fb : forall b0, Mem.valid_block m b0 -> b0 <> bb).
  { intros b0 Hv Heq. subst b0. exact (Mem.fresh_block_alloc _ _ _ _ _ A1 Hv). }
  assert (Vx : Mem.valid_block m bx) by (eapply jet_bitmachine_rep.load_valid_block; exact HOut).
  assert (Vo : Mem.valid_block m bo).
  { destruct (HRegs 0%nat ltac:(lia)) as [HL0 _]. eapply jet_bitmachine_rep.load_valid_block; exact HL0. }
  assert (VG : Mem.valid_block m (sha_symbol_block _simplicity_sha256_compression))
    by (eapply jet_bitmachine_rep.load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m (sha_symbol_block _sha256_max_counter))
    by (eapply jet_bitmachine_rep.load_valid_block; exact HMax).
  assert (PB1 : Mem.range_perm m1 bb 0 4 Cur Freeable).
  { intros ofs Hr0. eapply Mem.perm_alloc_2; eauto. }
  destruct (eval_sha_WriteBE32 m1 bb Ptrofs.zero x
    ltac:(change (Ptrofs.unsigned Ptrofs.zero) with 0; change Ptrofs.max_unsigned with 18446744073709551615; lia))
    as (m2 & HW & HB2 & HF2 & HP2 & HV2).
  { change (Ptrofs.unsigned Ptrofs.zero) with 0. intros ofs Hr0.
    eapply Mem.perm_implies with (p1 := Freeable); [apply PB1; lia|constructor]. }
  change (Ptrofs.unsigned Ptrofs.zero) with 0 in HB2, HF2.
  assert (K2 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m2 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. rewrite HF2 by (left; apply Fb; exact Hv). apply XL. exact Hv. }
  pose proof (eval_sha256_uchars Hmodel m2 bx cbase bo obase bb Ptrofs.zero l regs bs c ovf
    Hcb HcM Hob HoM Hox (not_eq_sym (Fb bx Vx)) (not_eq_sym (Fb bo Vo)) Hgx Hgo) as HU.
  cbv zeta in HU.
  destruct HU as (m3 & HUc & HOut3 & HCnt3 & HOvf3 & HBlk3 & HReg3 & HMem3 & HPerm3 & HVal3).
  { change (Ptrofs.unsigned Ptrofs.zero) with 0. cbn [bs c_be32_bytes length].
    change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  { exact Hr. }
  { rewrite K2 by exact Vx. exact HOut. }
  { rewrite K2 by exact Vx. exact HCnt. }
  { exact HMod. }
  { rewrite K2 by exact Vx. exact HOvf. }
  { intros i Hi. rewrite K2 by exact Vx. apply HBlk. exact Hi. }
  { intros i Hi. destruct (HRegs i Hi) as [HL0 [Pr Al]]. split.
    - rewrite K2 by exact Vo. exact HL0.
    - split; [|exact Al]. intros ofs Hr0. apply HP2, XP, Pr, Hr0. }
  { intros i Hi. change (Ptrofs.unsigned Ptrofs.zero) with 0. apply HB2. exact Hi. }
  { unfold sha_dispatch_ok. rewrite K2 by exact VG. exact Hdisp. }
  { rewrite K2 by exact VM. exact HMax. }
  { intros ofs Hr0. apply HP2, XP, HPerm, Hr0. }
  { exact HAl. }
  change (Z.of_nat (length bs)) with 4 in HUc, HCnt3, HOvf3. fold ovf' in HUc, HOvf3.
  assert (Vb2 : Mem.valid_block m2 bb) by (apply HV2; eapply Mem.valid_new_block; exact A1).
  destruct (free_list_blocks [(bb, 0, 4)] m3) as (mf & HFL & HLf & HPf & HVf).
  { intros b0 lo hi [Heq|[]]. injection Heq as <- <- <-. intros ofs Hr0.
    apply HPerm3; [exact Vb2|]. apply HP2, PB1, Hr0. }
  { repeat constructor; cbn; tauto. }
  cbn [map fst] in HLf, HPf.
  assert (HNb : forall b0, Mem.valid_block m b0 -> ~ In b0 [bb]).
  { intros b0 Hv [Heq|[]]. exact (Fb b0 Hv (eq_sym Heq)). }
  assert (V2 : forall b0, Mem.valid_block m b0 -> Mem.valid_block m2 b0).
  { intros b0 Hv. apply HV2, XV, Hv. }
  exists mf. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - eapply eval_funcall_internal with (e := u32_env bb) (le1 := u32_temps bx cbase x) (m1 := m1)
      (le2 := PTree.set _t'1 (Vint (bit_int (negb ovf'))) (u32_temps bx cbase x)) (m2 := m3)
      (out := Out_return (Some (Vint (bit_int (negb ovf')), tbool))).
    + apply u32_entry; exact A1.
    + cbn [f_sha256_u32be fn_body].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := u32_temps bx cbase x) (m1 := m2).
      { change (u32_temps bx cbase x) with (set_opttemp None Vundef (u32_temps bx cbase x)) at 2.
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _WriteBE32) Ptrofs.zero)
          (vargs := [Vptr bb Ptrofs.zero; Vlong x]) (f := Internal f_WriteBE32).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_WriteBE32_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs.
          + eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity].
          + reflexivity.
          + eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|apply eval_Enil].
        - exact sha_WriteBE32_funct.
        - reflexivity.
        - exact HW. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      { change (PTree.set _t'1 (Vint (bit_int (negb ovf'))) (u32_temps bx cbase x)) with
          (set_opttemp (Some _t'1) (Vint (bit_int (negb ovf'))) (u32_temps bx cbase x)).
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_uchars) Ptrofs.zero)
          (vargs := [Vptr bx (Ptrofs.repr cbase); Vptr bb Ptrofs.zero; Vlong (Int64.repr 4)])
          (f := Internal f_sha256_uchars).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_uchars_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
          eapply eval_Econs.
          + eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity].
          + reflexivity.
          + eapply eval_Econs; [apply eval_Esizeof|reflexivity|apply eval_Enil].
        - exact sha_uchars_funct.
        - reflexivity.
        - exact HUc. }
      apply exec_Sreturn_some. apply eval_Etempvar. apply PTree.gss.
    + cbn. split; [discriminate|]. destruct ovf'; reflexivity.
    + rewrite u32_blocks. exact HFL.
  - rewrite HLf by (apply HNb; exact Vx). exact HOut3.
  - rewrite HLf by (apply HNb; exact Vx). exact HCnt3.
  - rewrite HLf by (apply HNb; exact Vx). exact HOvf3.
  - intros i Hi. rewrite HLf by (apply HNb; exact Vx). apply HBlk3. exact Hi.
  - intros i Hi. rewrite HLf by (apply HNb; exact Vo). apply HReg3. exact Hi.
  - intros ch b0 ofs Hv Hc1 Hc2. rewrite HLf by (apply HNb; exact Hv).
    rewrite HMem3; [apply K2; exact Hv|apply V2; exact Hv|exact Hc1|exact Hc2].
  - intros b0 ofs k p Hv Hp. apply HPf; [apply HNb; exact Hv|].
    apply HPerm3; [apply V2; exact Hv|]. apply HP2, XP, Hp.
  - intros b0 Hv. apply HVf, HVal3, V2, Hv.
Qed.
