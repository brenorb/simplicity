(** Complete execution of [sha256_uchar(ctx, x)] in the SHA translation
    unit: the byte is spilled to an addressable local and absorbed by
    [sha256_uchars].  Conditional on the explicit [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_ctx8_model.
Require Import C.jet_sha_compress_uchar C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec.
Require Import C.jet_sha_add_n_calls.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Definition uch_env (bv : block) : env := PTree.set _x (bv, tuchar) empty_env.

Lemma uch_blocks bv : blocks_of_env sha_ge (uch_env bv) = [(bv, 0, 1)].
Proof. reflexivity. Qed.

Local Opaque sha_ge.

Theorem eval_sha256_uchar (Hmodel : memcpy_model) m bx cbase bo obase
    (l regs : list int) (x : int) (c : int64) (ovf : bool) :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned -> 0 <= obase -> obase + 32 <= Ptrofs.max_unsigned ->
  bo <> bx ->
  sha_symbol_block _simplicity_sha256_compression <> bx ->
  sha_symbol_block _simplicity_sha256_compression <> bo ->
  Int.zero_ext 8 x = x ->
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
  let vn := Int64.repr 1 in
  let ovf' := uc_overflow ovf c vn in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_uchar)
      [Vptr bx (Ptrofs.repr cbase); Vint x] E0 m' (Vint (bit_int (negb ovf'))) /\
    Mem.load Mptr m' bx cbase = Some (Vptr bo (Ptrofs.repr obase)) /\
    Mem.load Mint64 m' bx (cbase + 8) = Some (Vlong (Int64.add c vn)) /\
    Mem.load Mint8unsigned m' bx (cbase + 80) = Some (Vint (bit_int ovf')) /\
    (forall i, (i < length (fst (absorb_i l regs [x])))%nat ->
       Mem.load Mint8unsigned m' bx (cbase + 16 + Z.of_nat i) =
         Some (Vint (nth i (fst (absorb_i l regs [x])) Int.zero))) /\
    (forall i, (i < 8)%nat ->
       Mem.load Mint32 m' bo (obase + 4 * Z.of_nat i) =
         Some (Vint (nth i (snd (absorb_i l regs [x])) Int.zero))) /\
    (forall ch b ofs, Mem.valid_block m b ->
       (b <> bx \/ ofs + size_chunk ch <= cbase + 8 \/ cbase + 81 <= ofs) ->
       (b <> bo \/ ofs + size_chunk ch <= obase \/ obase + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros Hcb HcM Hob HoM Hox Hgx Hgo Hx Hr HOut HCnt HMod HOvf HBlk HRegs Hdisp HMax HPerm HAl vn ovf'.
  set (G := sha_symbol_block _simplicity_sha256_compression) in *.
  set (MAXC := sha_symbol_block _sha256_max_counter) in *.
  assert (Vx : Mem.valid_block m bx) by (eapply load_valid_block; exact HOut).
  assert (Vo : Mem.valid_block m bo) by (eapply load_valid_block; exact (proj1 (HRegs 0%nat ltac:(lia)))).
  assert (VG : Mem.valid_block m G) by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m MAXC) by (eapply load_valid_block; exact HMax).
  destruct (Mem.alloc m 0 1) as [m1 bv] eqn:AL.
  assert (Fv : forall b, Mem.valid_block m b -> b <> bv).
  { intros b Hv Heq. subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ AL Hv). }
  assert (PV1 : Mem.range_perm m1 bv 0 1 Cur Freeable).
  { intros ofs Hr0. eapply Mem.perm_alloc_2; [exact AL|exact Hr0]. }
  assert (VA : Mem.valid_access m1 Mint8unsigned bv 0 Writable).
  { split; [|exists 0; reflexivity]. intros ofs Hr0. change (size_chunk Mint8unsigned) with 1 in Hr0.
    eapply Mem.perm_implies; [apply PV1; lia|constructor]. }
  destruct (Mem.valid_access_store m1 Mint8unsigned bv 0 (Vint x) VA) as [m2 ST].
  assert (L2 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m2 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hv. rewrite (Mem.load_store_other _ _ _ _ _ _ ST) by (left; apply Fv; exact Hv).
    eapply Mem.load_alloc_unchanged; [exact AL|exact Hv]. }
  assert (P2 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m2 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact ST|]. eapply Mem.perm_alloc_1; [exact AL|exact Hp]. }
  assert (V2 : forall b, Mem.valid_block m b -> Mem.valid_block m2 b).
  { intros b Hv. eapply Mem.store_valid_block_1; [exact ST|]. eapply Mem.valid_block_alloc; [exact AL|exact Hv]. }
  assert (Vv2 : Mem.valid_block m2 bv).
  { eapply Mem.store_valid_block_1; [exact ST|]. eapply Mem.valid_new_block; exact AL. }
  pose proof (eval_sha256_uchars Hmodel m2 bx cbase bo obase bv Ptrofs.zero l regs [x] c ovf
    Hcb HcM Hob HoM Hox (not_eq_sym (Fv bx Vx)) (not_eq_sym (Fv bo Vo)) Hgx Hgo) as HU.
  cbv zeta in HU.
  destruct HU as (m3 & HUc & HOut3 & HCnt3 & HOvf3 & HBlk3 & HReg3 & HMem3 & HPerm3 & HVal3).
  { change (Ptrofs.unsigned Ptrofs.zero) with 0. cbn [length].
    change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  { exact Hr. }
  { rewrite L2 by exact Vx. exact HOut. }
  { rewrite L2 by exact Vx. exact HCnt. }
  { exact HMod. }
  { rewrite L2 by exact Vx. exact HOvf. }
  { intros i Hi. rewrite L2 by exact Vx. apply HBlk. exact Hi. }
  { intros i Hi. destruct (HRegs i Hi) as [HLd [HPm HAlg]]. split.
    - rewrite L2 by exact Vo. exact HLd.
    - split; [|exact HAlg]. intros ofs Hr0. apply P2, HPm, Hr0. }
  { intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i.
    change (Ptrofs.unsigned Ptrofs.zero + Z.of_nat 0) with 0. cbn [nth].
    rewrite (Mem.load_store_same _ _ _ _ _ _ ST). cbn [Val.load_result]. rewrite Hx. reflexivity. }
  { unfold sha_dispatch_ok. fold G. rewrite L2 by exact VG. exact Hdisp. }
  { fold MAXC. rewrite L2 by exact VM. exact HMax. }
  { intros ofs Hr0. apply P2, HPerm, Hr0. }
  { exact HAl. }
  assert (PV3 : Mem.range_perm m3 bv 0 1 Cur Freeable).
  { intros ofs Hr0. apply HPerm3; [exact Vv2|]. eapply Mem.perm_store_1; [exact ST|]. apply PV1, Hr0. }
  destruct (Mem.range_perm_free m3 bv 0 1 PV3) as [mf FR].
  assert (LF : forall ch b ofs, b <> bv -> Mem.load ch mf b ofs = Mem.load ch m3 b ofs).
  { intros ch b ofs Hb. eapply Mem.load_free; [exact FR|left; exact Hb]. }
  exists mf.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - eapply eval_funcall_internal with (e := uch_env bv) (m1 := m1)
      (le1 := PTree.set _x (Vint x) (PTree.set _ctx (Vptr bx (Ptrofs.repr cbase))
        (create_undef_temps (fn_temps f_sha256_uchar))))
      (le2 := PTree.set _t'1 (Vint (bit_int (negb ovf')))
        (PTree.set _x (Vint x) (PTree.set _ctx (Vptr bx (Ptrofs.repr cbase))
          (create_undef_temps (fn_temps f_sha256_uchar)))))
      (m2 := m3) (out := Out_return (Some (Vint (bit_int (negb ovf')), tbool))).
    + apply function_entry2_intro.
      * cbn. repeat constructor; cbn; intuition discriminate.
      * cbn. repeat constructor; cbn; intuition discriminate.
      * intros a b HA HB Hab. cbn in HA, HB.
        repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
          first [contradiction | vm_compute in Hab; discriminate | congruence].
      * eapply alloc_variables_cons with (m1 := m1) (b1 := bv);
          [change (Mem.alloc m 0 1 = (m1, bv)); exact AL|constructor].
      * reflexivity.
    + cbn [f_sha256_uchar fn_body].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2).
      { eapply exec_Sassign with (v2 := Vint x) (v := Vint x).
        - apply eval_Evar_local; reflexivity.
        - apply eval_Etempvar; reflexivity.
        - change (Some (Vint (Int.zero_ext 8 x)) = Some (Vint x)). rewrite Hx. reflexivity.
        - eapply assign_loc_value; [reflexivity|exact ST]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m3).
      { eapply exec_Scall with (optid := Some _t'1)
          (vf := Vptr (sha_symbol_block _sha256_uchars) Ptrofs.zero)
          (vargs := [Vptr bx (Ptrofs.repr cbase); Vptr bv Ptrofs.zero; Vlong (Int64.repr 1)])
          (f := Internal f_sha256_uchars).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact an_uchars_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
          eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
          eapply eval_Econs; [apply eval_Econst_int|vm_compute; reflexivity|apply eval_Enil].
        - exact an_uchars_funct.
        - reflexivity.
        - exact HUc. }
      apply exec_Sreturn_some. apply eval_Etempvar. apply PTree.gss.
    + cbn. split; [discriminate|]. destruct (negb ovf'); reflexivity.
    + rewrite uch_blocks. cbn [Mem.free_list]. rewrite FR. reflexivity.
  - rewrite LF by (apply Fv; exact Vx). exact HOut3.
  - rewrite LF by (apply Fv; exact Vx). exact HCnt3.
  - rewrite LF by (apply Fv; exact Vx). exact HOvf3.
  - intros i Hi. rewrite LF by (apply Fv; exact Vx). apply HBlk3. exact Hi.
  - intros i Hi. rewrite LF by (apply Fv; exact Vo). apply HReg3. exact Hi.
  - intros ch b ofs Hv H1 H2. rewrite LF by (apply Fv; exact Hv).
    rewrite (HMem3 ch b ofs (V2 b Hv) H1 H2). apply L2. exact Hv.
  - intros b ofs k p Hv Hp. eapply Mem.perm_free_1; [exact FR|left; apply Fv; exact Hv|].
    apply HPerm3; [apply V2; exact Hv|apply P2; exact Hp].
  - intros b Hv. eapply Mem.valid_block_free_1; [exact FR|]. apply HVal3, V2, Hv.
Qed.
