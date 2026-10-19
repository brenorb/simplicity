(** Execution of [copyInput(result, input)] (bitcoin/env.c), complete: the
    compound literal, the optional annex hash, the previous transaction id,
    the spent output ([copyOutput]) and the scriptSig hash. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_bitmachine_rep C.jet_uint32_array_init.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_ctx8_model C.jet_sha_compress_call.
Require Import C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_sha_add_n_init C.jet_sha_add_n_calls.
Require Import C.jet_sha_tapdata_prep C.jet_sha_ctx_abs.
Require Import C.jet_env_store_words C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_tomidstate.
Require Import C.jet_bitcoin_env_hashbuffer C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_key.
Require Import C.jet_bitcoin_env_tapenv_fill C.jet_bitcoin_env_copyoutput C.jet_bitcoin_env_copyinput_fill.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 600.

Definition ci_env (bCmp : block) : env := PTree.set ___compound (bCmp, SIN) empty_env.

Lemma ci_blocks bCmp : blocks_of_env sha_ge (ci_env bCmp) = [(bCmp, 0, 160)].
Proof. vm_compute. reflexivity. Qed.

Lemma sha_copyOutput_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _copyOutput = Some (sha_symbol_block _copyOutput).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_copyOutput_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _copyOutput) Ptrofs.zero) =
    Some (Internal f_copyOutput).
Proof. vm_compute; reflexivity. Qed.

Lemma ci_entry m m1 bCmp vres vin :
  Mem.alloc m 0 160 = (m1, bCmp) ->
  function_entry2 sha_ge f_copyInput [vres; vin] m (ci_env bCmp)
    (PTree.set _input vin (PTree.set _result vres (create_undef_temps (fn_temps f_copyInput)))) m1.
Proof.
  intros A1. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst; try contradiction; discriminate.
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bCmp); [rewrite ci_sizeof_SIN; exact A1|].
    constructor.
  - reflexivity.
Qed.

Local Opaque sha_ge.

Lemma ci_call_hashBuffer e le m m' (a1 a2 : expr) b1 o1 b2 o2 :
  e!_hashBuffer = None ->
  eval_expr sha_ge e le m a1 (Vptr b1 o1) -> typeof a1 = tptr MID ->
  eval_expr sha_ge e le m a2 (Vptr b2 o2) -> typeof a2 = tptr RBUF ->
  Clight2.eval_funcall sha_ge m (Internal f_hashBuffer) [Vptr b1 o1; Vptr b2 o2] E0 m' Vundef ->
  Clight2.exec_stmt sha_ge e le m
    (Scall None (Evar _hashBuffer (Tfunction (Tcons (tptr MID) (Tcons (tptr RBUF) Tnil)) tvoid cc_default))
       [a1; a2]) E0 le m' Out_normal.
Proof.
  intros He H1 T1 H2 T2 HC. change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _hashBuffer) Ptrofs.zero)
    (vargs := [Vptr b1 o1; Vptr b2 o2]) (f := Internal f_hashBuffer).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact sha_hashBuffer_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [exact H1|rewrite T1; reflexivity|].
    eapply eval_Econs; [exact H2|rewrite T2; reflexivity|apply eval_Enil].
  - exact sha_hashBuffer_funct.
  - reflexivity.
  - exact HC.
Qed.

Lemma ci_call_copyOutput e le m m' (a1 a2 : expr) b1 o1 b2 o2 :
  e!_copyOutput = None ->
  eval_expr sha_ge e le m a1 (Vptr b1 o1) -> typeof a1 = tptr SOUT ->
  eval_expr sha_ge e le m a2 (Vptr b2 o2) -> typeof a2 = tptr ROUT ->
  Clight2.eval_funcall sha_ge m (Internal f_copyOutput) [Vptr b1 o1; Vptr b2 o2] E0 m' Vundef ->
  Clight2.exec_stmt sha_ge e le m
    (Scall None (Evar _copyOutput (Tfunction (Tcons (tptr SOUT) (Tcons (tptr ROUT) Tnil)) tvoid cc_default))
       [a1; a2]) E0 le m' Out_normal.
Proof.
  intros He H1 T1 H2 T2 HC. change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _copyOutput) Ptrofs.zero)
    (vargs := [Vptr b1 o1; Vptr b2 o2]) (f := Internal f_copyOutput).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact sha_copyOutput_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [exact H1|rewrite T1; reflexivity|].
    eapply eval_Econs; [exact H2|rewrite T2; reflexivity|apply eval_Enil].
  - exact sha_copyOutput_funct.
  - reflexivity.
  - exact HC.
Qed.

(** A raw buffer structure at [(b, o)]: data pointer, length, bytes. *)
Definition raw_buffer_at (m : mem) (b : block) (o : Z) (bd : block) (od : ptrofs) (bs : list int) : Prop :=
  exists len,
    Mem.load Mptr m b o = Some (Vptr bd od) /\
    Mem.load Mint32 m b (o + 8) = Some (Vint len) /\
    Z.of_nat (length bs) = Int.unsigned len /\
    Ptrofs.unsigned od + Z.of_nat (length bs) <= Ptrofs.max_unsigned /\
    Mem.valid_block m bd /\
    (forall i, (i < length bs)%nat ->
       Mem.load Mint8unsigned m bd (Ptrofs.unsigned od + Z.of_nat i) = Some (Vint (nth i bs Int.zero))).

Lemma raw_buffer_at_frame m m' b o bd od bs :
  raw_buffer_at m b o bd od bs ->
  (forall ch b' ofs, b' = b \/ b' = bd -> Mem.load ch m' b' ofs = Mem.load ch m b' ofs) ->
  (forall b', Mem.valid_block m b' -> Mem.valid_block m' b') ->
  raw_buffer_at m' b o bd od bs.
Proof.
  intros (len & H1 & H2 & H3 & H4 & H5 & H6) HL HV. exists len.
  rewrite !HL by tauto. repeat (split; [assumption|]). split; [apply HV, H5|].
  intros i Hi. rewrite HL by tauto. apply H6, Hi.
Qed.

Section CopyInput.
Variable Hmodel : memcpy_model.
Variables (bres bin : block) (ores oin : Z).
Hypothesis Hores : 0 <= ores /\ ores + 160 <= Ptrofs.max_unsigned.
Hypothesis HoA : (8 | ores).
Hypothesis Hoin : 0 <= oin /\ oin + 64 <= Ptrofs.max_unsigned.
Hypothesis NGr : bres <> GC.
Hypothesis NMr : bres <> GM.
Hypothesis Nir : bin <> bres.

(** The annex pointer, the stored flag and the stored annex hash. *)
Definition annex_spec (m : mem) (vannex : val) (hasv : int) (areg : list int) : Prop :=
  (vannex = Vlong Int64.zero /\ hasv = Int.zero /\ areg = repeat Int.zero 8) \/
  (exists bax oax bad oad abs,
     vannex = Vptr bax oax /\ hasv = Int.one /\ areg = hash_buffer_regs abs /\
     Ptrofs.unsigned oax + 16 <= Ptrofs.max_unsigned /\ bax <> bres /\ bad <> bres /\
     raw_buffer_at m bax (Ptrofs.unsigned oax) bad oad abs).

Lemma ev_res_addr e le m f delta ty :
  le!_result = Some (Vptr bres (Ptrofs.repr ores)) -> envu_field_at _sigInput f delta -> 0 <= delta <= 160 ->
  eval_expr sha_ge e le m
    (Eaddrof (Efield (Ederef (Etempvar _result (tptr SIN)) SIN) f ty) (tptr ty))
    (Vptr bres (Ptrofs.repr (ores + delta))).
Proof.
  intros Hle Hf Hd. rewrite <- envu_ptr_add_repr by lia.
  eapply eval_Eaddrof. eapply eval_envu_field_lvalue; [reflexivity|exact Hf|apply eval_envu_deref_struct; exact Hle].
Qed.

Lemma ev_in_addr e le m f delta ty :
  le!_input = Some (Vptr bin (Ptrofs.repr oin)) -> envu_field_at _rawInput f delta -> 0 <= delta <= 64 ->
  eval_expr sha_ge e le m
    (Eaddrof (Efield (Ederef (Etempvar _input (tptr RIN)) RIN) f ty) (tptr ty))
    (Vptr bin (Ptrofs.repr (oin + delta))).
Proof.
  intros Hle Hf Hd. rewrite <- envu_ptr_add_repr by lia.
  eapply eval_Eaddrof. eapply eval_envu_field_lvalue; [reflexivity|exact Hf|apply eval_envu_deref_struct; exact Hle].
Qed.

Lemma ev_in_field e le m f delta ty chunk v :
  le!_input = Some (Vptr bin (Ptrofs.repr oin)) -> envu_field_at _rawInput f delta -> 0 <= delta <= 64 ->
  access_mode ty = By_value chunk -> Mem.load chunk m bin (oin + delta) = Some v ->
  eval_expr sha_ge e le m (Efield (Ederef (Etempvar _input (tptr RIN)) RIN) f ty) v.
Proof.
  intros Hle Hf Hd Hacc HL. eapply eval_envu_field_value;
    [reflexivity|exact Hf|exact Hacc|apply eval_envu_deref_struct; exact Hle|].
  rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|exact HL].
Qed.

Theorem eval_copyInput m (vannex : val) (hasv : int) (areg : list int)
    btx otx (txb : list int) (value : int64) bsp osp (spb : list int) bss oss (ssb : list int) (ix sq : int) :
  Mem.range_perm m bres ores (ores + 160) Cur Writable ->
  Mem.load Mptr m bin oin = Some vannex ->
  annex_spec m vannex hasv areg ->
  Mem.load Mptr m bin (oin + 8) = Some (Vptr btx otx) -> btx <> bres ->
  Ptrofs.unsigned otx + 32 <= Ptrofs.max_unsigned ->
  (forall i, (i < 32)%nat ->
     Mem.load Mint8unsigned m btx (Ptrofs.unsigned otx + Z.of_nat i) = Some (Vint (nth i txb Int.zero))) ->
  Mem.load Mint64 m bin (oin + 16) = Some (Vlong value) ->
  raw_buffer_at m bin (oin + 24) bsp osp spb -> bsp <> bres ->
  raw_buffer_at m bin (oin + 40) bss oss ssb -> bss <> bres ->
  Mem.load Mint32 m bin (oin + 56) = Some (Vint ix) ->
  Mem.load Mint32 m bin (oin + 60) = Some (Vint sq) ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_copyInput)
      [Vptr bres (Ptrofs.repr ores); Vptr bin (Ptrofs.repr oin)] E0 m' Vundef /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 m' bres (ores + 4 * Z.of_nat j) = Some (Vint (nth j areg Int.zero))) /\
    (forall j, (j < 8)%nat ->
       Mem.load Mint32 m' bres (ores + 32 + 4 * Z.of_nat j) = Some (Vint (nth j (hash_buffer_regs ssb) Int.zero))) /\
    (forall j, (j < 8)%nat ->
       Mem.load Mint32 m' bres (ores + 64 + 4 * Z.of_nat j) = Some (Vint (nth j (tm_words txb) Int.zero))) /\
    Mem.load Mint64 m' bres (ores + 96) = Some (Vlong (Int64.repr (Int.unsigned ix))) /\
    Mem.load Mint64 m' bres (ores + 104) = Some (Vlong value) /\
    (forall j, (j < 8)%nat ->
       Mem.load Mint32 m' bres (ores + 112 + 4 * Z.of_nat j) = Some (Vint (nth j (hash_buffer_regs spb) Int.zero))) /\
    Mem.load Mint64 m' bres (ores + 144) = Some (Vlong (Int64.repr (Int.unsigned sq))) /\
    Mem.load Mint8unsigned m' bres (ores + 152) = Some (Vint hasv) /\
    (forall ch b ofs, Mem.valid_block m b ->
       (b <> bres \/ ofs + size_chunk ch <= ores \/ ores + 160 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros PR HAnx HAn HTx Ntx HtxM HTxB HVal HSpk Nsp HSsg Nss HIx HSq Hdisp HMax.
  assert (VG : Mem.valid_block m GC) by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m GM) by (eapply load_valid_block; exact HMax).
  assert (Vin : Mem.valid_block m bin) by (eapply load_valid_block; exact HAnx).
  assert (Vres : Mem.valid_block m bres) by (eapply Mem.perm_valid_block; apply (PR ores); lia).
  assert (Vtx : Mem.valid_block m btx) by (eapply load_valid_block; exact (HTxB 0%nat ltac:(lia))).
  destruct (Mem.alloc m 0 160) as [m0 bCmp] eqn:A1.
  assert (NC : forall b, Mem.valid_block m b -> b <> bCmp).
  { intros b Hb E. subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ A1 Hb). }
  assert (L0 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m0 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. eapply Mem.load_alloc_unchanged; [exact A1|exact Hb]. }
  assert (P0 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m0 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_alloc_1; [exact A1|exact Hp]. }
  assert (V0 : forall b, Mem.valid_block m b -> Mem.valid_block m0 b).
  { intros b Hb. eapply Mem.valid_block_alloc; [exact A1|exact Hb]. }
  assert (PC0 : Mem.range_perm m0 bCmp 0 160 Cur Freeable).
  { intros o Ho. eapply Mem.perm_alloc_2; [exact A1|exact Ho]. }
  set (e := ci_env bCmp).
  set (le0 := PTree.set _input (Vptr bin (Ptrofs.repr oin))
    (PTree.set _result (Vptr bres (Ptrofs.repr ores)) (create_undef_temps (fn_temps f_copyInput)))).
  (* the compound literal *)
  assert (HAn0 : (vannex = Vlong Int64.zero /\ hasv = Int.zero) \/
    (exists ba oa, vannex = Vptr ba oa /\ Mem.perm m0 ba (Ptrofs.unsigned oa) Cur Nonempty /\ hasv = Int.one)).
  { destruct HAn as [(-> & -> & _)|(bax & oax & bad & oad & abs & -> & -> & _ & _ & _ & _ & (len & HB & _))].
    - left. split; reflexivity.
    - right. exists bax, oax. split; [reflexivity|]. split; [|reflexivity].
      apply P0. apply Mem.load_valid_access in HB. destruct HB as [HR _].
      eapply Mem.perm_implies; [apply HR; change (size_chunk Mptr) with 8; lia|constructor]. }
  destruct (ci_fill_exec e bCmp bres bin ores oin ix sq hasv vannex eq_refl Hores HoA Hoin
    (not_eq_sym (NC _ Vres)) (NC _ Vin) le0 m0 eq_refl eq_refl)
    as (mG & le1 & (HZ & HIxG & HSqG & HHasG) & HlR & HlI & LG & PG & VGm & KG).
  { rewrite L0 by exact Vin. exact HAnx. }
  { rewrite L0 by exact Vin. exact HIx. }
  { rewrite L0 by exact Vin. exact HSq. }
  { exact HAn0. }
  { intros o Ho. eapply Mem.perm_implies; [apply PC0, Ho|constructor]. }
  { intros o Ho. apply P0, PR, Ho. }
  assert (KoldG : forall ch b ofs, Mem.valid_block m b -> b <> bres -> Mem.load ch mG b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb Hn. rewrite LG; [apply L0, Hb|apply NC, Hb|left; exact Hn]. }
  assert (PRG : Mem.range_perm mG bres ores (ores + 160) Cur Writable).
  { intros o Ho. apply PG, P0, PR, Ho. }
  (* the annex *)
  assert (HS2 : exists m2 le2,
    Clight2.exec_stmt sha_ge e le1 mG
      (match ci_rest with Ssequence s _ => s | _ => Sskip end) E0 le2 m2 Out_normal /\
    le2!_result = Some (Vptr bres (Ptrofs.repr ores)) /\ le2!_input = Some (Vptr bin (Ptrofs.repr oin)) /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 m2 bres (ores + 4 * Z.of_nat j) = Some (Vint (nth j areg Int.zero))) /\
    (forall ch b ofs, Mem.valid_block mG b ->
       (b <> bres \/ ofs + size_chunk ch <= ores \/ ores + 32 <= ofs) ->
       Mem.load ch m2 b ofs = Mem.load ch mG b ofs) /\
    (forall b ofs k p, Mem.perm mG b ofs k p -> Mem.perm m2 b ofs k p) /\
    (forall b, Mem.valid_block mG b -> Mem.valid_block m2 b)).
  { cbv delta [ci_rest] beta iota.
    destruct HAn as [(-> & -> & ->)|(bax & oax & bad & oad & abs & -> & -> & -> & HoaxM & Nax & Nad & HRB)].
    - exists mG, (PTree.set _t'2 (Vlong Int64.zero) le1).
      split.
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := PTree.set _t'2 (Vlong Int64.zero) le1) (m1 := mG).
        - apply exec_Sset. eapply ev_in_field with (delta := 0) (chunk := Mptr);
            [exact HlI|exact envu_rawInput_annex|lia|reflexivity|].
          rewrite Z.add_0_r, KoldG by assumption. exact HAnx.
        - eapply exec_Sifthenelse with (v1 := Vlong Int64.zero) (b := false).
          + apply eval_Etempvar. apply PTree.gss.
          + reflexivity.
          + apply exec_Sskip. }
      rewrite !PTree.gso by discriminate. split; [exact HlR|]. split; [exact HlI|].
      split; [intros j Hj; rewrite nth_repeat; apply HZ, Hj|]. split; [reflexivity|]. split; auto.
    - destruct HRB as (alen & HB1 & HB2 & HB3 & HB4 & HB5 & HB6).
      assert (Vax : Mem.valid_block m bax) by (eapply load_valid_block; exact HB1).
      destruct (eval_hashBuffer Hmodel mG bres (ores + 0) bax oax bad oad abs alen
        ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; destruct HoA as [q ->]; exists (2 * q); lia))
        as (m2 & HCall & HReg & HL2 & HP2 & HV2); try assumption.
      { intros o Ho. apply PRG. lia. }
      { apply VGm, V0, HB5. }
      { rewrite KoldG by assumption. exact HB1. }
      { rewrite KoldG by assumption. exact HB2. }
      { intros i Hi. rewrite KoldG by assumption. apply HB6, Hi. }
      { unfold sha_dispatch_ok. rewrite KoldG; [exact Hdisp|exact VG|congruence]. }
      { rewrite KoldG; [exact HMax|exact VM|congruence]. }
      set (le2 := PTree.set _t'3 (Vptr bax oax) (PTree.set _t'2 (Vptr bax oax) le1)).
      assert (HW : Mem.weak_valid_pointer mG bax (Ptrofs.unsigned oax) = true).
      { unfold Mem.weak_valid_pointer. apply orb_true_iff. left. apply Mem.valid_pointer_nonempty_perm.
        apply PG, P0. apply Mem.load_valid_access in HB1. destruct HB1 as [HR _].
        eapply Mem.perm_implies; [apply HR; change (size_chunk Mptr) with 8; lia|constructor]. }
      exists m2, le2. split.
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := PTree.set _t'2 (Vptr bax oax) le1) (m1 := mG).
        - apply exec_Sset. eapply ev_in_field with (delta := 0) (chunk := Mptr);
            [exact HlI|exact envu_rawInput_annex|lia|reflexivity|].
          rewrite Z.add_0_r, KoldG by assumption. exact HAnx.
        - eapply exec_Sifthenelse with (v1 := Vptr bax oax) (b := true).
          + apply eval_Etempvar. apply PTree.gss.
          + cbn. unfold bool_val. cbn. rewrite HW. reflexivity.
          + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mG).
            * apply exec_Sset. eapply ev_in_field with (delta := 0) (chunk := Mptr);
                [rewrite PTree.gso by discriminate; exact HlI|exact envu_rawInput_annex|lia|reflexivity|].
              rewrite Z.add_0_r, KoldG by assumption. exact HAnx.
            * eapply ci_call_hashBuffer with (b1 := bres) (o1 := Ptrofs.repr (ores + 0)) (b2 := bax) (o2 := oax);
                [reflexivity| |reflexivity| |reflexivity|exact HCall].
              -- apply ev_res_addr; [|exact envu_sigInput_annexHash|lia].
                 unfold le2. rewrite !PTree.gso by discriminate. exact HlR.
              -- apply eval_Etempvar. apply PTree.gss. }
      unfold le2. rewrite !PTree.gso by discriminate. split; [exact HlR|]. split; [exact HlI|].
      split; [intros j Hj; rewrite <- (Z.add_0_r ores) at 1; apply HReg, Hj|].
      split; [intros ch b ofs Hb Hr; apply HL2; [exact Hb|];
              destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; lia|right; right; lia]|].
      split; assumption. }
  destruct HS2 as (m2 & le2 & HEx2 & HlR2 & HlI2 & HAnn2 & HL2 & HP2 & HV2).
  assert (Kold2 : forall ch b ofs, Mem.valid_block m b -> b <> bres -> Mem.load ch m2 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb Hn. rewrite HL2; [apply KoldG; assumption|apply VGm, V0, Hb|left; exact Hn]. }
  (* the previous transaction id *)
  set (otxid := Ptrofs.repr (ores + 64)).
  assert (Hotxid : Ptrofs.unsigned otxid = ores + 64) by (apply Ptrofs.unsigned_repr; lia).
  destruct (eval_sha256_toMidstate bres btx otxid otx txb (not_eq_sym Ntx) HtxM) with (m := m2)
    as (m3 & HSt3 & HCall3).
  { rewrite Hotxid. lia. }
  { rewrite Hotxid. destruct HoA as [q ->]. exists (2 * q + 16). lia. }
  { intros i Hi. rewrite Kold2 by assumption. apply HTxB, Hi. }
  { rewrite Hotxid. intros o Ho. apply HP2, PRG. lia. }
  rewrite Hotxid in HSt3.
  assert (HLenT : length (tm_words txb) = 8%nat) by reflexivity.
  assert (L3 : forall ch b ofs, (b <> bres \/ ofs + size_chunk ch <= ores + 64 \/ ores + 96 <= ofs) ->
    Mem.load ch m3 b ofs = Mem.load ch m2 b ofs).
  { intros ch b ofs Hc. apply (store_words_load_other _ _ _ _ _ HSt3). rewrite HLenT.
    destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc|right; left; exact Hc|right; right; lia]. }
  assert (P3 : forall b ofs k p, Mem.perm m2 b ofs k p -> Mem.perm m3 b ofs k p).
  { intros b ofs k p Hp. apply (store_words_perm _ _ _ _ _ HSt3). exact Hp. }
  assert (V3 : forall b, Mem.valid_block m2 b -> Mem.valid_block m3 b).
  { intros b Hb. unfold Mem.valid_block. rewrite (store_words_nextblock _ _ _ _ _ HSt3). exact Hb. }
  assert (Kold3 : forall ch b ofs, Mem.valid_block m b -> b <> bres -> Mem.load ch m3 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb Hn. rewrite L3 by (left; exact Hn). apply Kold2; assumption. }
  assert (Vold3 : forall b, Mem.valid_block m b -> Mem.valid_block m3 b).
  { intros b Hb. apply V3, HV2, VGm, V0, Hb. }
  assert (PR3 : Mem.range_perm m3 bres ores (ores + 160) Cur Writable).
  { intros o Ho. apply P3, HP2, PRG, Ho. }
  (* the spent output *)
  destruct HSpk as (splen & HP1 & HP2' & HP3 & HP4 & HP5 & HP6).
  destruct (eval_copyOutput Hmodel m3 bres (ores + 104) bin (oin + 16) bsp osp spb splen value
    ltac:(lia) ltac:(lia) ltac:(destruct HoA as [q ->]; exists (q + 13); lia))
    as (m4 & HCall4 & HVal4 & HSpk4 & HL4 & HP4m & HV4); try assumption; try lia.
  { intros o Ho. apply PR3. lia. }
  { apply Vold3, HP5. }
  { rewrite Kold3 by assumption. exact HVal. }
  { rewrite Kold3 by assumption. replace (oin + 16 + 8) with (oin + 24) by lia. exact HP1. }
  { rewrite Kold3 by assumption. replace (oin + 16 + 16) with (oin + 24 + 8) by lia. exact HP2'. }
  { intros i Hi. rewrite Kold3 by (assumption || exact HP5). apply HP6, Hi. }
  { unfold sha_dispatch_ok. rewrite Kold3; [exact Hdisp|exact VG|congruence]. }
  { rewrite Kold3; [exact HMax|exact VM|congruence]. }
  assert (Kold4 : forall ch b ofs, Mem.valid_block m b -> b <> bres -> Mem.load ch m4 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb Hn. rewrite HL4; [apply Kold3; assumption|apply Vold3, Hb|left; exact Hn]. }
  (* the scriptSig *)
  destruct HSsg as (sslen & HG1 & HG2 & HG3 & HG4 & HG5 & HG6).
  set (obuf := Ptrofs.repr (oin + 40)).
  assert (Hobuf : Ptrofs.unsigned obuf = oin + 40) by (apply Ptrofs.unsigned_repr; lia).
  destruct (eval_hashBuffer Hmodel m4 bres (ores + 32) bin obuf bss oss ssb sslen
    ltac:(lia) ltac:(lia) ltac:(destruct HoA as [q ->]; exists (2 * q + 8); lia))
    as (m5 & HCall5 & HSsg5 & HL5 & HP5m & HV5); try assumption.
  { intros o Ho. apply HP4m, PR3. lia. }
  { apply HV4, Vold3, HG5. }
  { rewrite Hobuf. lia. }
  { rewrite Hobuf, Kold4 by assumption. exact HG1. }
  { rewrite Hobuf, Kold4 by assumption. exact HG2. }
  { intros i Hi. rewrite Kold4 by (assumption || exact HG5). apply HG6, Hi. }
  { unfold sha_dispatch_ok. rewrite Kold4; [exact Hdisp|exact VG|congruence]. }
  { rewrite Kold4; [exact HMax|exact VM|congruence]. }
  (* freeing the local *)
  assert (Pall5 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m5 b ofs k p).
  { intros b ofs k p Hp. apply HP5m, HP4m, P3, HP2, PG, Hp. }
  destruct (free_list_blocks [(bCmp, 0, 160)] m5) as (mf & HFL & HLf & HPf & HVf).
  { intros b lo hi HIn ofs Hr. destruct HIn as [E|[]]. injection E as <- <- <-. apply Pall5, PC0, Hr. }
  { cbn [map fst]. apply NoDup_cons; [intros []|apply NoDup_nil]. }
  cbn [map fst] in HLf, HPf.
  assert (NCl : forall b, Mem.valid_block m b -> ~ In b [bCmp]).
  { intros b Hb [E|[]]. exact (NC b Hb (eq_sym E)). }
  assert (V5 : forall b, Mem.valid_block m b -> Mem.valid_block m5 b).
  { intros b Hb. apply HV5, HV4, Vold3, Hb. }
  assert (Vr3 : Mem.valid_block m3 bres) by (apply Vold3, Vres).
  assert (Vr4 : Mem.valid_block m4 bres) by (apply HV4, Vr3).
  assert (VrG : Mem.valid_block mG bres) by (apply VGm, V0, Vres).
  set (le3 := PTree.set _t'1 (Vptr btx otx) le2).
  assert (HlR3 : le3!_result = Some (Vptr bres (Ptrofs.repr ores))) by (unfold le3; rewrite PTree.gso by discriminate; exact HlR2).
  assert (HlI3 : le3!_input = Some (Vptr bin (Ptrofs.repr oin))) by (unfold le3; rewrite PTree.gso by discriminate; exact HlI2).
  exists mf. split.
  { eapply eval_funcall_internal with (e := e) (le1 := le0) (m1 := m0) (le2 := le3) (m2 := m5) (out := Out_normal).
    - eapply ci_entry. exact A1.
    - apply KG. revert HEx2. cbv delta [ci_rest] beta iota. intros HEx2.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HEx2|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m3).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m2).
        - apply exec_Sset. eapply ev_in_field with (delta := 8) (chunk := Mptr);
            [exact HlI2|exact envu_rawInput_prevTxid|lia|reflexivity|].
          rewrite Kold2 by assumption. exact HTx.
        - eapply te_call_toMidstate with (bm := bres) (om := otxid) (bh := btx) (oh := otx);
            [reflexivity| |reflexivity| |reflexivity|exact HCall3].
          + pose proof (eval_envu_field_array e le3 m2
              (Efield (Efield (Ederef (Etempvar _result (tptr SIN)) SIN) _prevOutpoint OP) _txid MID)
              _sha256_midstate _s 0 A8 bres otxid eq_refl envu_sha256_midstate_s
              ltac:(intros chunk; discriminate) eq_refl) as HE.
            rewrite Ptrofs.add_zero in HE. apply HE.
            pose proof (eval_envu_field_struct e le3 m2
              (Efield (Ederef (Etempvar _result (tptr SIN)) SIN) _prevOutpoint OP) _outpoint _txid 0
              _sha256_midstate bres otxid eq_refl envu_outpoint_txid) as HE2.
            rewrite Ptrofs.add_zero in HE2. apply HE2.
            pose proof (eval_envu_field_struct e le3 m2 (Ederef (Etempvar _result (tptr SIN)) SIN)
              _sigInput _prevOutpoint 64 _outpoint bres (Ptrofs.repr ores) eq_refl envu_sigInput_prevOutpoint
              (eval_envu_deref_struct e le3 m2 _result _sigInput bres (Ptrofs.repr ores) HlR3)) as HE3.
            rewrite envu_ptr_add_repr in HE3 by lia. exact HE3.
          + apply eval_Etempvar. apply PTree.gss. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m4).
      { eapply ci_call_copyOutput with (b1 := bres) (o1 := Ptrofs.repr (ores + 104))
          (b2 := bin) (o2 := Ptrofs.repr (oin + 16)); [reflexivity| |reflexivity| |reflexivity|exact HCall4].
        - apply ev_res_addr; [exact HlR3|exact envu_sigInput_txo|lia].
        - apply ev_in_addr; [exact HlI3|exact envu_rawInput_txo|lia]. }
      eapply ci_call_hashBuffer with (b1 := bres) (o1 := Ptrofs.repr (ores + 32)) (b2 := bin) (o2 := obuf);
        [reflexivity| |reflexivity| |reflexivity|exact HCall5].
      + apply ev_res_addr; [exact HlR3|exact envu_sigInput_scriptSigHash|lia].
      + apply ev_in_addr; [exact HlI3|exact envu_rawInput_scriptSig|lia].
    - cbn. reflexivity.
    - unfold e. rewrite ci_blocks. exact HFL. }
  assert (LAf : forall ch ofs, Mem.load ch mf bres ofs = Mem.load ch m5 bres ofs).
  { intros ch ofs. apply HLf. apply NCl, Vres. }
  split.
  { intros j Hj. rewrite LAf.
    rewrite HL5 by (first [exact Vr4 | right; left; change (size_chunk Mint32) with 4; lia]).
    rewrite HL4 by (first [exact Vr3 | right; left; change (size_chunk Mint32) with 4; lia]).
    rewrite L3 by (right; left; change (size_chunk Mint32) with 4; lia). apply HAnn2, Hj. }
  split; [intros j Hj; rewrite LAf; apply HSsg5, Hj|].
  split.
  { intros j Hj. rewrite LAf.
    rewrite HL5 by (first [exact Vr4 | right; right; lia]).
    rewrite HL4 by (first [exact Vr3 | right; left; change (size_chunk Mint32) with 4; lia]).
    apply (u32_nth m3 bres (ores + 64) (tm_words txb)); [eapply store_words_loads; exact HSt3|exact Hj]. }
  split.
  { rewrite LAf. rewrite HL5 by (first [exact Vr4 | right; right; lia]).
    rewrite HL4 by (first [exact Vr3 | right; left; cbn; lia]).
    rewrite L3 by (right; right; lia). rewrite HL2 by (first [exact VrG | right; right; lia]). exact HIxG. }
  split.
  { rewrite LAf. rewrite HL5 by (first [exact Vr4 | right; right; lia]). exact HVal4. }
  split.
  { intros j Hj. rewrite LAf. rewrite HL5 by (first [exact Vr4 | right; right; lia]).
    replace (ores + 112 + 4 * Z.of_nat j) with (ores + 104 + 8 + 4 * Z.of_nat j) by lia. apply HSpk4, Hj. }
  split.
  { rewrite LAf. rewrite HL5 by (first [exact Vr4 | right; right; lia]).
    rewrite HL4 by (first [exact Vr3 | right; right; lia]).
    rewrite L3 by (right; right; lia). rewrite HL2 by (first [exact VrG | right; right; lia]). exact HSqG. }
  split.
  { rewrite LAf. rewrite HL5 by (first [exact Vr4 | right; right; lia]).
    rewrite HL4 by (first [exact Vr3 | right; right; lia]).
    rewrite L3 by (right; right; lia). rewrite HL2 by (first [exact VrG | right; right; lia]). exact HHasG. }
  split.
  { intros ch b ofs Hb Hr. rewrite HLf by (apply NCl, Hb).
    rewrite HL5; [|apply HV4, Vold3, Hb|destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; lia|right; right; lia]].
    rewrite HL4; [|apply Vold3, Hb|destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; lia|right; right; lia]].
    rewrite L3 by (destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; lia|right; right; lia]).
    rewrite HL2; [|apply VGm, V0, Hb|destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; lia|right; right; lia]].
    rewrite LG; [apply L0, Hb|apply NC, Hb|exact Hr]. }
  split.
  { intros b ofs k p Hp. apply HPf; [apply NCl; eapply Mem.perm_valid_block; exact Hp|apply Pall5, P0, Hp]. }
  intros b Hb. apply HVf, V5, Hb.
Qed.
End CopyInput.
