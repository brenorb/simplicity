(** Execution of [sha256_finalize(ctx)]: the SHA-256 padding (0x80, zeros up
    to 56 mod 64, the 64-bit big-endian bit length) is absorbed into the
    context.  Conditional on the explicit [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_compress_call C.jet_sha_block_local C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_exec C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec.
Require Import C.jet_sha_be64_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Lemma sha_finalize_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_finalize = Some (sha_symbol_block _sha256_finalize).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_finalize_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_finalize) Ptrofs.zero) =
    Some (Internal f_sha256_finalize).
Proof. vm_compute; reflexivity. Qed.

Definition cf_assign (k : nat) : statement :=
  Sassign (Ederef (Ebinop Oadd (Evar ___compound (tarray tuchar 64))
      (Econst_int (Int.repr (Z.of_nat k)) tint) (tptr tuchar)) tuchar)
    (Econst_int (Int.repr (match k with O => 128 | _ => 0 end)) tint).

Fixpoint cf_fill (k : nat) : statement :=
  match k with
  | O => cf_assign 0
  | S k' => Ssequence (cf_fill k') (cf_assign k)
  end.

Definition fin_result : statement :=
  Ssequence (Sset _t'3 (ctx_field_expr SOverflow _ctx))
    (Sset _result (Ecast (Eunop Onotbool (Etempvar _t'3 tbool) tint) tbool)).
Definition fin_length : statement :=
  Ssequence (Sset _t'2 (ctx_field_expr SCounter _ctx))
    (Sset _length (Ebinop Omul (Etempvar _t'2 tulong) (Econst_int (Int.repr 8) tint) tulong)).
Definition fin_pad_len : expr :=
  Ebinop Oadd (Econst_int (Int.repr 1) tint)
    (Ebinop Omod
      (Ebinop Osub
        (Ebinop Osub (Ebinop Oadd (Econst_int (Int.repr 64) tint) (Econst_int (Int.repr 56) tint) tint)
          (Ebinop Omod (Etempvar _t'1 tulong) (Econst_int (Int.repr 64) tint) tulong) tulong)
        (Econst_int (Int.repr 1) tint) tulong)
      (Econst_int (Int.repr 64) tint) tulong) tulong.
Definition uchars_ty : type :=
  Tfunction (Tcons (tptr (Tstruct _sha256_context noattr)) (Tcons (tptr tuchar) (Tcons tulong Tnil)))
    tbool cc_default.
Definition fin_pad : statement :=
  Ssequence (cf_fill 63)
    (Ssequence (Sset _t'1 (ctx_field_expr SCounter _ctx))
      (Scall None (Evar _sha256_uchars uchars_ty)
        [Etempvar _ctx (tptr (Tstruct _sha256_context noattr)); Evar ___compound (tarray tuchar 64); fin_pad_len])).
Definition fin_len_call : statement :=
  Scall None (Evar _sha256_u64be
      (Tfunction (Tcons (tptr (Tstruct _sha256_context noattr)) (Tcons tulong Tnil)) tbool cc_default))
    [Etempvar _ctx (tptr (Tstruct _sha256_context noattr)); Etempvar _length tulong].

Lemma finalize_body :
  fn_body f_sha256_finalize =
    Ssequence fin_result (Ssequence fin_length
      (Ssequence fin_pad (Ssequence fin_len_call (Sreturn (Some (Etempvar _result tbool)))))).
Proof. reflexivity. Qed.

Definition pad_source : list int := Int.repr 128 :: repeat Int.zero 63.

Definition fin_env (bk : block) : env := PTree.set ___compound (bk, tarray tuchar 64) empty_env.
Lemma fin_blocks bk : blocks_of_env sha_ge (fin_env bk) = [(bk, 0, 64)].
Proof. vm_compute. reflexivity. Qed.
Definition fin_temps (bx : block) (cbase : Z) : temp_env :=
  PTree.set _ctx (Vptr bx (Ptrofs.repr cbase)) (create_undef_temps (fn_temps f_sha256_finalize)).

Lemma fin_entry m m1 bk bx cbase :
  Mem.alloc m 0 64 = (m1, bk) ->
  function_entry2 sha_ge f_sha256_finalize [Vptr bx (Ptrofs.repr cbase)] m
    (fin_env bk) (fin_temps bx cbase) m1.
Proof.
  intros HA. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros a b HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bk).
    + change (Mem.alloc m 0 64 = (m1, bk)); exact HA.
    + constructor.
  - reflexivity.
Qed.

Local Opaque sha_ge.

Lemma pad_source_nth k : (k < 64)%nat ->
  nth k pad_source Int.zero = Int.zero_ext 8 (Int.repr (match k with O => 128 | _ => 0 end)).
Proof.
  intros Hk. destruct k as [|k]; [reflexivity|].
  unfold pad_source. cbn [nth]. rewrite nth_repeat. reflexivity.
Qed.

Section Fill.
Variables (bk : block) (e : env).
Hypothesis He : e!___compound = Some (bk, tarray tuchar 64).

Lemma cf_fill_exec k : (k < 64)%nat -> forall le m,
  Mem.range_perm m bk 0 64 Cur Writable ->
  exists m',
    Clight2.exec_stmt sha_ge e le m (cf_fill k) E0 le m' Out_normal /\
    (forall j, (j <= k)%nat ->
       Mem.load Mint8unsigned m' bk (Z.of_nat j) = Some (Vint (nth j pad_source Int.zero))) /\
    (forall ch b ofs, b <> bk -> Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs kd p, Mem.perm m b ofs kd p -> Mem.perm m' b ofs kd p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  assert (Hstep : forall j le m, (j < 64)%nat -> Mem.range_perm m bk 0 64 Cur Writable ->
    exists m', Mem.store Mint8unsigned m bk (Z.of_nat j)
        (Vint (Int.zero_ext 8 (Int.repr (match j with O => 128 | _ => 0 end)))) = Some m' /\
      Clight2.exec_stmt sha_ge e le m (cf_assign j) E0 le m' Out_normal).
  { intros j le m Hj HP.
    assert (HW : Mem.valid_access m Mint8unsigned bk (Z.of_nat j) Writable).
    { split; [|exists (Z.of_nat j); cbn; lia]. intros ofs Ho. apply HP.
      change (size_chunk Mint8unsigned) with 1 in Ho. lia. }
    destruct (Mem.valid_access_store m Mint8unsigned bk (Z.of_nat j)
      (Vint (Int.zero_ext 8 (Int.repr (match j with O => 128 | _ => 0 end)))) HW) as [m' HS].
    exists m'. split; [exact HS|]. unfold cf_assign.
    eapply exec_Sassign with (v2 := Vint (Int.repr (match j with O => 128 | _ => 0 end))).
    - eapply eval_Ederef. eapply eval_Ebinop;
        [eapply eval_Elvalue; [apply eval_Evar_local; exact He|apply deref_loc_reference; reflexivity]
        |apply eval_Econst_int|reflexivity].
    - apply eval_Econst_int.
    - reflexivity.
    - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
      rewrite ptr_byte_offset;
        [exact HS|lia|change (Ptrofs.unsigned Ptrofs.zero) with 0;
                      change Ptrofs.max_unsigned with 18446744073709551615; lia]. }
  induction k as [|k IH]; intros Hk le m HP.
  - destruct (Hstep 0%nat le m Hk HP) as (m' & HS & HE).
    exists m'. split; [exact HE|]. split.
    { intros j Hj. assert (j = 0)%nat by lia. subst j.
      rewrite (Mem.load_store_same _ _ _ _ _ _ HS). reflexivity. }
    split; [intros ch b ofs Hb; eapply Mem.load_store_other; [exact HS|left; exact Hb]|].
    split; [intros b ofs kd p Hp; eapply Mem.perm_store_1; eauto|].
    intros b Hv; eapply Mem.store_valid_block_1; eauto.
  - destruct (IH ltac:(lia) le m HP) as (m1 & HE1 & HL1 & HF1 & HP1 & HV1).
    destruct (Hstep (S k) le m1 Hk ltac:(intros ofs Ho; apply HP1, HP, Ho)) as (m' & HS & HE).
    exists m'. split; [cbn [cf_fill]; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HE1|exact HE]|].
    split.
    { intros j Hj. destruct (Nat.eq_dec j (S k)) as [->|Hne].
      - rewrite (Mem.load_store_same _ _ _ _ _ _ HS). cbn [Val.load_result].
        rewrite pad_source_nth by lia. rewrite Int.zero_ext_idem by lia. reflexivity.
      - rewrite (Mem.load_store_other _ _ _ _ _ _ HS)
          by (right; change (size_chunk Mint8unsigned) with 1; lia).
        apply HL1. lia. }
    split.
    { intros ch b ofs Hb. rewrite (Mem.load_store_other _ _ _ _ _ _ HS) by (left; exact Hb).
      apply HF1. exact Hb. }
    split; [intros b ofs kd p Hp; eapply Mem.perm_store_1; [exact HS|apply HP1; exact Hp]|].
    intros b Hv; eapply Mem.store_valid_block_1; [exact HS|apply HV1; exact Hv].
Qed.
End Fill.

(** ** The padding *)
Definition pad_count (c : int64) : int64 :=
  Int64.add (Int64.repr 1)
    (Int64.modu (Int64.sub (Int64.sub (Int64.repr 120) (Int64.modu c c64)) (Int64.repr 1)) c64).

Lemma pad_count_unsigned c :
  Int64.unsigned (pad_count c) = 1 + (119 - Int64.unsigned c mod 64) mod 64.
Proof.
  pose proof (Z.mod_pos_bound (Int64.unsigned c) 64 ltac:(lia)) as HL.
  set (L := Int64.unsigned c mod 64) in *.
  assert (MU : Int64.max_unsigned = 18446744073709551615) by reflexivity.
  unfold pad_count. rewrite !modu64. fold L.
  assert (H1 : Int64.unsigned (Int64.sub (Int64.repr 120) (Int64.repr L)) = 120 - L).
  { unfold Int64.sub. rewrite (Int64.unsigned_repr 120), (Int64.unsigned_repr L) by lia.
    apply Int64.unsigned_repr. lia. }
  assert (H2 : Int64.unsigned (Int64.sub (Int64.sub (Int64.repr 120) (Int64.repr L)) (Int64.repr 1)) = 119 - L).
  { unfold Int64.sub at 1. rewrite H1. rewrite (Int64.unsigned_repr 1) by lia.
    rewrite Int64.unsigned_repr by lia. lia. }
  rewrite H2.
  pose proof (Z.mod_pos_bound (119 - L) 64 ltac:(lia)) as HM.
  unfold Int64.add. rewrite (Int64.unsigned_repr 1) by lia.
  rewrite (Int64.unsigned_repr ((119 - L) mod 64)) by lia.
  apply Int64.unsigned_repr. lia.
Qed.

Definition pad_bytes (c : int64) : list int :=
  firstn (Z.to_nat (Int64.unsigned (pad_count c))) pad_source.

Lemma pad_bytes_length c : Z.of_nat (length (pad_bytes c)) = Int64.unsigned (pad_count c).
Proof.
  pose proof (pad_count_unsigned c) as HP.
  pose proof (Z.mod_pos_bound (119 - Int64.unsigned c mod 64) 64 ltac:(lia)) as HM.
  unfold pad_bytes. rewrite firstn_length_le; [lia|].
  change (length pad_source) with 64%nat. lia.
Qed.

Lemma nth_firstn_lt {A} (n i : nat) (l : list A) d : (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  revert i l. induction n; intros i l Hi; [lia|].
  destruct l as [|x l]; [destruct i; reflexivity|].
  destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IHn. lia.
Qed.

Definition sha_pad (c : int64) : list int :=
  pad_bytes c ++ c_be64_bytes (Int64.mul c (Int64.repr 8)).

Lemma add_mod64 (a b : int64) :
  Int64.unsigned (Int64.add a b) mod 64 = (Int64.unsigned a mod 64 + Int64.unsigned b) mod 64.
Proof.
  assert (HD : forall x, (x mod Int64.modulus) mod 64 = x mod 64).
  { intros x. symmetry. apply Znumtheory.Zmod_div_mod;
      [lia|reflexivity|exists 288230376151711744; reflexivity]. }
  unfold Int64.add. rewrite Int64.unsigned_repr_eq, HD.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Theorem eval_sha256_finalize (Hmodel : memcpy_model) m bx cbase bo obase
    (l regs : list int) (c : int64) (ovf : bool) :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned -> 0 <= obase -> obase + 32 <= Ptrofs.max_unsigned ->
  bo <> bx ->
  sha_symbol_block _simplicity_sha256_compression <> bx ->
  sha_symbol_block _simplicity_sha256_compression <> bo ->
  sha_symbol_block _sha256_max_counter <> bx ->
  sha_symbol_block _sha256_max_counter <> bo ->
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
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_finalize)
      [Vptr bx (Ptrofs.repr cbase)] E0 m' (Vint (bit_int (negb ovf))) /\
    (forall i, (i < 8)%nat ->
       Mem.load Mint32 m' bo (obase + 4 * Z.of_nat i) =
         Some (Vint (nth i (snd (absorb_i l regs (sha_pad c))) Int.zero))) /\
    (forall ch b ofs, Mem.valid_block m b ->
       (b <> bx \/ ofs + size_chunk ch <= cbase + 8 \/ cbase + 81 <= ofs) ->
       (b <> bo \/ ofs + size_chunk ch <= obase \/ obase + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros Hcb HcM Hob HoM Hox Hgx Hgo HMx HMo Hr HOut HCnt HMod HOvf HBlk HRegs Hdisp HMax HPerm HAl.
  assert (Hll : (length l < 64)%nat).
  { pose proof (Z.mod_pos_bound (Int64.unsigned c) 64 ltac:(lia)). lia. }
  destruct (Mem.alloc m 0 64) as [m1 bk] eqn:A1.
  pose proof (mext_alloc _ _ _ _ _ A1) as (XV & XL & XP & XA).
  assert (Fk : forall b0, Mem.valid_block m b0 -> b0 <> bk).
  { intros b0 Hv Heq. subst b0. exact (Mem.fresh_block_alloc _ _ _ _ _ A1 Hv). }
  assert (Vx : Mem.valid_block m bx) by (eapply jet_bitmachine_rep.load_valid_block; exact HOut).
  assert (Vo : Mem.valid_block m bo).
  { destruct (HRegs 0%nat ltac:(lia)) as [HL0 _]. eapply jet_bitmachine_rep.load_valid_block; exact HL0. }
  assert (VG : Mem.valid_block m (sha_symbol_block _simplicity_sha256_compression))
    by (eapply jet_bitmachine_rep.load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m (sha_symbol_block _sha256_max_counter))
    by (eapply jet_bitmachine_rep.load_valid_block; exact HMax).
  assert (PK1 : Mem.range_perm m1 bk 0 64 Cur Freeable).
  { intros ofs Hr0. eapply Mem.perm_alloc_2; eauto. }
  set (le0 := fin_temps bx cbase).
  set (le1 := PTree.set _result (Vint (bit_int (negb ovf))) (PTree.set _t'3 (Vint (bit_int ovf)) le0)).
  set (len := Int64.mul c (Int64.repr 8)).
  set (le2 := PTree.set _length (Vlong len) (PTree.set _t'2 (Vlong c) le1)).
  destruct (cf_fill_exec bk (fin_env bk) eq_refl 63 ltac:(lia) le2 m1
    ltac:(intros ofs Hr0; eapply Mem.perm_implies with (p1 := Freeable); [apply PK1; exact Hr0|constructor]))
    as (m2 & HFill & HB2 & HF2 & HP2 & HV2).
  set (le3 := PTree.set _t'1 (Vlong c) le2).
  assert (K2 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m2 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. rewrite HF2 by (apply Fk; exact Hv). apply XL. exact Hv. }
  assert (V2 : forall b0, Mem.valid_block m b0 -> Mem.valid_block m2 b0).
  { intros b0 Hv. apply HV2, XV, Hv. }
  assert (Q2 : forall b0 ofs k p, Mem.perm m b0 ofs k p -> Mem.perm m2 b0 ofs k p).
  { intros b0 ofs k p Hp. apply HP2, XP, Hp. }
  set (bs := pad_bytes c).
  pose proof (pad_bytes_length c) as Hbs. fold bs in Hbs.
  pose proof (pad_count_unsigned c) as HPC.
  pose proof (Z.mod_pos_bound (119 - Int64.unsigned c mod 64) 64 ltac:(lia)) as HPM.
  pose proof (eval_sha256_uchars Hmodel m2 bx cbase bo obase bk Ptrofs.zero l regs bs c ovf
    Hcb HcM Hob HoM Hox (not_eq_sym (Fk bx Vx)) (not_eq_sym (Fk bo Vo)) Hgx Hgo) as HU.
  cbv zeta in HU.
  destruct HU as (m3 & HUc & HOut3 & HCnt3 & HOvf3 & HBlk3 & HReg3 & HMem3 & HPerm3 & HVal3).
  { change (Ptrofs.unsigned Ptrofs.zero) with 0. change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  { exact Hr. }
  { rewrite K2 by exact Vx. exact HOut. }
  { rewrite K2 by exact Vx. exact HCnt. }
  { exact HMod. }
  { rewrite K2 by exact Vx. exact HOvf. }
  { intros i Hi. rewrite K2 by exact Vx. apply HBlk. exact Hi. }
  { intros i Hi. destruct (HRegs i Hi) as [HL0 [Pr Al]]. split.
    - rewrite K2 by exact Vo. exact HL0.
    - split; [|exact Al]. intros ofs Hr0. apply Q2, Pr, Hr0. }
  { intros i Hi. change (Ptrofs.unsigned Ptrofs.zero) with 0. rewrite Z.add_0_l.
    assert (Hi64 : (i < 64)%nat) by lia.
    rewrite (HB2 i ltac:(lia)). unfold bs, pad_bytes. rewrite nth_firstn_lt by (fold bs; lia). reflexivity. }
  { unfold sha_dispatch_ok. rewrite K2 by exact VG. exact Hdisp. }
  { rewrite K2 by exact VM. exact HMax. }
  { intros ofs Hr0. apply Q2, HPerm, Hr0. }
  { exact HAl. }
  assert (HBsN : Int64.repr (Z.of_nat (length bs)) = pad_count c).
  { rewrite Hbs. apply Int64.repr_unsigned. }
  rewrite HBsN in HUc, HCnt3, HOvf3.
  set (ovf1 := uc_overflow ovf c (pad_count c)) in *.
  set (c1 := Int64.add c (pad_count c)) in *.
  destruct (absorb_i_shape bs l regs Hll Hr) as (HS1 & HS2 & HS3).
  set (l1 := fst (absorb_i l regs bs)) in *. set (regs1 := snd (absorb_i l regs bs)) in *.
  assert (V3 : forall b0, Mem.valid_block m b0 -> Mem.valid_block m3 b0).
  { intros b0 Hv. apply HVal3, V2, Hv. }
  assert (K3 : forall ch b0 ofs, Mem.valid_block m b0 ->
    (b0 <> bx \/ ofs + size_chunk ch <= cbase + 8 \/ cbase + 81 <= ofs) ->
    (b0 <> bo \/ ofs + size_chunk ch <= obase \/ obase + 32 <= ofs) ->
    Mem.load ch m3 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv H1 H2. rewrite HMem3; [apply K2; exact Hv|apply V2; exact Hv|exact H1|exact H2]. }
  assert (Q3 : forall b0 ofs k p, Mem.perm m b0 ofs k p -> Mem.perm m3 b0 ofs k p).
  { intros b0 ofs k p Hp. apply HPerm3; [apply V2; eapply Mem.perm_valid_block; exact Hp|]. apply Q2, Hp. }
  pose proof (eval_sha256_u64be Hmodel m3 bx cbase bo obase l1 regs1 c1 len ovf1
    Hcb HcM Hob HoM Hox Hgx Hgo HS3 HOut3 HCnt3) as HE.
  cbv zeta in HE.
  destruct HE as (m4 & HEc & _ & _ & _ & _ & HReg4 & HMem4 & HPerm4 & HVal4).
  { unfold c1. rewrite add_mod64, HMod, <- Hbs. symmetry. exact HS1. }
  { exact HOvf3. }
  { exact HBlk3. }
  { intros i Hi. split; [apply HReg3; exact Hi|].
    destruct (HRegs i Hi) as [_ [Pr Al]]. split; [|exact Al]. intros ofs Hr0. apply Q3, Pr, Hr0. }
  { unfold sha_dispatch_ok. rewrite K3; [exact Hdisp|exact VG|left; exact Hgx|left; exact Hgo]. }
  { rewrite K3; [exact HMax|exact VM|left; exact HMx|left; exact HMo]. }
  { intros ofs Hr0. apply Q3, HPerm, Hr0. }
  { exact HAl. }
  assert (HAbs : absorb_i l regs (sha_pad c) = absorb_i l1 regs1 (c_be64_bytes len)).
  { unfold sha_pad. fold bs len. rewrite absorb_i_app. reflexivity. }
  assert (Vk2 : Mem.valid_block m2 bk) by (apply HV2; eapply Mem.valid_new_block; exact A1).
  destruct (free_list_blocks [(bk, 0, 64)] m4) as (mf & HFL & HLf & HPf & HVf).
  { intros b0 lo hi [Heq|[]]. injection Heq as <- <- <-. intros ofs Hr0.
    apply HPerm4; [apply HVal3; exact Vk2|]. apply HPerm3; [exact Vk2|]. apply HP2, PK1, Hr0. }
  { repeat constructor; cbn; tauto. }
  cbn [map fst] in HLf, HPf.
  assert (HNk : forall b0, Mem.valid_block m b0 -> ~ In b0 [bk]).
  { intros b0 Hv [Heq|[]]. exact (Fk b0 Hv (eq_sym Heq)). }
  exists mf. split; [|split; [|split; [|split]]].
  - eapply eval_funcall_internal with (e := fin_env bk) (le1 := le0) (m1 := m1) (le2 := le3) (m2 := m4)
      (out := Out_return (Some (Vint (bit_int (negb ovf)), tbool))).
    + apply fin_entry; exact A1.
    + rewrite finalize_body.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m1).
      { unfold fin_result. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        - apply exec_Sset. eapply (eval_ctx_field SOverflow) with (chunk := Mint8unsigned);
            [exact Hcb|exact HcM|reflexivity|reflexivity|].
          rewrite XL by exact Vx. exact HOvf.
        - apply exec_Sset. eapply eval_Ecast with (v1 := Val.of_bool (negb ovf)).
          + eapply eval_Eunop; [apply eval_Etempvar; apply PTree.gss|]. destruct ovf; reflexivity.
          + destruct ovf; reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m1).
      { unfold fin_length. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        - apply exec_Sset. eapply (eval_ctx_field SCounter) with (chunk := Mint64);
            [exact Hcb|exact HcM|reflexivity|reflexivity|].
          rewrite XL by exact Vx. exact HCnt.
        - apply exec_Sset. eapply eval_Ebinop;
            [apply eval_Etempvar; apply PTree.gss|apply eval_Econst_int|reflexivity]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m3).
      { unfold fin_pad. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HFill|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m2).
        - apply exec_Sset. eapply (eval_ctx_field SCounter) with (chunk := Mint64);
            [exact Hcb|exact HcM|reflexivity|reflexivity|].
          rewrite K2 by exact Vx. exact HCnt.
        - change le3 with (set_opttemp None (Vint (bit_int (negb ovf1))) le3) at 2.
          eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_uchars) Ptrofs.zero)
            (vargs := [Vptr bx (Ptrofs.repr cbase); Vptr bk Ptrofs.zero; Vlong (pad_count c)])
            (f := Internal f_sha256_uchars).
          + reflexivity.
          + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_uchars_symbol]|].
            apply deref_loc_reference; reflexivity.
          + eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
            eapply eval_Econs.
            * eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity].
            * reflexivity.
            * eapply eval_Econs with (v1 := Vlong (pad_count c)); [|reflexivity|apply eval_Enil].
              unfold fin_pad_len, pad_count.
              set (vA := Int64.modu c c64).
              set (vB := Int64.sub (Int64.repr 120) vA).
              set (vC := Int64.sub vB (Int64.repr 1)).
              set (vD := Int64.modu vC c64).
              eapply eval_Ebinop with (v1 := Vint (Int.repr 1)) (v2 := Vlong vD);
                [apply eval_Econst_int| |reflexivity].
              eapply eval_Ebinop with (v1 := Vlong vC) (v2 := Vint (Int.repr 64));
                [|apply eval_Econst_int|reflexivity].
              eapply eval_Ebinop with (v1 := Vlong vB) (v2 := Vint (Int.repr 1));
                [|apply eval_Econst_int|reflexivity].
              eapply eval_Ebinop with (v1 := Vint (Int.add (Int.repr 64) (Int.repr 56))) (v2 := Vlong vA);
                [| |reflexivity].
              -- eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Econst_int|reflexivity].
              -- eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|apply eval_Econst_int|reflexivity].
          + exact sha_uchars_funct.
          + reflexivity.
          + exact HUc. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m4).
      { unfold fin_len_call.
        change le3 with (set_opttemp None (Vint (bit_int (negb (uc_overflow ovf1 c1 (Int64.repr 8))))) le3) at 2.
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_u64be) Ptrofs.zero)
          (vargs := [Vptr bx (Ptrofs.repr cbase); Vlong len]) (f := Internal f_sha256_u64be).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_u64be_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
          eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|apply eval_Enil].
        - exact sha_u64be_funct.
        - reflexivity.
        - exact HEc. }
      apply exec_Sreturn_some. apply eval_Etempvar. reflexivity.
    + cbn. split; [discriminate|]. destruct ovf; reflexivity.
    + rewrite fin_blocks. exact HFL.
  - intros i Hi. rewrite HLf by (apply HNk; exact Vo). rewrite HAbs. apply HReg4. exact Hi.
  - intros ch b0 ofs Hv H1 H2. rewrite HLf by (apply HNk; exact Hv).
    rewrite HMem4; [apply K3; assumption|apply V3; exact Hv|exact H1|exact H2].
  - intros b0 ofs k p Hv Hp. apply HPf; [apply HNk; exact Hv|].
    apply HPerm4; [apply V3; exact Hv|]. apply Q3, Hp.
  - intros b0 Hv. apply HVf, HVal4, V3, Hv.
Qed.
