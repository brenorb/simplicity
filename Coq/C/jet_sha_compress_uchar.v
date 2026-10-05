(** Execution of [sha256_compression_uchar(s, chunk)]: the 64 bytes at
    [chunk] are read as sixteen big-endian words into a local array, which is
    then compressed into the state [s] through the dispatch pointer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import C.jet_exec.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_compress_call C.jet_sha_block_exec C.jet_sha_block_local.
Require Import C.jet_sha_ctx8_model C.jet_sha_be32_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 300.

Definition be_temps : list ident :=
  [_t'1; _t'2; _t'3; _t'4; _t'5; _t'6; _t'7; _t'8; _t'9; _t'10; _t'11; _t'12; _t'13; _t'14; _t'15; _t'16].

Definition be_temp (k : nat) : ident := nth k be_temps _t'1.

Definition be_call (k : nat) : statement :=
  Scall (Some (be_temp k)) (Evar _ReadBE32 (Tfunction (Tcons (tptr tuchar) Tnil) tuint cc_default))
    [Ebinop Oadd (Etempvar _chunk (tptr tuchar))
       (Ebinop Omul (Econst_int (Int.repr 4) tint) (Econst_int (Int.repr (Z.of_nat k)) tint) tint)
       (tptr tuchar)].

Definition be_assign (k : nat) : statement :=
  Sassign
    (Ederef (Ebinop Oadd (Evar ___compound (tarray tuint 16)) (Econst_int (Int.repr (Z.of_nat k)) tint)
      (tptr tuint)) tuint)
    (Etempvar (be_temp k) tuint).

Fixpoint be_fill (k : nat) : statement :=
  match k with
  | O => Ssequence (be_call 0) (be_assign 0)
  | S k' => Ssequence (Ssequence (be_fill k') (be_call k)) (be_assign k)
  end.

Definition be_tail : statement :=
  Ssequence
    (Sset _t'17 (Evar _simplicity_sha256_compression
      (tptr (Tfunction (Tcons (tptr tuint) (Tcons (tptr tuint) Tnil)) tvoid cc_default))))
    (Scall None (Etempvar _t'17 (tptr (Tfunction (Tcons (tptr tuint) (Tcons (tptr tuint) Tnil)) tvoid cc_default)))
      [Etempvar _s (tptr tuint); Evar ___compound (tarray tuint 16)]).

Lemma compression_uchar_body :
  fn_body f_sha256_compression_uchar = Ssequence (be_fill 15) be_tail.
Proof. reflexivity. Qed.

Definition c_be_word (bytes : list int) (j : nat) : int :=
  c_be32 (nth (4 * j) bytes Int.zero) (nth (4 * j + 1) bytes Int.zero)
         (nth (4 * j + 2) bytes Int.zero) (nth (4 * j + 3) bytes Int.zero).

Lemma be_temp_fresh k : (k < 16)%nat -> be_temp k <> _chunk /\ be_temp k <> _s.
Proof.
  intros Hk. do 16 (destruct k as [|k]; [split; discriminate|]). lia.
Qed.

Lemma ptr_word_offset (i : Z) : 0 <= i <= 1000 ->
  Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr i)))) = 4 * i.
Proof.
  intros Hi.
  assert (HI : Ptrofs.of_ints (Int.repr i) = Ptrofs.repr i).
  { unfold Ptrofs.of_ints. rewrite Int.signed_repr; [reflexivity|].
    change Int.min_signed with (-2147483648). change Int.max_signed with 2147483647. lia. }
  rewrite HI, Ptrofs.add_zero_l. unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 4), (Ptrofs.unsigned_repr i)
    by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
  apply Ptrofs.unsigned_repr. change Ptrofs.max_unsigned with 18446744073709551615. lia.
Qed.

Section Fill.
Variables (bc bk : block) (oc : ptrofs) (bytes : list int) (e : env).
Hypothesis Hbk : bc <> bk.
Hypothesis Hoc : Ptrofs.unsigned oc + 64 <= Ptrofs.max_unsigned.
Hypothesis He : e!___compound = Some (bk, tarray tuint 16).
Hypothesis HeR : e!_ReadBE32 = None.

Definition fill_ok (m : mem) : Prop :=
  (forall i, (i < 64)%nat ->
     Mem.load Mint8unsigned m bc (Ptrofs.unsigned oc + Z.of_nat i) = Some (Vint (nth i bytes Int.zero))) /\
  (forall j, (j < 16)%nat -> Mem.valid_access m Mint32 bk (4 * Z.of_nat j) Writable).

Lemma be_pair_exec k le m :
  (k < 16)%nat -> fill_ok m -> le!_chunk = Some (Vptr bc oc) ->
  exists m',
    Mem.store Mint32 m bk (4 * Z.of_nat k) (Vint (c_be_word bytes k)) = Some m' /\
    Clight2.exec_stmt sha_ge e le m (be_call k) E0
      (PTree.set (be_temp k) (Vint (c_be_word bytes k)) le) m Out_normal /\
    Clight2.exec_stmt sha_ge e (PTree.set (be_temp k) (Vint (c_be_word bytes k)) le) m (be_assign k) E0
      (PTree.set (be_temp k) (Vint (c_be_word bytes k)) le) m' Out_normal.
Proof.
  intros Hk [HB HW] Hchunk.
  destruct (Mem.valid_access_store m Mint32 bk (4 * Z.of_nat k) (Vint (c_be_word bytes k)) (HW k Hk))
    as [m' HS].
  exists m'. split; [exact HS|].
  assert (HMul : Int.mul (Int.repr 4) (Int.repr (Z.of_nat k)) = Int.repr (4 * Z.of_nat k)).
  { unfold Int.mul. rewrite !Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
    reflexivity. }
  set (ok := Ptrofs.add oc (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr (4 * Z.of_nat k))))).
  assert (Hok : Ptrofs.unsigned ok = Ptrofs.unsigned oc + 4 * Z.of_nat k)
    by (apply ptr_byte_offset; lia).
  split.
  - change (PTree.set (be_temp k) (Vint (c_be_word bytes k)) le) with
      (set_opttemp (Some (be_temp k)) (Vint (c_be_word bytes k)) le).
    eapply exec_Scall with (vf := Vptr (sha_symbol_block _ReadBE32) Ptrofs.zero)
      (vargs := [Vptr bc ok]) (f := Internal f_ReadBE32).
    + reflexivity.
    + eapply eval_Elvalue; [apply eval_Evar_global; [exact HeR|exact sha_ReadBE32_symbol]|].
      apply deref_loc_reference; reflexivity.
    + eapply eval_Econs; [| |apply eval_Enil].
      * eapply eval_Ebinop; [apply eval_Etempvar; exact Hchunk| |].
        -- eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Econst_int|reflexivity].
        -- cbn. rewrite HMul. reflexivity.
      * reflexivity.
    + exact sha_ReadBE32_funct.
    + reflexivity.
    + unfold c_be_word. apply eval_sha_ReadBE32.
      * rewrite Hok. lia.
      * rewrite Hok. replace (Ptrofs.unsigned oc + 4 * Z.of_nat k) with
          (Ptrofs.unsigned oc + Z.of_nat (4 * k)) by lia. apply HB. lia.
      * rewrite Hok. replace (Ptrofs.unsigned oc + 4 * Z.of_nat k + 1) with
          (Ptrofs.unsigned oc + Z.of_nat (4 * k + 1)) by lia. apply HB. lia.
      * rewrite Hok. replace (Ptrofs.unsigned oc + 4 * Z.of_nat k + 2) with
          (Ptrofs.unsigned oc + Z.of_nat (4 * k + 2)) by lia. apply HB. lia.
      * rewrite Hok. replace (Ptrofs.unsigned oc + 4 * Z.of_nat k + 3) with
          (Ptrofs.unsigned oc + Z.of_nat (4 * k + 3)) by lia. apply HB. lia.
  - eapply exec_Sassign with (v2 := Vint (c_be_word bytes k)) (v := Vint (c_be_word bytes k)).
    + eapply eval_Ederef. eapply eval_Ebinop;
        [eapply eval_Elvalue; [apply eval_Evar_local; exact He|apply deref_loc_reference; reflexivity]
        |apply eval_Econst_int|reflexivity].
    + apply eval_Etempvar. apply PTree.gss.
    + reflexivity.
    + eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
      rewrite ptr_word_offset by lia. exact HS.
Qed.

Lemma fill_ok_store k m m' v :
  fill_ok m -> Mem.store Mint32 m bk (4 * Z.of_nat k) v = Some m' -> fill_ok m'.
Proof.
  intros [HB HW] HS. split.
  - intros i Hi. rewrite (Mem.load_store_other _ _ _ _ _ _ HS) by (left; exact Hbk). apply HB; exact Hi.
  - intros j Hj. eapply Mem.store_valid_access_1; [exact HS|apply HW; exact Hj].
Qed.

Lemma be_fill_exec k : (k < 16)%nat -> forall le m,
  fill_ok m -> le!_chunk = Some (Vptr bc oc) ->
  exists le' m',
    Clight2.exec_stmt sha_ge e le m (be_fill k) E0 le' m' Out_normal /\
    le'!_chunk = le!_chunk /\ le'!_s = le!_s /\ fill_ok m' /\
    (forall j, (j <= k)%nat ->
       Mem.load Mint32 m' bk (4 * Z.of_nat j) = Some (Vint (c_be_word bytes j))) /\
    (forall ch b ofs, b <> bk -> Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs kd p, Mem.perm m b ofs kd p -> Mem.perm m' b ofs kd p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  induction k as [|k IH]; intros Hk le m Hok Hchunk.
  - destruct (be_pair_exec 0 le m Hk Hok Hchunk) as (m' & HS & HC & HA).
    destruct (be_temp_fresh 0 Hk) as [N1 N2].
    exists (PTree.set (be_temp 0) (Vint (c_be_word bytes 0)) le), m'.
    split; [cbn [be_fill]; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HC|exact HA]|].
    split; [apply PTree.gso; auto|]. split; [apply PTree.gso; auto|].
    split; [eapply fill_ok_store; eauto|].
    split.
    { intros j Hj. assert (j = 0)%nat by lia. subst j.
      rewrite (Mem.load_store_same _ _ _ _ _ _ HS). reflexivity. }
    split; [intros ch b ofs Hb; eapply Mem.load_store_other; [exact HS|left; exact Hb]|].
    split; [intros b ofs kd p Hp; eapply Mem.perm_store_1; eauto|].
    intros b Hv; eapply Mem.store_valid_block_1; eauto.
  - destruct (IH ltac:(lia) le m Hok Hchunk) as (le1 & m1 & HE1 & HC1 & HS1 & Hok1 & HL1 & HF1 & HP1 & HV1).
    destruct (be_pair_exec (S k) le1 m1 Hk Hok1 ltac:(rewrite HC1; exact Hchunk)) as (m' & HS & HC & HA).
    destruct (be_temp_fresh (S k) Hk) as [N1 N2].
    exists (PTree.set (be_temp (S k)) (Vint (c_be_word bytes (S k))) le1), m'.
    split.
    { cbn [be_fill]. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [|exact HA].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HE1|exact HC]. }
    split; [rewrite PTree.gso by auto; exact HC1|]. split; [rewrite PTree.gso by auto; exact HS1|].
    split; [eapply fill_ok_store; eauto|].
    split.
    { intros j Hj. destruct (Nat.eq_dec j (S k)) as [->|Hne].
      - rewrite (Mem.load_store_same _ _ _ _ _ _ HS). reflexivity.
      - rewrite (Mem.load_store_other _ _ _ _ _ _ HS)
          by (right; change (size_chunk Mint32) with 4; lia).
        apply HL1. lia. }
    split.
    { intros ch b ofs Hb. rewrite (Mem.load_store_other _ _ _ _ _ _ HS) by (left; exact Hb).
      apply HF1. exact Hb. }
    split; [intros b ofs kd p Hp; eapply Mem.perm_store_1; [exact HS|apply HP1; exact Hp]|].
    intros b Hv; eapply Mem.store_valid_block_1; [exact HS|apply HV1; exact Hv].
Qed.
End Fill.

Lemma c_be_words_eq (bytes : list int) :
  length bytes = 64%nat -> (forall i, (i < 64)%nat -> Int.unsigned (nth i bytes Int.zero) < 256) ->
  map (c_be_word bytes) (seq 0 16) = be_words bytes.
Proof.
  intros HL HR. apply (nth_ext _ _ Int.zero Int.zero).
  - rewrite map_length, seq_length. symmetry. apply be_words_length. rewrite HL. reflexivity.
  - intros n Hn. rewrite map_length, seq_length in Hn.
    rewrite (nth_indep _ Int.zero (c_be_word bytes 0)) by (rewrite map_length, seq_length; exact Hn).
    rewrite map_nth, seq_nth by exact Hn. cbn [Nat.add].
    rewrite be_words_nth by lia. unfold c_be_word. apply c_be32_be32; apply HR; lia.
Qed.

Definition cu_env (bk : block) : env := PTree.set ___compound (bk, tarray tuint 16) empty_env.
Definition cu_temps (bs : block) (os : ptrofs) (bc : block) (oc : ptrofs) : temp_env :=
  PTree.set _chunk (Vptr bc oc) (PTree.set _s (Vptr bs os)
    (create_undef_temps (fn_temps f_sha256_compression_uchar))).

Lemma cu_entry m m1 bk bs os bc oc :
  Mem.alloc m 0 64 = (m1, bk) ->
  function_entry2 sha_ge f_sha256_compression_uchar [Vptr bs os; Vptr bc oc] m
    (cu_env bk) (cu_temps bs os bc oc) m1.
Proof.
  intros HA. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bk).
    + change (Mem.alloc m 0 64 = (m1, bk)); exact HA.
    + constructor.
  - reflexivity.
Qed.

Lemma cu_blocks bk : blocks_of_env sha_ge (cu_env bk) = [(bk, 0, 64)].
Proof. vm_compute. reflexivity. Qed.

Theorem eval_sha_compression_uchar m bs os bc oc (regs bytes : list int) :
  length regs = 8%nat -> length bytes = 64%nat ->
  Ptrofs.unsigned os + 32 <= Ptrofs.max_unsigned -> Ptrofs.unsigned oc + 64 <= Ptrofs.max_unsigned ->
  sha_dispatch_ok m ->
  (forall i, (i < 8)%nat ->
     Mem.load Mint32 m bs (Ptrofs.unsigned os + 4 * Z.of_nat i) = Some (Vint (nth i regs Int.zero)) /\
     Mem.valid_access m Mint32 bs (Ptrofs.unsigned os + 4 * Z.of_nat i) Writable) ->
  (forall i, (i < 64)%nat ->
     Mem.load Mint8unsigned m bc (Ptrofs.unsigned oc + Z.of_nat i) = Some (Vint (nth i bytes Int.zero))) ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_compression_uchar)
      [Vptr bs os; Vptr bc oc] E0 m' Vundef /\
    (forall i, (i < 8)%nat ->
       Mem.load Mint32 m' bs (Ptrofs.unsigned os + 4 * Z.of_nat i) =
         Some (Vint (nth i (SHA256.hash_block regs (be_words bytes)) Int.zero))) /\
    (forall ch b ofs, Mem.valid_block m b ->
       (b <> bs \/ ofs + size_chunk ch <= Ptrofs.unsigned os \/ Ptrofs.unsigned os + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros Hlr Hlb Hso Hco Hdisp HS HC.
  destruct (Mem.alloc m 0 64) as [m1 bk] eqn:A1.
  pose proof (mext_alloc _ _ _ _ _ A1) as (XV & XL & XP & XA).
  assert (Hfresh : forall b, Mem.valid_block m b -> b <> bk).
  { intros b Hv Heq. subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ A1 Hv). }
  assert (Hvs : Mem.valid_block m bs).
  { destruct (HS 0%nat ltac:(lia)) as [_ PW]. eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies; [exact PW|constructor]. }
  assert (Hvc : Mem.valid_block m bc).
  { pose proof (HC 0%nat ltac:(lia)) as HL. apply Mem.load_valid_access in HL.
    eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies; [exact HL|constructor]. }
  assert (Hvg : Mem.valid_block m (sha_symbol_block _simplicity_sha256_compression)).
  { unfold sha_dispatch_ok in Hdisp. apply Mem.load_valid_access in Hdisp.
    eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies; [exact Hdisp|constructor]. }
  assert (Hok1 : fill_ok bc bk oc bytes m1).
  { split.
    - intros i Hi. rewrite XL by exact Hvc. apply HC; exact Hi.
    - intros j Hj. eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
      eapply Mem.valid_access_alloc_same; [exact A1|lia|change (size_chunk Mint32) with 4; lia|].
      exists (Z.of_nat j). change (align_chunk Mint32) with 4. lia. }
  destruct (be_fill_exec bc bk oc bytes (cu_env bk) (Hfresh bc Hvc) Hco eq_refl eq_refl 15 ltac:(lia)
    (cu_temps bs os bc oc) m1 Hok1 eq_refl)
    as (le2 & m2 & HE2 & HC2 & HS2 & Hok2 & HL2 & HF2 & HP2 & HV2).
  set (blk := map (c_be_word bytes) (seq 0 16)).
  assert (Hlblk : length blk = 16%nat) by (unfold blk; rewrite map_length, seq_length; reflexivity).
  destruct (eval_sha_compression m2 bs os bk Ptrofs.zero regs blk Hlr Hlblk Hso
    ltac:(change (Ptrofs.unsigned Ptrofs.zero) with 0; change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(left; apply Hfresh; exact Hvs))
    as (m3 & Hcomp & HS3 & HL3 & HP3 & HV3).
  { intros i Hi. destruct (HS i Hi) as [HLd HVa]. split.
    - rewrite HF2 by (apply Hfresh; exact Hvs). rewrite XL by exact Hvs. exact HLd.
    - destruct HVa as [Pr Al]. split; [|exact Al].
      intros ofs Ho. apply HP2, XP, Pr. exact Ho. }
  { intros i Hi. change (Ptrofs.unsigned Ptrofs.zero) with 0. rewrite Z.add_0_l.
    rewrite (HL2 i ltac:(lia)). unfold blk.
    rewrite (nth_indep _ Int.zero (c_be_word bytes 0)) by (rewrite map_length, seq_length; exact Hi).
    rewrite map_nth, seq_nth by exact Hi. reflexivity. }
  assert (Vk1 : Mem.valid_block m1 bk) by (eapply Mem.valid_new_block; exact A1).
  assert (PF : forall b0 lo hi, In (b0, lo, hi) [(bk, 0, 64)] -> Mem.range_perm m3 b0 lo hi Cur Freeable).
  { intros b0 lo hi [Heq|[]]. injection Heq as <- <- <-. intros ofs Ho.
    apply HP3; [apply HV2; exact Vk1|]. apply HP2. eapply Mem.perm_alloc_2; eauto. }
  destruct (free_list_blocks [(bk, 0, 64)] m3 PF ltac:(repeat constructor; cbn; tauto))
    as (mf & HFL & HLf & HPf & HVf).
  cbn [map fst] in HLf, HPf.
  assert (Hnk : forall b, Mem.valid_block m b -> ~ In b [bk]).
  { intros b Hv [Heq|[]]. exact (Hfresh b Hv (eq_sym Heq)). }
  exists mf. split; [|split; [|split; [|split]]].
  - set (le3 := PTree.set _t'17 (Vptr (sha_symbol_block _sha256_compression_portable) Ptrofs.zero) le2).
    eapply eval_funcall_internal with (e := cu_env bk) (le1 := cu_temps bs os bc oc) (le2 := le3)
      (m1 := m1) (m2 := m3) (out := Out_normal).
    + apply cu_entry; exact A1.
    + rewrite compression_uchar_body.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HE2|]. unfold be_tail.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2) (le1 := le3).
      * constructor. eapply eval_Elvalue.
        -- apply eval_Evar_global; [reflexivity|exact sha_dispatch_symbol].
        -- eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv.
           change (Ptrofs.unsigned Ptrofs.zero) with 0.
           rewrite HF2 by (apply Hfresh; exact Hvg). rewrite XL by exact Hvg. exact Hdisp.
      * change le3 with (set_opttemp None Vundef le3) at 2.
        eapply exec_Scall with
          (vf := Vptr (sha_symbol_block _sha256_compression_portable) Ptrofs.zero)
          (vargs := [Vptr bs os; Vptr bk Ptrofs.zero])
          (f := Internal f_sha256_compression_portable) (vres := Vundef).
        -- reflexivity.
        -- apply eval_Etempvar. apply PTree.gss.
        -- eapply eval_Econs.
           ++ apply eval_Etempvar. unfold le3. rewrite PTree.gso by discriminate.
              rewrite HS2. reflexivity.
           ++ reflexivity.
           ++ eapply eval_Econs with (v1 := Vptr bk Ptrofs.zero); [|reflexivity|apply eval_Enil].
              eapply eval_Elvalue; [eapply eval_Evar_local; reflexivity|].
              apply deref_loc_reference; reflexivity.
        -- exact sha_compression_funct.
        -- reflexivity.
        -- exact Hcomp.
    + cbn. reflexivity.
    + rewrite cu_blocks. exact HFL.
  - intros i Hi. rewrite HLf by (apply Hnk; exact Hvs).
    rewrite (HS3 i Hi). unfold blk. rewrite c_be_words_eq; [reflexivity|exact Hlb|].
    intros j Hj. eapply load_byte_range. apply HC. exact Hj.
  - intros ch b ofs Hv Hcond. rewrite HLf by (apply Hnk; exact Hv).
    rewrite HL3; [|apply HV2, XV; exact Hv|exact Hcond].
    rewrite HF2 by (apply Hfresh; exact Hv). apply XL. exact Hv.
  - intros b ofs k p Hv Hp. apply HPf; [apply Hnk; exact Hv|].
    apply HP3; [apply HV2, XV; exact Hv|]. apply HP2, XP. exact Hp.
  - intros b Hv. apply HVf, HV3, HV2, XV. exact Hv.
Qed.
