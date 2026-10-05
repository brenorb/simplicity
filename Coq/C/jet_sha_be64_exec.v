(** Execution of [WriteBE64] and [sha256_u64be] in the SHA translation unit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_be32_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Lemma sha_WriteBE64_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _WriteBE64 = Some (sha_symbol_block _WriteBE64).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_WriteBE64_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _WriteBE64) Ptrofs.zero) =
    Some (Internal f_WriteBE64).
Proof. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

Definition c255 : int64 := Int64.repr (Int.signed (Int.repr 255)).

(** The byte stored at position [i < 7] and at position 7. *)
Definition c_be64_shift (x : int64) (k : Z) : int :=
  Int.zero_ext 8 (Int64.loword (Int64.and c255 (Int64.shru' x (Int.repr k)))).
Definition c_be64_low (x : int64) : int :=
  Int.zero_ext 8 (Int64.loword (Int64.and c255 x)).

Definition c_be64_bytes (x : int64) : list int :=
  [c_be64_shift x 56; c_be64_shift x 48; c_be64_shift x 40; c_be64_shift x 32;
   c_be64_shift x 24; c_be64_shift x 16; c_be64_shift x 8; c_be64_low x].

Definition wbe_le (bp : block) (op : ptrofs) (x : int64) : temp_env :=
  PTree.set _x (Vlong x) (PTree.set _ptr (Vptr bp op) (create_undef_temps (fn_temps f_WriteBE64))).

Definition wbe_lhs (i : Z) : expr :=
  Ederef (Ebinop Oadd (Etempvar _ptr (tptr tuchar)) (Econst_int (Int.repr i) tint) (tptr tuchar)) tuchar.

Lemma wbe_assign bp op x m m' i rhs v w :
  0 <= i <= 7 -> Ptrofs.unsigned op + 8 <= Ptrofs.max_unsigned ->
  eval_expr sha_ge empty_env (wbe_le bp op x) m rhs v ->
  sem_cast v (typeof rhs) tuchar m = Some (Vint w) ->
  Mem.store Mint8unsigned m bp (Ptrofs.unsigned op + i) (Vint w) = Some m' ->
  Clight2.exec_stmt sha_ge empty_env (wbe_le bp op x) m (Sassign (wbe_lhs i) rhs) E0
    (wbe_le bp op x) m' Out_normal.
Proof.
  intros Hi HM HE HC HS. unfold wbe_lhs.
  eapply exec_Sassign with (v2 := v) (v := Vint w).
  - eapply eval_Ederef. eapply eval_Ebinop; [apply eval_Etempvar; reflexivity|apply eval_Econst_int|reflexivity].
  - exact HE.
  - exact HC.
  - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
    rewrite ptr_byte_offset by lia. exact HS.
Qed.

Ltac wbe_rhs :=
  first [apply eval_Etempvar; reflexivity | apply eval_Econst_int
        | eapply eval_Ebinop; [wbe_rhs|wbe_rhs|reflexivity]
        | eapply eval_Ecast; [wbe_rhs|reflexivity]].

Lemma zero_ext8_idem x : Int.zero_ext 8 (Int.zero_ext 8 x) = Int.zero_ext 8 x.
Proof. apply Int.zero_ext_idem. lia. Qed.

Theorem eval_sha_WriteBE64 m bp op x :
  Ptrofs.unsigned op + 8 <= Ptrofs.max_unsigned ->
  Mem.range_perm m bp (Ptrofs.unsigned op) (Ptrofs.unsigned op + 8) Cur Writable ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_WriteBE64) [Vptr bp op; Vlong x] E0 m' Vundef /\
    (forall i, (i < 8)%nat ->
       Mem.load Mint8unsigned m' bp (Ptrofs.unsigned op + Z.of_nat i) =
         Some (Vint (nth i (c_be64_bytes x) Int.zero))) /\
    (forall ch b ofs,
       (b <> bp \/ ofs + size_chunk ch <= Ptrofs.unsigned op \/ Ptrofs.unsigned op + 8 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HM HP.
  set (o := Ptrofs.unsigned op) in *.
  assert (HVA : forall mm i, 0 <= i <= 7 -> (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mm b ofs k p) ->
    Mem.valid_access mm Mint8unsigned bp (o + i) Writable).
  { intros mm i Hi Hpm. split; [|exists (o + i); cbn; lia]. intros ofs Ho. apply Hpm, HP.
    change (size_chunk Mint8unsigned) with 1 in Ho. lia. }
  destruct (Mem.valid_access_store m Mint8unsigned bp (o + 0) (Vint (Int.zero_ext 8 (c_be64_shift x 56))) (HVA m 0 ltac:(lia) (fun b ofs k p H => H))) as [m1 S1].
  assert (P1 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m1 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S1|]. exact Hp. }
  destruct (Mem.valid_access_store m1 Mint8unsigned bp (o + 1) (Vint (c_be64_shift x 48)) (HVA m1 1 ltac:(lia) P1)) as [m2 S2].
  assert (P2 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m2 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S2|]. apply P1; exact Hp. }
  destruct (Mem.valid_access_store m2 Mint8unsigned bp (o + 2) (Vint (c_be64_shift x 40)) (HVA m2 2 ltac:(lia) P2)) as [m3 S3].
  assert (P3 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m3 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S3|]. apply P2; exact Hp. }
  destruct (Mem.valid_access_store m3 Mint8unsigned bp (o + 3) (Vint (c_be64_shift x 32)) (HVA m3 3 ltac:(lia) P3)) as [m4 S4].
  assert (P4 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m4 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S4|]. apply P3; exact Hp. }
  destruct (Mem.valid_access_store m4 Mint8unsigned bp (o + 4) (Vint (c_be64_shift x 24)) (HVA m4 4 ltac:(lia) P4)) as [m5 S5].
  assert (P5 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m5 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S5|]. apply P4; exact Hp. }
  destruct (Mem.valid_access_store m5 Mint8unsigned bp (o + 5) (Vint (c_be64_shift x 16)) (HVA m5 5 ltac:(lia) P5)) as [m6 S6].
  assert (P6 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m6 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S6|]. apply P5; exact Hp. }
  destruct (Mem.valid_access_store m6 Mint8unsigned bp (o + 6) (Vint (c_be64_shift x 8)) (HVA m6 6 ltac:(lia) P6)) as [m7 S7].
  assert (P7 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m7 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S7|]. apply P6; exact Hp. }
  destruct (Mem.valid_access_store m7 Mint8unsigned bp (o + 7) (Vint (c_be64_low x)) (HVA m7 7 ltac:(lia) P7)) as [m8 S8].
  assert (P8 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m8 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S8|]. apply P7; exact Hp. }
  exists m8. split; [|split; [|split; [|split; [exact P8|]]]].
  - eapply eval_funcall_internal with (e := empty_env) (le1 := wbe_le bp op x) (m1 := m)
      (le2 := wbe_le bp op x) (m2 := m8) (out := Out_normal).
    + apply function_entry2_intro.
      * apply list_norepet_nil.
      * cbn. repeat constructor; cbn; intuition discriminate.
      * intros x0 y0 HX HY. cbn in HY. contradiction.
      * apply alloc_variables_nil.
      * reflexivity.
    + cbn [f_WriteBE64 fn_body].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := wbe_le bp op x).
      { eapply (wbe_assign bp op x m m1 0); [lia|exact HM|wbe_rhs|reflexivity|exact S1]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2) (le1 := wbe_le bp op x).
      { eapply (wbe_assign bp op x m1 m2 1); [lia|exact HM|wbe_rhs|reflexivity|exact S2]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m3) (le1 := wbe_le bp op x).
      { eapply (wbe_assign bp op x m2 m3 2); [lia|exact HM|wbe_rhs|reflexivity|exact S3]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m4) (le1 := wbe_le bp op x).
      { eapply (wbe_assign bp op x m3 m4 3); [lia|exact HM|wbe_rhs|reflexivity|exact S4]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m5) (le1 := wbe_le bp op x).
      { eapply (wbe_assign bp op x m4 m5 4); [lia|exact HM|wbe_rhs|reflexivity|exact S5]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m6) (le1 := wbe_le bp op x).
      { eapply (wbe_assign bp op x m5 m6 5); [lia|exact HM|wbe_rhs|reflexivity|exact S6]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m7) (le1 := wbe_le bp op x).
      { eapply (wbe_assign bp op x m6 m7 6); [lia|exact HM|wbe_rhs|reflexivity|exact S7]. }
      eapply (wbe_assign bp op x m7 m8 7); [lia|exact HM|wbe_rhs|reflexivity|exact S8].
    + cbn. reflexivity.
    + reflexivity.
  - intros i Hi.
    assert (HL : forall j w mm mm', Mem.store Mint8unsigned mm bp (o + j) (Vint w) = Some mm' ->
      Mem.load Mint8unsigned mm' bp (o + j) = Some (Vint (Int.zero_ext 8 w))).
    { intros j w mm mm' HS. rewrite (Mem.load_store_same _ _ _ _ _ _ HS). reflexivity. }
    assert (HO : forall j j' w mm mm', j <> j' -> Mem.store Mint8unsigned mm bp (o + j') (Vint w) = Some mm' ->
      Mem.load Mint8unsigned mm' bp (o + j) = Mem.load Mint8unsigned mm bp (o + j)).
    { intros j j' w mm mm' Hne HS. apply (Mem.load_store_other _ _ _ _ _ _ HS).
      right. change (size_chunk Mint8unsigned) with 1. lia. }
    destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [| | | | | | | |lia].
    + change (o + Z.of_nat 0) with (o + 0). cbn [nth c_be64_bytes]. rewrite (HO 0 7 _ _ _ ltac:(lia) S8). rewrite (HO 0 6 _ _ _ ltac:(lia) S7). rewrite (HO 0 5 _ _ _ ltac:(lia) S6). rewrite (HO 0 4 _ _ _ ltac:(lia) S5). rewrite (HO 0 3 _ _ _ ltac:(lia) S4). rewrite (HO 0 2 _ _ _ ltac:(lia) S3). rewrite (HO 0 1 _ _ _ ltac:(lia) S2). rewrite (HL 0 _ _ _ S1). unfold c_be64_shift. rewrite !zero_ext8_idem. reflexivity.
    + change (o + Z.of_nat 1) with (o + 1). cbn [nth c_be64_bytes]. rewrite (HO 1 7 _ _ _ ltac:(lia) S8). rewrite (HO 1 6 _ _ _ ltac:(lia) S7). rewrite (HO 1 5 _ _ _ ltac:(lia) S6). rewrite (HO 1 4 _ _ _ ltac:(lia) S5). rewrite (HO 1 3 _ _ _ ltac:(lia) S4). rewrite (HO 1 2 _ _ _ ltac:(lia) S3). rewrite (HL 1 _ _ _ S2). unfold c_be64_shift, c_be64_low. rewrite zero_ext8_idem. reflexivity.
    + change (o + Z.of_nat 2) with (o + 2). cbn [nth c_be64_bytes]. rewrite (HO 2 7 _ _ _ ltac:(lia) S8). rewrite (HO 2 6 _ _ _ ltac:(lia) S7). rewrite (HO 2 5 _ _ _ ltac:(lia) S6). rewrite (HO 2 4 _ _ _ ltac:(lia) S5). rewrite (HO 2 3 _ _ _ ltac:(lia) S4). rewrite (HL 2 _ _ _ S3). unfold c_be64_shift, c_be64_low. rewrite zero_ext8_idem. reflexivity.
    + change (o + Z.of_nat 3) with (o + 3). cbn [nth c_be64_bytes]. rewrite (HO 3 7 _ _ _ ltac:(lia) S8). rewrite (HO 3 6 _ _ _ ltac:(lia) S7). rewrite (HO 3 5 _ _ _ ltac:(lia) S6). rewrite (HO 3 4 _ _ _ ltac:(lia) S5). rewrite (HL 3 _ _ _ S4). unfold c_be64_shift, c_be64_low. rewrite zero_ext8_idem. reflexivity.
    + change (o + Z.of_nat 4) with (o + 4). cbn [nth c_be64_bytes]. rewrite (HO 4 7 _ _ _ ltac:(lia) S8). rewrite (HO 4 6 _ _ _ ltac:(lia) S7). rewrite (HO 4 5 _ _ _ ltac:(lia) S6). rewrite (HL 4 _ _ _ S5). unfold c_be64_shift, c_be64_low. rewrite zero_ext8_idem. reflexivity.
    + change (o + Z.of_nat 5) with (o + 5). cbn [nth c_be64_bytes]. rewrite (HO 5 7 _ _ _ ltac:(lia) S8). rewrite (HO 5 6 _ _ _ ltac:(lia) S7). rewrite (HL 5 _ _ _ S6). unfold c_be64_shift, c_be64_low. rewrite zero_ext8_idem. reflexivity.
    + change (o + Z.of_nat 6) with (o + 6). cbn [nth c_be64_bytes]. rewrite (HO 6 7 _ _ _ ltac:(lia) S8). rewrite (HL 6 _ _ _ S7). unfold c_be64_shift, c_be64_low. rewrite zero_ext8_idem. reflexivity.
    + change (o + Z.of_nat 7) with (o + 7). cbn [nth c_be64_bytes]. rewrite (HL 7 _ _ _ S8). unfold c_be64_shift, c_be64_low. rewrite zero_ext8_idem. reflexivity.
  - intros ch b ofs Hc.
    rewrite (Mem.load_store_other _ _ _ _ _ _ S8)
      by (change (size_chunk Mint8unsigned) with 1; destruct Hc as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]).
    rewrite (Mem.load_store_other _ _ _ _ _ _ S7)
      by (change (size_chunk Mint8unsigned) with 1; destruct Hc as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]).
    rewrite (Mem.load_store_other _ _ _ _ _ _ S6)
      by (change (size_chunk Mint8unsigned) with 1; destruct Hc as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]).
    rewrite (Mem.load_store_other _ _ _ _ _ _ S5)
      by (change (size_chunk Mint8unsigned) with 1; destruct Hc as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]).
    rewrite (Mem.load_store_other _ _ _ _ _ _ S4)
      by (change (size_chunk Mint8unsigned) with 1; destruct Hc as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]).
    rewrite (Mem.load_store_other _ _ _ _ _ _ S3)
      by (change (size_chunk Mint8unsigned) with 1; destruct Hc as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]).
    rewrite (Mem.load_store_other _ _ _ _ _ _ S2)
      by (change (size_chunk Mint8unsigned) with 1; destruct Hc as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]).
    rewrite (Mem.load_store_other _ _ _ _ _ _ S1)
      by (change (size_chunk Mint8unsigned) with 1; destruct Hc as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]).
    reflexivity.
  - intros b Hv.
    eapply Mem.store_valid_block_1; [exact S8|].
    eapply Mem.store_valid_block_1; [exact S7|].
    eapply Mem.store_valid_block_1; [exact S6|].
    eapply Mem.store_valid_block_1; [exact S5|].
    eapply Mem.store_valid_block_1; [exact S4|].
    eapply Mem.store_valid_block_1; [exact S3|].
    eapply Mem.store_valid_block_1; [exact S2|].
    eapply Mem.store_valid_block_1; [exact S1|].
    exact Hv.
Qed.

(** ** sha256_u64be *)
Require sha.SHA256 sha.common_lemmas.
Require Import C.jet_memcpy_model C.jet_readBit_layout.
Require Import C.jet_sha_compress_call C.jet_sha_block_local C.jet_sha_ctx8_model.
Require Import C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec.

Local Transparent sha_ge.
Lemma sha_u64be_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_u64be = Some (sha_symbol_block _sha256_u64be).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_u64be_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_u64be) Ptrofs.zero) =
    Some (Internal f_sha256_u64be).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_uchars_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_uchars = Some (sha_symbol_block _sha256_uchars).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_uchars_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_uchars) Ptrofs.zero) =
    Some (Internal f_sha256_uchars).
Proof. vm_compute; reflexivity. Qed.

Definition u64_env (bb : block) : env := PTree.set _buf (bb, tarray tuchar 8) empty_env.
Definition u64_temps (bx : block) (cbase : Z) (x : int64) : temp_env :=
  PTree.set _x (Vlong x) (PTree.set _ctx (Vptr bx (Ptrofs.repr cbase))
    (create_undef_temps (fn_temps f_sha256_u64be))).

Lemma u64_blocks bb : blocks_of_env sha_ge (u64_env bb) = [(bb, 0, 8)].
Proof. vm_compute. reflexivity. Qed.

Lemma u64_entry m m1 bb bx cbase x :
  Mem.alloc m 0 8 = (m1, bb) ->
  function_entry2 sha_ge f_sha256_u64be [Vptr bx (Ptrofs.repr cbase); Vlong x] m
    (u64_env bb) (u64_temps bx cbase x) m1.
Proof.
  intros HA. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros a b HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bb).
    + change (Mem.alloc m 0 8 = (m1, bb)); exact HA.
    + constructor.
  - reflexivity.
Qed.
Local Opaque sha_ge.

Lemma absorb_i_cons_small l regs x bs : (length l < 63)%nat ->
  absorb_i l regs (x :: bs) = absorb_i (l ++ [x]) regs bs.
Proof.
  intros HL. unfold absorb_i. cbn [fold_left]. unfold absorb_step_i at 2. cbn [fst snd].
  assert (HE : Nat.eqb (length (l ++ [x])) 64 = false)
    by (apply Nat.eqb_neq; rewrite app_length; cbn [length]; lia).
  rewrite HE. reflexivity.
Qed.

Lemma absorb_i_cons_full l regs x bs : length l = 63%nat ->
  absorb_i l regs (x :: bs) = absorb_i [] (SHA256.hash_block regs (be_words (l ++ [x]))) bs.
Proof.
  intros HL. unfold absorb_i. cbn [fold_left]. unfold absorb_step_i at 2. cbn [fst snd].
  assert (HE : Nat.eqb (length (l ++ [x])) 64 = true)
    by (apply Nat.eqb_eq; rewrite app_length; cbn [length]; lia).
  rewrite HE. reflexivity.
Qed.

Lemma absorb_i_shape bs : forall l regs, (length l < 64)%nat -> length regs = 8%nat ->
  Z.of_nat (length (fst (absorb_i l regs bs))) = (Z.of_nat (length l) + Z.of_nat (length bs)) mod 64 /\
  (length (fst (absorb_i l regs bs)) < 64)%nat /\ length (snd (absorb_i l regs bs)) = 8%nat.
Proof.
  induction bs as [|x bs IH]; intros l regs HL HR.
  - unfold absorb_i. cbn [fold_left fst snd length]. rewrite Z.add_0_r, Z.mod_small by lia. auto.
  - destruct (Nat.eq_dec (length l) 63) as [E|E].
    + rewrite absorb_i_cons_full by exact E.
      destruct (IH [] (SHA256.hash_block regs (be_words (l ++ [x]))) ltac:(cbn; lia)) as (H1 & H2 & H3).
      { apply sha.common_lemmas.length_hash_block; [exact HR|].
        apply be_words_length. rewrite app_length. cbn [length]. lia. }
      split; [|split; assumption]. rewrite H1. cbn [length]. rewrite E.
      replace (Z.of_nat 63 + Z.of_nat (S (length bs))) with (Z.of_nat 0 + Z.of_nat (length bs) + 1 * 64) by lia.
      rewrite Z.mod_add by lia. reflexivity.
    + rewrite absorb_i_cons_small by lia.
      destruct (IH (l ++ [x]) regs ltac:(rewrite app_length; cbn [length]; lia) HR) as (H1 & H2 & H3).
      split; [|split; assumption]. rewrite H1, app_length. cbn [length]. f_equal. lia.
Qed.

Theorem eval_sha256_u64be (Hmodel : memcpy_model) m bx cbase bo obase
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
  let bs := c_be64_bytes x in
  let ovf' := uc_overflow ovf c (Int64.repr 8) in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_u64be)
      [Vptr bx (Ptrofs.repr cbase); Vlong x] E0 m' (Vint (bit_int (negb ovf'))) /\
    Mem.load Mptr m' bx cbase = Some (Vptr bo (Ptrofs.repr obase)) /\
    Mem.load Mint64 m' bx (cbase + 8) = Some (Vlong (Int64.add c (Int64.repr 8))) /\
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
  destruct (Mem.alloc m 0 8) as [m1 bb] eqn:A1.
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
  assert (PB1 : Mem.range_perm m1 bb 0 8 Cur Freeable).
  { intros ofs Hr0. eapply Mem.perm_alloc_2; eauto. }
  destruct (eval_sha_WriteBE64 m1 bb Ptrofs.zero x
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
  { change (Ptrofs.unsigned Ptrofs.zero) with 0. cbn [bs c_be64_bytes length].
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
  change (Z.of_nat (length bs)) with 8 in HUc, HCnt3, HOvf3. fold ovf' in HUc, HOvf3.
  assert (Vb2 : Mem.valid_block m2 bb) by (apply HV2; eapply Mem.valid_new_block; exact A1).
  destruct (free_list_blocks [(bb, 0, 8)] m3) as (mf & HFL & HLf & HPf & HVf).
  { intros b0 lo hi [Heq|[]]. injection Heq as <- <- <-. intros ofs Hr0.
    apply HPerm3; [exact Vb2|]. apply HP2, PB1, Hr0. }
  { repeat constructor; cbn; tauto. }
  cbn [map fst] in HLf, HPf.
  assert (HNb : forall b0, Mem.valid_block m b0 -> ~ In b0 [bb]).
  { intros b0 Hv [Heq|[]]. exact (Fb b0 Hv (eq_sym Heq)). }
  assert (V2 : forall b0, Mem.valid_block m b0 -> Mem.valid_block m2 b0).
  { intros b0 Hv. apply HV2, XV, Hv. }
  exists mf. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - eapply eval_funcall_internal with (e := u64_env bb) (le1 := u64_temps bx cbase x) (m1 := m1)
      (le2 := PTree.set _t'1 (Vint (bit_int (negb ovf'))) (u64_temps bx cbase x)) (m2 := m3)
      (out := Out_return (Some (Vint (bit_int (negb ovf')), tbool))).
    + apply u64_entry; exact A1.
    + cbn [f_sha256_u64be fn_body].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := u64_temps bx cbase x) (m1 := m2).
      { change (u64_temps bx cbase x) with (set_opttemp None Vundef (u64_temps bx cbase x)) at 2.
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _WriteBE64) Ptrofs.zero)
          (vargs := [Vptr bb Ptrofs.zero; Vlong x]) (f := Internal f_WriteBE64).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_WriteBE64_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs.
          + eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity].
          + reflexivity.
          + eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|apply eval_Enil].
        - exact sha_WriteBE64_funct.
        - reflexivity.
        - exact HW. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      { change (PTree.set _t'1 (Vint (bit_int (negb ovf'))) (u64_temps bx cbase x)) with
          (set_opttemp (Some _t'1) (Vint (bit_int (negb ovf'))) (u64_temps bx cbase x)).
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_uchars) Ptrofs.zero)
          (vargs := [Vptr bx (Ptrofs.repr cbase); Vptr bb Ptrofs.zero; Vlong (Int64.repr 8)])
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
    + rewrite u64_blocks. exact HFL.
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
