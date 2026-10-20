(** Execution of [WriteLE32(ptr, x)] (sha256.h) in the Elements environment
    unit: the four low bytes of [x] are stored in little-endian order. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec.
Require Import C.jets_elements C.jet_elements_support_sha_linkage C.jet_sha_ctx8_model C.jet_elements_support_sha_be32_exec C.jet_elements_support_sha_be64_exec C.jet_elements_support_sha_be32_write.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Lemma sha_WriteLE32_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _WriteLE32 = Some (sha_symbol_block _WriteLE32).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_WriteLE32_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _WriteLE32) Ptrofs.zero) =
    Some (Internal f_WriteLE32).
Proof. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

(** The value the C code computes for the byte of weight [2^k]. *)
Definition le32_long (x : int64) (k : Z) : int64 :=
  Int64.and c255 (Int64.shru x (Int64.repr (Int.unsigned (Int.repr k)))).
Definition le32_byte (x : int64) (k : Z) : int :=
  Int.zero_ext 8 (Int64.loword (if Z.eqb k 0 then Int64.and c255 x else le32_long x k)).

Definition c_le32_bytes (x : int64) : list int :=
  [le32_byte x 0; le32_byte x 8; le32_byte x 16; le32_byte x 24].

Definition wle32_le (bp : block) (op : ptrofs) (x : int64) : temp_env :=
  PTree.set _x (Vlong x) (PTree.set _ptr (Vptr bp op) (create_undef_temps (fn_temps f_WriteLE32))).

Lemma wle32_assign bp op x m m' i rhs v w :
  0 <= i <= 3 -> Ptrofs.unsigned op + 4 <= Ptrofs.max_unsigned ->
  eval_expr sha_ge empty_env (wle32_le bp op x) m rhs v ->
  sem_cast v (typeof rhs) tuchar m = Some (Vint w) ->
  Mem.store Mint8unsigned m bp (Ptrofs.unsigned op + i) (Vint w) = Some m' ->
  Clight2.exec_stmt sha_ge empty_env (wle32_le bp op x) m (Sassign (wbe_lhs i) rhs) E0
    (wle32_le bp op x) m' Out_normal.
Proof.
  intros Hi HM HE HC HS. unfold wbe_lhs.
  eapply exec_Sassign with (v2 := v) (v := Vint w).
  - eapply eval_Ederef. eapply eval_Ebinop; [apply eval_Etempvar; reflexivity|apply eval_Econst_int|reflexivity].
  - exact HE.
  - exact HC.
  - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
    rewrite ptr_byte_offset by lia. exact HS.
Qed.

Theorem eval_WriteLE32 m bp op x :
  Ptrofs.unsigned op + 4 <= Ptrofs.max_unsigned ->
  Mem.range_perm m bp (Ptrofs.unsigned op) (Ptrofs.unsigned op + 4) Cur Writable ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_WriteLE32) [Vptr bp op; Vlong x] E0 m' Vundef /\
    (forall i, (i < 4)%nat ->
       Mem.load Mint8unsigned m' bp (Ptrofs.unsigned op + Z.of_nat i) =
         Some (Vint (nth i (c_le32_bytes x) Int.zero))) /\
    (forall ch b ofs,
       (b <> bp \/ ofs + size_chunk ch <= Ptrofs.unsigned op \/ Ptrofs.unsigned op + 4 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HM HP.
  set (o := Ptrofs.unsigned op) in *.
  assert (HVA : forall mm i, 0 <= i <= 3 -> (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mm b ofs k p) ->
    Mem.valid_access mm Mint8unsigned bp (o + i) Writable).
  { intros mm i Hi Hpm. split; [|exists (o + i); cbn; lia]. intros ofs Ho. apply Hpm, HP.
    change (size_chunk Mint8unsigned) with 1 in Ho. lia. }
  destruct (Mem.valid_access_store m Mint8unsigned bp (o + 3) (Vint (Int.zero_ext 8 (le32_byte x 24)))
    (HVA m 3 ltac:(lia) (fun b ofs k p H => H))) as [m1 S1].
  assert (P1 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m1 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S1|]. exact Hp. }
  destruct (Mem.valid_access_store m1 Mint8unsigned bp (o + 2) (Vint (le32_byte x 16)) (HVA m1 2 ltac:(lia) P1)) as [m2 S2].
  assert (P2 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m2 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S2|]. apply P1; exact Hp. }
  destruct (Mem.valid_access_store m2 Mint8unsigned bp (o + 1) (Vint (le32_byte x 8)) (HVA m2 1 ltac:(lia) P2)) as [m3 S3].
  assert (P3 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m3 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S3|]. apply P2; exact Hp. }
  destruct (Mem.valid_access_store m3 Mint8unsigned bp (o + 0) (Vint (le32_byte x 0)) (HVA m3 0 ltac:(lia) P3)) as [m4 S4].
  assert (P4 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m4 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S4|]. apply P3; exact Hp. }
  exists m4. split; [|split; [|split; [|split; [exact P4|]]]].
  - eapply eval_funcall_internal with (e := empty_env) (le1 := wle32_le bp op x) (m1 := m)
      (le2 := wle32_le bp op x) (m2 := m4) (out := Out_normal).
    + apply function_entry2_intro.
      * apply list_norepet_nil.
      * cbn. repeat constructor; cbn; intuition discriminate.
      * intros x0 y0 HX HY. cbn in HY. contradiction.
      * apply alloc_variables_nil.
      * reflexivity.
    + cbn [f_WriteLE32 fn_body].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := wle32_le bp op x).
      { eapply (wle32_assign bp op x m m1 3); [lia|exact HM|wbe_rhs|reflexivity|exact S1]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2) (le1 := wle32_le bp op x).
      { eapply (wle32_assign bp op x m1 m2 2); [lia|exact HM|wbe_rhs|reflexivity|exact S2]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m3) (le1 := wle32_le bp op x).
      { eapply (wle32_assign bp op x m2 m3 1); [lia|exact HM|wbe_rhs|reflexivity|exact S3]. }
      eapply (wle32_assign bp op x m3 m4 0); [lia|exact HM|wbe_rhs|reflexivity|exact S4].
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
    assert (HI : forall k, Int.zero_ext 8 (le32_byte x k) = le32_byte x k)
      by (intros k; unfold le32_byte; apply zero_ext8_idem).
    destruct i as [|[|[|[|i]]]]; [| | | |lia].
    + change (o + Z.of_nat 0) with (o + 0). cbn [nth c_le32_bytes]. rewrite (HL 0 _ _ _ S4). rewrite HI. reflexivity.
    + change (o + Z.of_nat 1) with (o + 1). cbn [nth c_le32_bytes]. rewrite (HO 1 0 _ _ _ ltac:(lia) S4).
      rewrite (HL 1 _ _ _ S3). rewrite HI. reflexivity.
    + change (o + Z.of_nat 2) with (o + 2). cbn [nth c_le32_bytes]. rewrite (HO 2 0 _ _ _ ltac:(lia) S4).
      rewrite (HO 2 1 _ _ _ ltac:(lia) S3). rewrite (HL 2 _ _ _ S2). rewrite HI. reflexivity.
    + change (o + Z.of_nat 3) with (o + 3). cbn [nth c_le32_bytes]. rewrite (HO 3 0 _ _ _ ltac:(lia) S4).
      rewrite (HO 3 1 _ _ _ ltac:(lia) S3). rewrite (HO 3 2 _ _ _ ltac:(lia) S2). rewrite (HL 3 _ _ _ S1).
      rewrite !HI. reflexivity.
  - intros ch b ofs Hc.
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
    eapply Mem.store_valid_block_1; [exact S4|].
    eapply Mem.store_valid_block_1; [exact S3|].
    eapply Mem.store_valid_block_1; [exact S2|].
    eapply Mem.store_valid_block_1; [exact S1|].
    exact Hv.
Qed.

(** The bytes are the little-endian base-256 digits of the low 32 bits. *)
Lemma le32_byte_value (x : int64) (k : Z) : 0 <= k < 64 ->
  le32_byte x k = Int.repr ((Int64.unsigned x / 2 ^ k) mod 256).
Proof.
  intros Hk. unfold le32_byte. rewrite zero_ext8_loword. f_equal.
  destruct (Z.eqb_spec k 0) as [->|Hne].
  - rewrite Int64.and_commut, and255_unsigned. change (2 ^ 0) with 1. rewrite Z.div_1_r.
    apply Z.mod_mod. lia.
  - unfold le32_long. rewrite Int64.and_commut, and255_unsigned.
    rewrite (Int.unsigned_repr k) by (change Int.max_unsigned with 4294967295; lia).
    rewrite shru64_unsigned by lia. apply Z.mod_mod. lia.
Qed.

Lemma c_le32_bytes_length x : length (c_le32_bytes x) = 4%nat.
Proof. reflexivity. Qed.
