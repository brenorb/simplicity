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
