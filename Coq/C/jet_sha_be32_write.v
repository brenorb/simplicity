(** Execution of [WriteBE32] and [sha256_fromMidstate] in the SHA translation
    unit: a state of 32-bit words is written as its big-endian bytes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_ctx8_model C.jet_sha_be32_exec C.jet_sha_be64_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Lemma sha_WriteBE32_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _WriteBE32 = Some (sha_symbol_block _WriteBE32).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_WriteBE32_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _WriteBE32) Ptrofs.zero) =
    Some (Internal f_WriteBE32).
Proof. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

Definition c_be32_bytes (x : int64) : list int :=
  [Int.zero_ext 8 (Int64.loword (Int64.shru x (Int64.repr 24)));
   Int.zero_ext 8 (Int64.loword (Int64.and (Int64.shru x (Int64.repr 16)) c255));
   Int.zero_ext 8 (Int64.loword (Int64.and (Int64.shru x (Int64.repr 8)) c255));
   Int.zero_ext 8 (Int64.loword (Int64.and x c255))].

Definition wbe32_le (bp : block) (op : ptrofs) (x : int64) : temp_env :=
  PTree.set _x (Vlong x) (PTree.set _ptr (Vptr bp op) (create_undef_temps (fn_temps f_WriteBE32))).

Lemma wbe32_assign bp op x m m' i rhs v w :
  0 <= i <= 3 -> Ptrofs.unsigned op + 4 <= Ptrofs.max_unsigned ->
  eval_expr sha_ge empty_env (wbe32_le bp op x) m rhs v ->
  sem_cast v (typeof rhs) tuchar m = Some (Vint w) ->
  Mem.store Mint8unsigned m bp (Ptrofs.unsigned op + i) (Vint w) = Some m' ->
  Clight2.exec_stmt sha_ge empty_env (wbe32_le bp op x) m (Sassign (wbe_lhs i) rhs) E0
    (wbe32_le bp op x) m' Out_normal.
Proof.
  intros Hi HM HE HC HS. unfold wbe_lhs.
  eapply exec_Sassign with (v2 := v) (v := Vint w).
  - eapply eval_Ederef. eapply eval_Ebinop; [apply eval_Etempvar; reflexivity|apply eval_Econst_int|reflexivity].
  - exact HE.
  - exact HC.
  - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
    rewrite ptr_byte_offset by lia. exact HS.
Qed.

Theorem eval_sha_WriteBE32 m bp op x :
  Ptrofs.unsigned op + 4 <= Ptrofs.max_unsigned ->
  Mem.range_perm m bp (Ptrofs.unsigned op) (Ptrofs.unsigned op + 4) Cur Writable ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_WriteBE32) [Vptr bp op; Vlong x] E0 m' Vundef /\
    (forall i, (i < 4)%nat ->
       Mem.load Mint8unsigned m' bp (Ptrofs.unsigned op + Z.of_nat i) =
         Some (Vint (nth i (c_be32_bytes x) Int.zero))) /\
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
  destruct (Mem.valid_access_store m Mint8unsigned bp (o + 0) (Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int64.loword (Int64.shru x (Int64.repr 24)))))) (HVA m 0 ltac:(lia) (fun b ofs k p H => H))) as [m1 S1].
  assert (P1 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m1 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S1|]. exact Hp. }
  destruct (Mem.valid_access_store m1 Mint8unsigned bp (o + 1) (Vint (Int.zero_ext 8 (Int64.loword (Int64.and (Int64.shru x (Int64.repr 16)) c255)))) (HVA m1 1 ltac:(lia) P1)) as [m2 S2].
  assert (P2 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m2 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S2|]. apply P1; exact Hp. }
  destruct (Mem.valid_access_store m2 Mint8unsigned bp (o + 2) (Vint (Int.zero_ext 8 (Int64.loword (Int64.and (Int64.shru x (Int64.repr 8)) c255)))) (HVA m2 2 ltac:(lia) P2)) as [m3 S3].
  assert (P3 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m3 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S3|]. apply P2; exact Hp. }
  destruct (Mem.valid_access_store m3 Mint8unsigned bp (o + 3) (Vint (Int.zero_ext 8 (Int64.loword (Int64.and x c255)))) (HVA m3 3 ltac:(lia) P3)) as [m4 S4].
  assert (P4 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m4 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S4|]. apply P3; exact Hp. }
  exists m4. split; [|split; [|split; [|split; [exact P4|]]]].
  - eapply eval_funcall_internal with (e := empty_env) (le1 := wbe32_le bp op x) (m1 := m)
      (le2 := wbe32_le bp op x) (m2 := m4) (out := Out_normal).
    + apply function_entry2_intro.
      * apply list_norepet_nil.
      * cbn. repeat constructor; cbn; intuition discriminate.
      * intros x0 y0 HX HY. cbn in HY. contradiction.
      * apply alloc_variables_nil.
      * reflexivity.
    + cbn [f_WriteBE32 fn_body].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := wbe32_le bp op x).
      { eapply (wbe32_assign bp op x m m1 0); [lia|exact HM|wbe_rhs|reflexivity|exact S1]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2) (le1 := wbe32_le bp op x).
      { eapply (wbe32_assign bp op x m1 m2 1); [lia|exact HM|wbe_rhs|reflexivity|exact S2]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m3) (le1 := wbe32_le bp op x).
      { eapply (wbe32_assign bp op x m2 m3 2); [lia|exact HM|wbe_rhs|reflexivity|exact S3]. }
      eapply (wbe32_assign bp op x m3 m4 3); [lia|exact HM|wbe_rhs|reflexivity|exact S4].
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
    destruct i as [|[|[|[|i]]]]; [| | | |lia].
    + change (o + Z.of_nat 0) with (o + 0). cbn [nth c_be32_bytes]. rewrite (HO 0 3 _ _ _ ltac:(lia) S4). rewrite (HO 0 2 _ _ _ ltac:(lia) S3). rewrite (HO 0 1 _ _ _ ltac:(lia) S2). rewrite (HL 0 _ _ _ S1). rewrite !zero_ext8_idem. reflexivity.
    + change (o + Z.of_nat 1) with (o + 1). cbn [nth c_be32_bytes]. rewrite (HO 1 3 _ _ _ ltac:(lia) S4). rewrite (HO 1 2 _ _ _ ltac:(lia) S3). rewrite (HL 1 _ _ _ S2). rewrite !zero_ext8_idem. reflexivity.
    + change (o + Z.of_nat 2) with (o + 2). cbn [nth c_be32_bytes]. rewrite (HO 2 3 _ _ _ ltac:(lia) S4). rewrite (HL 2 _ _ _ S3). rewrite !zero_ext8_idem. reflexivity.
    + change (o + Z.of_nat 3) with (o + 3). cbn [nth c_be32_bytes]. rewrite (HL 3 _ _ _ S4). rewrite !zero_ext8_idem. reflexivity.
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

(** ** The bytes are the big-endian bytes of the word *)
Lemma zero_ext8_loword (y : int64) :
  Int.zero_ext 8 (Int64.loword y) = Int.repr (Int64.unsigned y mod 256).
Proof.
  unfold Int64.loword.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr (Int64.unsigned y)))).
  rewrite Int.zero_ext_mod by (change Int.zwordsize with 32; lia).
  rewrite Int.unsigned_repr_eq. change (two_p 8) with 256. f_equal.
  symmetry. apply Znumtheory.Zmod_div_mod; [lia|reflexivity|exists 16777216; reflexivity].
Qed.

Lemma and255_unsigned (y : int64) : Int64.unsigned (Int64.and y c255) = Int64.unsigned y mod 256.
Proof.
  change c255 with (Int64.repr (two_p 8 - 1)). rewrite <- Int64.zero_ext_and by lia.
  rewrite Int64.zero_ext_mod by (change Int64.zwordsize with 64; lia). reflexivity.
Qed.

Lemma shru64_unsigned (x : int64) (k : Z) : 0 <= k < 64 ->
  Int64.unsigned (Int64.shru x (Int64.repr k)) = Int64.unsigned x / 2 ^ k.
Proof.
  intros Hk. pose proof (Int64.unsigned_range x) as HX.
  rewrite Int64.shru_div_two_p.
  rewrite (Int64.unsigned_repr k) by (change Int64.max_unsigned with 18446744073709551615; lia).
  rewrite two_p_correct. apply Int64.unsigned_repr.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Int64.unsigned x / 2 ^ k <= Int64.unsigned x) by (apply Z.div_le_upper_bound; nia).
  assert (0 <= Int64.unsigned x / 2 ^ k) by (apply Z.div_pos; lia).
  unfold Int64.max_unsigned. lia.
Qed.

Lemma c_be32_bytes_word (w : int) :
  be_words (c_be32_bytes (Int64.repr (Int.unsigned w))) = [w].
Proof.
  pose proof (Int.unsigned_range w) as HW. change Int.modulus with 4294967296 in HW.
  set (W := Int.unsigned w) in *.
  assert (HX : Int64.unsigned (Int64.repr W) = W)
    by (apply Int64.unsigned_repr; change Int64.max_unsigned with 18446744073709551615; lia).
  unfold c_be32_bytes. cbn [be_words]. unfold be32.
  rewrite !zero_ext8_loword, !and255_unsigned.
  rewrite (shru64_unsigned (Int64.repr W) 24), (shru64_unsigned (Int64.repr W) 16),
    (shru64_unsigned (Int64.repr W) 8) by lia. rewrite HX.
  change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  pose proof (Z.div_mod W 256 ltac:(lia)) as D0. pose proof (Z.mod_pos_bound W 256 ltac:(lia)) as M0.
  assert (E1 : W / 65536 = W / 256 / 256) by (rewrite Z.div_div by lia; reflexivity).
  assert (E2 : W / 16777216 = W / 256 / 256 / 256) by (rewrite !Z.div_div by lia; reflexivity).
  set (a := W / 256) in *.
  pose proof (Z.div_mod a 256 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound a 256 ltac:(lia)) as M1.
  set (b := a / 256) in *.
  pose proof (Z.div_mod b 256 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound b 256 ltac:(lia)) as M2.
  set (c := b / 256) in *.
  assert (Hc : 0 <= c < 256) by lia.
  rewrite E1, E2. fold c.
  rewrite (Z.mod_small c 256) by lia.
  rewrite !Z.mod_mod by lia.
  rewrite !Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  f_equal. transitivity (Int.repr W); [f_equal; lia|apply Int.repr_unsigned].
Qed.

Definition be_bytes (ws : list int) : list int :=
  flat_map (fun w => c_be32_bytes (Int64.repr (Int.unsigned w))) ws.

Lemma be_bytes_length ws : length (be_bytes ws) = (4 * length ws)%nat.
Proof.
  induction ws as [|w ws IH]; [reflexivity|].
  unfold be_bytes in *. cbn [flat_map]. rewrite app_length, IH. cbn [length c_be32_bytes]. lia.
Qed.

Lemma be_words_be_bytes ws : be_words (be_bytes ws) = ws.
Proof.
  induction ws as [|w ws IH]; [reflexivity|].
  pose proof (c_be32_bytes_word w) as HW.
  unfold be_bytes in *. cbn [flat_map].
  unfold c_be32_bytes in HW |- *. cbn [app be_words] in HW |- *.
  apply (f_equal (fun l => hd Int.zero l)) in HW. cbn [hd] in HW. f_equal; [exact HW|exact IH].
Qed.

Lemma be_bytes_nth ws i j : (i < length ws)%nat -> (j < 4)%nat ->
  nth (4 * i + j) (be_bytes ws) Int.zero =
    nth j (c_be32_bytes (Int64.repr (Int.unsigned (nth i ws Int.zero)))) Int.zero.
Proof.
  revert i. induction ws as [|w ws IH]; intros i Hi Hj; [cbn in Hi; lia|].
  unfold be_bytes. cbn [flat_map]. fold (be_bytes ws).
  destruct i as [|i].
  - rewrite app_nth1 by (cbn; lia). reflexivity.
  - rewrite app_nth2 by (cbn [length c_be32_bytes]; lia).
    change (length (c_be32_bytes (Int64.repr (Int.unsigned w)))) with 4%nat.
    replace (4 * S i + j - 4)%nat with (4 * i + j)%nat by lia.
    cbn [nth]. apply IH; [cbn in Hi; lia|exact Hj].
Qed.
