(** A concrete [memcpy]: the Clight translation of the byte loop in
    [jet_memcpy_impl.c] satisfies the libc contract used by the jet proofs
    ([jet_memcpy_model.memcpy_model]) as an *internal* function, in every
    global environment, for source ranges holding initialized data bytes.

    The data-byte premise is a legitimate requirement of this implementation:
    Clight's [unsigned char] load of an undefined byte or pointer fragment is
    [Vundef], which the assignment's cast rejects. *)
From Coq Require Import ZArith List Lia Classical_Prop.
From compcert Require Import Coqlib Zbits Integers AST Ctypes Cop Clight Maps Memdata.
From compcert Require Import ClightBigstep Memory Events Globalenvs Values.
Require Import C.memcpy_impl.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 60.

Definition memcpy_loop : statement :=
  Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _n tulong) tint)
        Sskip Sbreak)
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd (Etempvar _s (tptr tuchar)) (Etempvar _i tulong)
              (tptr tuchar)) tuchar))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _d (tptr tuchar)) (Etempvar _i tulong)
              (tptr tuchar)) tuchar)
          (Etempvar _t'1 tuchar))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint) tulong)).

Lemma memcpy_body_shape :
  fn_body f_memcpy =
    Ssequence (Sset _d (Etempvar _dest (tptr tvoid)))
      (Ssequence (Sset _s (Etempvar _src (tptr tvoid)))
        (Ssequence
          (Ssequence (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
            memcpy_loop)
          (Sreturn (Some (Etempvar _dest (tptr tvoid)))))).
Proof. reflexivity. Qed.

Lemma memcpy_index_offset o i :
  0 <= i -> Ptrofs.unsigned o + i < Ptrofs.modulus ->
  Ptrofs.unsigned
    (Ptrofs.add o (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr i)))) =
  Ptrofs.unsigned o + i.
Proof.
  intros Hi Hlt.
  pose proof (Ptrofs.unsigned_range o) as Ho.
  assert (Hm : Ptrofs.modulus = Int64.modulus) by reflexivity.
  assert (Hof : Ptrofs.of_int64 (Int64.repr i) = Ptrofs.repr i).
  { unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr; [reflexivity|].
    unfold Int64.max_unsigned. lia. }
  rewrite Hof, Ptrofs.mul_commut, Ptrofs.mul_one.
  unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr i) by (unfold Ptrofs.max_unsigned; lia).
  apply Ptrofs.unsigned_repr. unfold Ptrofs.max_unsigned. lia.
Qed.

(** Memory equalities.  CompCert proves these two facts with its separate
    axiom [Axioms.proof_irr]; here the proof components of the memory record
    are identified by proof irrelevance derived from [classic], which the
    accepted proofs already inherit, so no further assumption is used. *)
Lemma memcpy_mkmem_ext cont1 cont2 acc1 acc2 next1 next2 a1 a2 b1 b2 c1 c2 :
  cont1 = cont2 -> acc1 = acc2 -> next1 = next2 ->
  Mem.mkmem cont1 acc1 next1 a1 b1 c1 = Mem.mkmem cont2 acc2 next2 a2 b2 c2.
Proof.
  intros; subst; f_equal; apply Classical_Prop.proof_irrelevance.
Qed.

Section MemoryEqualities.
Local Transparent Mem.store Mem.storebytes.

Lemma memcpy_store_storebytes m b ofs chunk v m' :
  Mem.store chunk m b ofs v = Some m' ->
  Mem.storebytes m b ofs (encode_val chunk v) = Some m'.
Proof.
  intros H. unfold Mem.storebytes. unfold Mem.store in H.
  destruct (Mem.valid_access_dec m chunk b ofs Writable) as [v0|]; inv H.
  destruct (Mem.range_perm_dec m b ofs
    (ofs + Z.of_nat (length (encode_val chunk v))) Cur Writable) as [r|n].
  - f_equal. apply memcpy_mkmem_ext; auto.
  - elim n. rewrite encode_val_length. rewrite <- size_chunk_conv.
    destruct v0; auto.
Qed.

Lemma memcpy_storebytes_concat m b ofs bytes1 m1 bytes2 m2 :
  Mem.storebytes m b ofs bytes1 = Some m1 ->
  Mem.storebytes m1 b (ofs + Z.of_nat (length bytes1)) bytes2 = Some m2 ->
  Mem.storebytes m b ofs (bytes1 ++ bytes2) = Some m2.
Proof.
  intros ST1 ST2. pose proof ST1 as ST1'. revert ST1 ST2.
  unfold Mem.storebytes; intros ST1 ST2.
  destruct (Mem.range_perm_dec m b ofs (ofs + Z.of_nat (length bytes1)) Cur Writable)
    as [r|]; try congruence.
  destruct (Mem.range_perm_dec m1 b (ofs + Z.of_nat (length bytes1))
    (ofs + Z.of_nat (length bytes1) + Z.of_nat (length bytes2)) Cur Writable)
    as [r0|]; try congruence.
  destruct (Mem.range_perm_dec m b ofs
    (ofs + Z.of_nat (length (bytes1 ++ bytes2))) Cur Writable) as [r1|n].
  - inv ST1; inv ST2; simpl. f_equal. apply memcpy_mkmem_ext; auto.
    rewrite PMap.gss. rewrite Mem.setN_concat. symmetry. apply PMap.set2.
  - elim n. rewrite app_length. rewrite Nat2Z.inj_add. red; intros ofs0 Hofs0.
    destruct (zlt ofs0 (ofs + Z.of_nat (length bytes1))).
    + apply r. lia.
    + eapply Mem.perm_storebytes_2; [exact ST1'|]. apply r0. lia.
Qed.
End MemoryEqualities.

Lemma memcpy_byte_roundtrip x :
  exists k, decode_val Mint8unsigned [Byte x] = Vint k /\
    encode_val Mint8unsigned (Vint (Int.zero_ext 8 k)) = [Byte x].
Proof.
  eexists. split; [reflexivity|].
  set (d := decode_int [x]).
  assert (Hd : d = Byte.unsigned x).
  { unfold d, decode_int, rev_if_be. cbn [Archi.big_endian int_of_bytes]. lia. }
  pose proof (Byte.unsigned_range x) as Hx. change Byte.modulus with 256 in Hx.
  assert (Heq : Zbits.eqmod (two_p 8)
    (Int.unsigned (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr d)))) (Byte.unsigned x)).
  { eapply Zbits.eqmod_trans; [apply (Int.eqmod_zero_ext 8); change Int.zwordsize with 32; lia|].
    eapply Zbits.eqmod_trans; [apply (Int.eqmod_zero_ext 8); change Int.zwordsize with 32; lia|].
    rewrite Hd, Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
    apply Zbits.eqmod_refl. }
  unfold encode_val. rewrite (encode_int_8_mod _ _ Heq).
  unfold encode_int, rev_if_be, bytes_of_int. cbn.
  rewrite Byte.repr_unsigned. reflexivity.
Qed.

(** One iteration's memory effect: an initialized source byte is read and the
    same byte is stored at the destination. *)
Lemma memcpy_byte_step m bs so bd do x :
  Mem.loadbytes m bs so 1 = Some [Byte x] ->
  Mem.range_perm m bd do (do + 1) Cur Writable ->
  exists k m',
    Mem.load Mint8unsigned m bs so = Some (Vint k) /\
    Mem.store Mint8unsigned m bd do (Vint (Int.zero_ext 8 k)) = Some m' /\
    Mem.storebytes m bd do [Byte x] = Some m'.
Proof.
  intros HL HP.
  destruct (memcpy_byte_roundtrip x) as [k [Hdec Henc]].
  assert (HVA : Mem.valid_access m Mint8unsigned bd do Writable).
  { split; [exact HP|apply Z.divide_1_l]. }
  destruct (Mem.valid_access_store m Mint8unsigned bd do (Vint (Int.zero_ext 8 k)) HVA)
    as [m' HS].
  exists k, m'. split; [|split; [exact HS|]].
  - rewrite (Mem.loadbytes_load Mint8unsigned m bs so [Byte x] HL (Z.divide_1_l _)).
    rewrite Hdec. reflexivity.
  - rewrite <- Henc. apply memcpy_store_storebytes. exact HS.
Qed.

Section Loop.
Variable ge : genv.
Variables (bs bd : block) (os od : ptrofs) (n : Z).
Hypothesis Hn : n <= Int64.max_unsigned.
Hypothesis Hsrc_end : Ptrofs.unsigned os + n <= Ptrofs.modulus.
Hypothesis Hdst_end : Ptrofs.unsigned od + n <= Ptrofs.modulus.
Hypothesis Hsep : bs <> bd \/ Ptrofs.unsigned os + n <= Ptrofs.unsigned od \/
  Ptrofs.unsigned od + n <= Ptrofs.unsigned os.

Lemma memcpy_loop_exec : forall bl i m le,
  0 <= i -> i + Z.of_nat (length bl) = n ->
  Mem.loadbytes m bs (Ptrofs.unsigned os + i) (Z.of_nat (length bl)) = Some (inj_bytes bl) ->
  Mem.range_perm m bd (Ptrofs.unsigned od + i) (Ptrofs.unsigned od + n) Cur Writable ->
  le!_i = Some (Vlong (Int64.repr i)) -> le!_n = Some (Vlong (Int64.repr n)) ->
  le!_d = Some (Vptr bd od) -> le!_s = Some (Vptr bs os) ->
  exists m' le',
    Clight2.exec_stmt ge empty_env le m memcpy_loop E0 le' m' Out_normal /\
    (bl = nil -> m' = m) /\
    (bl <> nil -> Mem.storebytes m bd (Ptrofs.unsigned od + i) (inj_bytes bl) = Some m') /\
    le'!_dest = le!_dest.
Proof.
  induction bl as [|x bl IH]; intros i m le Hi Hlen HL HP Hli Hln Hld Hls.
  - cbn [length Z.of_nat] in Hlen. assert (i = n) by lia. subst i.
    exists m, le. split; [|split; [reflexivity|split; [congruence|reflexivity]]].
    eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
    change E0 with (E0 ** E0). eapply exec_Sseq_2; [|discriminate].
    eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
    + eapply eval_Ebinop; [apply eval_Etempvar; exact Hli|apply eval_Etempvar; exact Hln|].
      cbn. unfold sem_cmp, sem_binarith. cbn. unfold Val.of_bool, Int64.ltu.
      rewrite zlt_false by lia. reflexivity.
    + reflexivity.
    + constructor.
  - assert (Hlen' : (i + 1) + Z.of_nat (length bl) = n).
    { rewrite <- Hlen. cbn [length]. lia. }
    assert (Hin : i < n) by lia.
    pose proof (Ptrofs.unsigned_range os) as Hos.
    pose proof (Ptrofs.unsigned_range od) as Hod.
    assert (HLs : Mem.loadbytes m bs (Ptrofs.unsigned os + i)
        (1 + Z.of_nat (length bl)) = Some (inj_bytes (x :: bl))).
    { replace (1 + Z.of_nat (length bl)) with (Z.of_nat (length (x :: bl)))
        by (cbn [length]; lia). exact HL. }
    destruct (Mem.loadbytes_split _ _ _ _ _ _ HLs ltac:(lia) ltac:(lia))
      as [b1 [b2 [HL1 [HL2 Hb]]]].
    assert (Hb1 : b1 = [Byte x] /\ b2 = inj_bytes bl).
    { pose proof (Mem.loadbytes_length _ _ _ _ _ HL1) as Hl1.
      change (Z.to_nat 1) with 1%nat in Hl1.
      destruct b1 as [|y [|z b1]]; try discriminate Hl1.
      cbn in Hb. injection Hb as H1 H2. subst y b2. split; reflexivity. }
    destruct Hb1 as [-> ->].
    assert (HPbyte : Mem.range_perm m bd (Ptrofs.unsigned od + i)
        (Ptrofs.unsigned od + i + 1) Cur Writable).
    { intros o Ho. apply HP. lia. }
    destruct (memcpy_byte_step m bs _ bd _ x HL1 HPbyte)
      as [k [m1 [Hload [Hstore Hsb]]]].
    assert (HL' : Mem.loadbytes m1 bs (Ptrofs.unsigned os + (i + 1))
        (Z.of_nat (length bl)) = Some (inj_bytes bl)).
    { rewrite Z.add_assoc.
      rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ Hsb); [exact HL2|lia|].
      cbn [length Z.of_nat Pos.of_succ_nat].
      destruct Hsep as [Hne | [Hlt | Hlt]]; [left; exact Hne|right; left; lia|right; right; lia]. }
    assert (HP' : Mem.range_perm m1 bd (Ptrofs.unsigned od + (i + 1))
        (Ptrofs.unsigned od + n) Cur Writable).
    { intros o Ho. eapply Mem.perm_storebytes_1; [exact Hsb|]. apply HP. lia. }
    set (le1 := PTree.set _t'1 (Vint k) le).
    set (le2 := PTree.set _i (Vlong (Int64.repr (i + 1))) le1).
    assert (Hti : _t'1 <> _i) by (vm_compute; discriminate).
    assert (Htn : _t'1 <> _n) by (vm_compute; discriminate).
    assert (Htd : _t'1 <> _d) by (vm_compute; discriminate).
    assert (Hts : _t'1 <> _s) by (vm_compute; discriminate).
    assert (Hin' : _i <> _n) by (vm_compute; discriminate).
    assert (Hid : _i <> _d) by (vm_compute; discriminate).
    assert (His : _i <> _s) by (vm_compute; discriminate).
    assert (Hdt : _dest <> _t'1) by (vm_compute; discriminate).
    assert (Hdi : _dest <> _i) by (vm_compute; discriminate).
    destruct (IH (i + 1) m1 le2 ltac:(lia) Hlen' HL' HP') as [m' [le' [Hexec [Hnil [Hcons Hdest]]]]].
    { unfold le2. apply PTree.gss. }
    { unfold le2, le1. rewrite !PTree.gso by congruence. exact Hln. }
    { unfold le2, le1. rewrite !PTree.gso by congruence. exact Hld. }
    { unfold le2, le1. rewrite !PTree.gso by congruence. exact Hls. }
    exists m', le'. split; [|split; [discriminate|split]].
    + change E0 with (E0 ** E0 ** E0).
      eapply exec_Sloop_loop with (out1 := Out_normal) (le1 := le1) (m1 := m1)
        (le2 := le2) (m2 := m1); [|constructor| |exact Hexec].
      * change E0 with (E0 ** E0). eapply exec_Sseq_1 with (le1 := le) (m1 := m).
        { eapply exec_Sifthenelse with (v1 := Vtrue) (b := true).
          - eapply eval_Ebinop; [apply eval_Etempvar; exact Hli|apply eval_Etempvar; exact Hln|].
            cbn. unfold sem_cmp, sem_binarith. cbn. unfold Val.of_bool, Int64.ltu.
            rewrite !Int64.unsigned_repr by lia.
            rewrite zlt_true by lia. reflexivity.
          - reflexivity.
          - constructor. }
        change E0 with (E0 ** E0). eapply exec_Sseq_1 with (le1 := le1) (m1 := m).
        { apply exec_Sset. eapply eval_Elvalue.
          - apply eval_Ederef. eapply eval_Ebinop;
              [apply eval_Etempvar; exact Hls|apply eval_Etempvar; exact Hli|reflexivity].
          - eapply deref_loc_value; [reflexivity|].
            unfold Mem.loadv. rewrite memcpy_index_offset by lia. exact Hload. }
        eapply exec_Sassign with (v2 := Vint k) (v := Vint (Int.zero_ext 8 k)).
        { apply eval_Ederef. eapply eval_Ebinop;
            [apply eval_Etempvar; unfold le1; rewrite PTree.gso by congruence; exact Hld
            |apply eval_Etempvar; unfold le1; rewrite PTree.gso by congruence; exact Hli
            |reflexivity]. }
        { apply eval_Etempvar. unfold le1. apply PTree.gss. }
        { reflexivity. }
        { eapply assign_loc_value; [reflexivity|].
          unfold Mem.storev. rewrite memcpy_index_offset by lia. exact Hstore. }
      * apply exec_Sset. eapply eval_Ebinop;
          [apply eval_Etempvar; unfold le1; rewrite PTree.gso by congruence; exact Hli
          |apply eval_Econst_int|].
        cbn. unfold sem_add, sem_binarith. cbn. do 2 f_equal.
        rewrite Int64.add_unsigned. rewrite Int64.unsigned_repr by lia.
        reflexivity.
    + intros _. destruct bl as [|y bl'].
      * rewrite (Hnil eq_refl). exact Hsb.
      * change (inj_bytes (x :: y :: bl')) with ([Byte x] ++ inj_bytes (y :: bl')).
        eapply memcpy_storebytes_concat; [exact Hsb|].
        change (Z.of_nat (length [Byte x])) with 1. rewrite <- Z.add_assoc.
        apply Hcons. discriminate.
    + rewrite Hdest. unfold le2, le1. rewrite !PTree.gso by congruence. reflexivity.
Qed.
End Loop.

(** The whole call.  Apart from the data-byte source the premises are those
    of [memcpy_model]; block validity is implied by the loaded and writable
    ranges.  The result is the destination pointer, the trace is empty, and
    the final memory is exactly the [storebytes] of the loaded bytes: no
    block is allocated or freed, since the function has no addressable
    locals. *)
Theorem eval_memcpy_impl (ge : genv) m bd od bs os n bl :
  Mem.loadbytes m bs (Ptrofs.unsigned os) n = Some (inj_bytes bl) ->
  Mem.range_perm m bd (Ptrofs.unsigned od) (Ptrofs.unsigned od + n) Cur Writable ->
  (bs <> bd \/ Ptrofs.unsigned os + n <= Ptrofs.unsigned od \/
    Ptrofs.unsigned od + n <= Ptrofs.unsigned os) ->
  0 < n <= Int64.max_unsigned ->
  Ptrofs.unsigned os + n <= Ptrofs.max_unsigned + 1 ->
  Ptrofs.unsigned od + n <= Ptrofs.max_unsigned + 1 ->
  exists m', Mem.storebytes m bd (Ptrofs.unsigned od) (inj_bytes bl) = Some m' /\
    Clight2.eval_funcall ge m (Internal f_memcpy)
      [Vptr bd od; Vptr bs os; Vlong (Int64.repr n)] E0 m' (Vptr bd od).
Proof.
  intros HL HP Hsep Hn Hse Hde.
  assert (Hlen : Z.of_nat (length bl) = n).
  { pose proof (Mem.loadbytes_length _ _ _ _ _ HL) as H.
    rewrite length_inj_bytes in H. rewrite H. apply Z2Nat.id. lia. }
  pose (lei := create_undef_temps (fn_temps f_memcpy)).
  destruct (bind_parameter_temps (fn_params f_memcpy)
    [Vptr bd od; Vptr bs os; Vlong (Int64.repr n)] lei) as [le1|] eqn:Hbind;
    [|discriminate Hbind].
  set (le2 := PTree.set _d (Vptr bd od) le1).
  set (le3 := PTree.set _s (Vptr bs os) le2).
  set (le4 := PTree.set _i (Vlong (Int64.repr 0)) le3).
  assert (H1dest : le1!_dest = Some (Vptr bd od)).
  { injection Hbind as <-. reflexivity. }
  assert (H1src : le1!_src = Some (Vptr bs os)).
  { injection Hbind as <-. reflexivity. }
  assert (H1n : le1!_n = Some (Vlong (Int64.repr n))).
  { injection Hbind as <-. reflexivity. }
  assert (Hne1 : _s <> _d) by (vm_compute; discriminate).
  assert (Hne2 : _i <> _d) by (vm_compute; discriminate).
  assert (Hne3 : _i <> _s) by (vm_compute; discriminate).
  assert (Hne4 : _n <> _d) by (vm_compute; discriminate).
  assert (Hne5 : _n <> _s) by (vm_compute; discriminate).
  assert (Hne6 : _n <> _i) by (vm_compute; discriminate).
  assert (Hne7 : _dest <> _d) by (vm_compute; discriminate).
  assert (Hne8 : _dest <> _s) by (vm_compute; discriminate).
  assert (Hne9 : _dest <> _i) by (vm_compute; discriminate).
  assert (Hne10 : _src <> _d) by (vm_compute; discriminate).
  destruct (memcpy_loop_exec ge bs bd os od n ltac:(lia)
      ltac:(unfold Ptrofs.max_unsigned in Hse; lia)
      ltac:(unfold Ptrofs.max_unsigned in Hde; lia) Hsep bl 0 m le4)
    as [m' [le' [Hexec [_ [Hstore Hdest]]]]].
  - lia.
  - lia.
  - rewrite Z.add_0_r, Hlen. exact HL.
  - rewrite Z.add_0_r. exact HP.
  - unfold le4. apply PTree.gss.
  - unfold le4, le3, le2. rewrite !PTree.gso by congruence. exact H1n.
  - unfold le4, le3, le2. rewrite !PTree.gso by congruence. apply PTree.gss.
  - unfold le4, le3. rewrite PTree.gso by congruence. apply PTree.gss.
  - exists m'. split.
    + rewrite Z.add_0_r in Hstore. apply Hstore. intros ->. cbn in Hlen. lia.
    + eapply eval_funcall_internal with (e := empty_env) (le1 := le1) (m1 := m)
        (le2 := le') (m2 := m')
        (out := Out_return (Some (Vptr bd od, tptr tvoid))).
      * constructor.
        { apply list_norepet_nil. }
        { vm_compute.
          repeat (apply list_norepet_cons; [cbn; intuition discriminate|]).
          apply list_norepet_nil. }
        { intros x y Hx Hy. vm_compute in Hx, Hy. intuition (subst; discriminate). }
        { constructor. }
        { exact Hbind. }
      * rewrite memcpy_body_shape.
        change E0 with (E0 ** E0). eapply exec_Sseq_1 with (le1 := le2) (m1 := m).
        { apply exec_Sset. apply eval_Etempvar. exact H1dest. }
        change E0 with (E0 ** E0). eapply exec_Sseq_1 with (le1 := le3) (m1 := m).
        { apply exec_Sset. apply eval_Etempvar. unfold le2.
          rewrite PTree.gso by congruence. exact H1src. }
        change E0 with (E0 ** E0). eapply exec_Sseq_1 with (le1 := le') (m1 := m').
        { change E0 with (E0 ** E0). eapply exec_Sseq_1 with (le1 := le4) (m1 := m).
          - apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
          - exact Hexec. }
        apply exec_Sreturn_some. apply eval_Etempvar. rewrite Hdest.
        unfold le4, le3, le2. rewrite !PTree.gso by congruence. exact H1dest.
      * split; [discriminate|reflexivity].
      * reflexivity.
Qed.
