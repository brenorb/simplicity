(** A concrete [memcpy] meeting the libc contract exactly: the Clight
    translation of [jet_memcpy_exact.c], which moves each byte with CompCert's
    defined one-byte block copy [EF_memcpy 1 1], satisfies the conclusion of
    [jet_memcpy_model.memcpy_model] as an *internal* function in every global
    environment, for arbitrary memory values and under exactly the model's
    premises.  Only CompCert's defined builtin semantics is used; the abstract
    external-function parameter is not involved. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Memdata.
From compcert Require Import ClightBigstep Memory Events Globalenvs Values.
Require C.jet_memcpy_impl.
Require Import C.memcpy_exact.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 60.

Definition memcpy_loop : statement :=
  Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _n tulong) tint)
        Sskip Sbreak)
      (Sbuiltin None (EF_memcpy 1 1)
        (Tcons (tptr tuchar) (Tcons (tptr tuchar) Tnil))
        ((Ebinop Oadd (Etempvar _d (tptr tuchar)) (Etempvar _i tulong)
           (tptr tuchar)) ::
         (Ebinop Oadd (Etempvar _s (tptr tuchar)) (Etempvar _i tulong)
           (tptr tuchar)) :: nil)))
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
  Mem.loadbytes m bs (Ptrofs.unsigned os + i) (Z.of_nat (length bl)) = Some bl ->
  Mem.range_perm m bd (Ptrofs.unsigned od + i) (Ptrofs.unsigned od + n) Cur Writable ->
  le!_i = Some (Vlong (Int64.repr i)) -> le!_n = Some (Vlong (Int64.repr n)) ->
  le!_d = Some (Vptr bd od) -> le!_s = Some (Vptr bs os) ->
  exists m' le',
    Clight2.exec_stmt ge empty_env le m memcpy_loop E0 le' m' Out_normal /\
    (bl = nil -> m' = m) /\
    (bl <> nil -> Mem.storebytes m bd (Ptrofs.unsigned od + i) bl = Some m') /\
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
        (1 + Z.of_nat (length bl)) = Some (x :: bl)).
    { replace (1 + Z.of_nat (length bl)) with (Z.of_nat (length (x :: bl)))
        by (cbn [length]; lia). exact HL. }
    destruct (Mem.loadbytes_split _ _ _ _ _ _ HLs ltac:(lia) ltac:(lia))
      as [b1 [b2 [HL1 [HL2 Hb]]]].
    assert (Hb1 : b1 = [x] /\ b2 = bl).
    { pose proof (Mem.loadbytes_length _ _ _ _ _ HL1) as Hl1.
      change (Z.to_nat 1) with 1%nat in Hl1.
      destruct b1 as [|y [|z b1]]; try discriminate Hl1.
      cbn in Hb. injection Hb as H1 H2. subst y b2. split; reflexivity. }
    destruct Hb1 as [-> ->].
    assert (HPbyte : Mem.range_perm m bd (Ptrofs.unsigned od + i)
        (Ptrofs.unsigned od + i + Z.of_nat (length [x])) Cur Writable).
    { intros o Ho. apply HP. cbn [length Z.of_nat Pos.of_succ_nat] in Ho. lia. }
    destruct (Mem.range_perm_storebytes m bd _ [x] HPbyte) as [m1 Hsb].
    assert (HL' : Mem.loadbytes m1 bs (Ptrofs.unsigned os + (i + 1))
        (Z.of_nat (length bl)) = Some bl).
    { rewrite Z.add_assoc.
      rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ Hsb); [exact HL2|lia|].
      cbn [length Z.of_nat Pos.of_succ_nat].
      destruct Hsep as [Hne | [Hlt | Hlt]]; [left; exact Hne|right; left; lia|right; right; lia]. }
    assert (HP' : Mem.range_perm m1 bd (Ptrofs.unsigned od + (i + 1))
        (Ptrofs.unsigned od + n) Cur Writable).
    { intros o Ho. eapply Mem.perm_storebytes_1; [exact Hsb|]. apply HP. lia. }
    set (le2 := PTree.set _i (Vlong (Int64.repr (i + 1))) le).
    assert (Hin' : _i <> _n) by (vm_compute; discriminate).
    assert (Hid : _i <> _d) by (vm_compute; discriminate).
    assert (His : _i <> _s) by (vm_compute; discriminate).
    assert (Hdi : _dest <> _i) by (vm_compute; discriminate).
    destruct (IH (i + 1) m1 le2 ltac:(lia) Hlen' HL' HP') as [m' [le' [Hexec [Hnil [Hcons Hdest]]]]].
    { unfold le2. apply PTree.gss. }
    { unfold le2. rewrite !PTree.gso by congruence. exact Hln. }
    { unfold le2. rewrite !PTree.gso by congruence. exact Hld. }
    { unfold le2. rewrite !PTree.gso by congruence. exact Hls. }
    exists m', le'. split; [|split; [discriminate|split]].
    + change E0 with (E0 ** E0 ** E0).
      eapply exec_Sloop_loop with (out1 := Out_normal) (le1 := le) (m1 := m1)
        (le2 := le2) (m2 := m1); [|constructor| |exact Hexec].
      * change E0 with (E0 ** E0). eapply exec_Sseq_1 with (le1 := le) (m1 := m).
        { eapply exec_Sifthenelse with (v1 := Vtrue) (b := true).
          - eapply eval_Ebinop; [apply eval_Etempvar; exact Hli|apply eval_Etempvar; exact Hln|].
            cbn. unfold sem_cmp, sem_binarith. cbn. unfold Val.of_bool, Int64.ltu.
            rewrite !Int64.unsigned_repr by lia.
            rewrite zlt_true by lia. reflexivity.
          - reflexivity.
          - constructor. }
        change le with (set_opttemp None Vundef le) at 2.
        eapply exec_Sbuiltin.
        { eapply eval_Econs.
          - eapply eval_Ebinop;
              [apply eval_Etempvar; exact Hld|apply eval_Etempvar; exact Hli|reflexivity].
          - reflexivity.
          - eapply eval_Econs.
            + eapply eval_Ebinop;
                [apply eval_Etempvar; exact Hls|apply eval_Etempvar; exact Hli|reflexivity].
            + reflexivity.
            + apply eval_Enil. }
        change (extcall_memcpy_sem 1 1 ge
          [Vptr bd (Ptrofs.add od (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr i))));
           Vptr bs (Ptrofs.add os (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr i))))]
          m E0 Vundef m1).
        apply extcall_memcpy_sem_intro with (bytes := [x]).
        { left; reflexivity. }
        { lia. }
        { apply Z.divide_1_l. }
        { intros _. apply Z.divide_1_l. }
        { intros _. apply Z.divide_1_l. }
        { rewrite !jet_memcpy_impl.memcpy_index_offset by lia.
          destruct Hsep as [Hne | [Hlt | Hlt]];
            [left; exact Hne|right; right; left; lia|right; right; right; lia]. }
        { rewrite jet_memcpy_impl.memcpy_index_offset by lia. exact HL1. }
        { rewrite jet_memcpy_impl.memcpy_index_offset by lia. exact Hsb. }
      * apply exec_Sset. eapply eval_Ebinop;
          [apply eval_Etempvar; exact Hli|apply eval_Econst_int|].
        cbn. unfold sem_add, sem_binarith. cbn. do 2 f_equal.
        rewrite Int64.add_unsigned. rewrite Int64.unsigned_repr by lia.
        reflexivity.
    + intros _. destruct bl as [|y bl'].
      * rewrite (Hnil eq_refl). exact Hsb.
      * change (x :: y :: bl') with ([x] ++ y :: bl').
        eapply jet_memcpy_impl.memcpy_storebytes_concat; [exact Hsb|].
        change (Z.of_nat (length [x])) with 1. rewrite <- Z.add_assoc.
        apply Hcons. discriminate.
    + rewrite Hdest. unfold le2. rewrite !PTree.gso by congruence. reflexivity.
Qed.
End Loop.

(** The whole call.  The premises are those of [memcpy_model] (its two
    block-validity premises are not needed).  The result is the destination pointer, the trace is empty, and
    the final memory is exactly the [storebytes] of the loaded bytes: no
    block is allocated or freed, since the function has no addressable
    locals. *)
Theorem eval_memcpy_exact (ge : genv) m bd od bs os n bl :
  Mem.loadbytes m bs (Ptrofs.unsigned os) n = Some (bl) ->
  Mem.range_perm m bd (Ptrofs.unsigned od) (Ptrofs.unsigned od + n) Cur Writable ->
  (bs <> bd \/ Ptrofs.unsigned os + n <= Ptrofs.unsigned od \/
    Ptrofs.unsigned od + n <= Ptrofs.unsigned os) ->
  0 < n <= Int64.max_unsigned ->
  Ptrofs.unsigned os + n <= Ptrofs.max_unsigned + 1 ->
  Ptrofs.unsigned od + n <= Ptrofs.max_unsigned + 1 ->
  exists m', Mem.storebytes m bd (Ptrofs.unsigned od) (bl) = Some m' /\
    Clight2.eval_funcall ge m (Internal f_memcpy)
      [Vptr bd od; Vptr bs os; Vlong (Int64.repr n)] E0 m' (Vptr bd od).
Proof.
  intros HL HP Hsep Hn Hse Hde.
  assert (Hlen : Z.of_nat (length bl) = n).
  { pose proof (Mem.loadbytes_length _ _ _ _ _ HL) as H.
    rewrite H. apply Z2Nat.id. lia. }
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
