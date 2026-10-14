(** A concrete [memcmp]: the Clight translation of the byte loop in
    [jet_memcmp_impl.c] satisfies the libc contract
    ([jet_memcmp_model.memcmp_model]) as an *internal* function, in every
    global environment: it leaves memory unchanged, emits no event and
    returns -1, 0 or 1 by the lexicographic comparison of the two ranges
    read as unsigned bytes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Zbits Integers AST Ctypes Cop Clight Maps Memdata.
From compcert Require Import ClightBigstep Memory Events Globalenvs Values.
Require Import C.memcmp_impl C.jet_memcmp_model.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 60.

Definition mc_s1 : statement :=
  ltac:(let b := eval cbv delta [f_memcmp fn_body] beta iota in (fn_body f_memcmp) in
        lazymatch b with
        | Ssequence _ (Ssequence _ (Ssequence (Ssequence _ (Sloop ?s1 _)) _)) => exact s1
        end).
Definition mc_s2 : statement :=
  ltac:(let b := eval cbv delta [f_memcmp fn_body] beta iota in (fn_body f_memcmp) in
        lazymatch b with
        | Ssequence _ (Ssequence _ (Ssequence (Ssequence _ (Sloop _ ?s2)) _)) => exact s2
        end).

Lemma memcmp_body_shape :
  fn_body f_memcmp =
    Ssequence (Sset _p (Etempvar _a (tptr tvoid)))
      (Ssequence (Sset _q (Etempvar _b (tptr tvoid)))
        (Ssequence
          (Ssequence (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong)) (Sloop mc_s1 mc_s2))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))).
Proof. reflexivity. Qed.

(** The value the reference implementation returns. *)
Definition memcmp_ret (c : Datatypes.comparison) : int :=
  match c with
  | Eq => Int.zero
  | Lt => Int.neg (Int.repr 1)
  | Gt => Int.repr 1
  end.

Lemma memcmp_ret_sign c : memcmp_sign c (memcmp_ret c).
Proof. destruct c; cbn; [reflexivity|vm_compute; reflexivity|vm_compute; reflexivity]. Qed.

Definition mc_out (c : Datatypes.comparison) : outcome :=
  match c with
  | Eq => Out_normal
  | _ => Out_return (Some (Vint (memcmp_ret c), tint))
  end.

Lemma mc_index_offset o i :
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

Lemma mc_byte_range m b ofs x :
  Mem.load Mint8unsigned m b ofs = Some (Vint x) -> 0 <= Int.unsigned x < 256.
Proof.
  intros HL. pose proof (Mem.load_cast _ _ _ _ _ HL) as HC. cbn in HC.
  injection HC as HC. rewrite HC. change 256 with (two_p 8). apply Int.zero_ext_range.
  change Int.zwordsize with 32. lia.
Qed.

Lemma mc_byte_signed x : 0 <= Int.unsigned x < 256 -> Int.signed x = Int.unsigned x.
Proof.
  intros Hx. unfold Int.signed.
  destruct (zlt (Int.unsigned x) Int.half_modulus) as [_|HH];
    [reflexivity|change Int.half_modulus with 2147483648 in HH; lia].
Qed.

Section Loop.
Variable ge : genv.
Variables (m : mem) (b1 b2 : block) (o1 o2 : ptrofs) (n : Z).
Hypothesis Hn : n <= Int64.max_unsigned.
Hypothesis H1end : Ptrofs.unsigned o1 + n <= Ptrofs.modulus.
Hypothesis H2end : Ptrofs.unsigned o2 + n <= Ptrofs.modulus.

Lemma mc_load le id b o i x :
  le!id = Some (Vptr b o) -> le!_i = Some (Vlong (Int64.repr i)) ->
  0 <= i -> Ptrofs.unsigned o + i < Ptrofs.modulus ->
  Mem.load Mint8unsigned m b (Ptrofs.unsigned o + i) = Some (Vint x) ->
  eval_expr ge empty_env le m
    (Ederef (Ebinop Oadd (Etempvar id (tptr tuchar)) (Etempvar _i tulong) (tptr tuchar)) tuchar)
    (Vint x).
Proof.
  intros Hid Hi Hi0 Hlt HL. eapply eval_Elvalue.
  - eapply eval_Ederef. eapply eval_Ebinop; [apply eval_Etempvar; exact Hid|apply eval_Etempvar; exact Hi|reflexivity].
  - eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv.
    rewrite mc_index_offset by assumption. exact HL.
Qed.

Lemma mc_loop_exec : forall l1 l2 i le,
  length l1 = length l2 -> 0 <= i -> i + Z.of_nat (length l1) = n ->
  bytes_at m b1 (Ptrofs.unsigned o1 + i) l1 -> bytes_at m b2 (Ptrofs.unsigned o2 + i) l2 ->
  le!_i = Some (Vlong (Int64.repr i)) -> le!_n = Some (Vlong (Int64.repr n)) ->
  le!_p = Some (Vptr b1 o1) -> le!_q = Some (Vptr b2 o2) ->
  exists le',
    Clight2.exec_stmt ge empty_env le m (Sloop mc_s1 mc_s2) E0 le' m (mc_out (bytes_cmp l1 l2)).
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] i le HLen Hi Hsum HB1 HB2 Hli Hln Hlp Hlq; try discriminate HLen.
  - cbn [length Z.of_nat] in Hsum. assert (i = n) by lia. subst i.
    exists le. cbn [bytes_cmp mc_out].
    eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
    cbv delta [mc_s1] beta iota.
    change E0 with (E0 ** E0). eapply exec_Sseq_2; [|discriminate].
    eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
    + eapply eval_Ebinop; [apply eval_Etempvar; exact Hli|apply eval_Etempvar; exact Hln|].
      change (Some (Val.of_bool (Int64.ltu (Int64.repr n) (Int64.repr n))) = Some Vfalse).
      unfold Int64.ltu. rewrite zlt_false by lia. reflexivity.
    + reflexivity.
    + constructor.
  - cbn [length] in Hsum, HLen.
    assert (Hin : i < n) by lia.
    pose proof (Ptrofs.unsigned_range o1) as Ho1. pose proof (Ptrofs.unsigned_range o2) as Ho2.
    pose proof (HB1 0%nat ltac:(cbn; lia)) as HX. pose proof (HB2 0%nat ltac:(cbn; lia)) as HY.
    cbn [nth Z.of_nat] in HX, HY. rewrite Z.add_0_r in HX, HY.
    pose proof (mc_byte_range _ _ _ _ HX) as Rx. pose proof (mc_byte_range _ _ _ _ HY) as Ry.
    set (le2 := PTree.set _t'2 (Vint x) le).
    set (le3 := PTree.set _t'3 (Vint y) le2).
    assert (H3i : le3!_i = Some (Vlong (Int64.repr i))) by (unfold le3, le2; rewrite !PTree.gso by (vm_compute; discriminate); exact Hli).
    assert (H3p : le3!_p = Some (Vptr b1 o1)) by (unfold le3, le2; rewrite !PTree.gso by (vm_compute; discriminate); exact Hlp).
    assert (H3q : le3!_q = Some (Vptr b2 o2)) by (unfold le3, le2; rewrite !PTree.gso by (vm_compute; discriminate); exact Hlq).
    assert (H3n : le3!_n = Some (Vlong (Int64.repr n))) by (unfold le3, le2; rewrite !PTree.gso by (vm_compute; discriminate); exact Hln).
    assert (HCond : Clight2.exec_stmt ge empty_env le m
      (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _n tulong) tint) Sskip Sbreak)
      E0 le m Out_normal).
    { eapply exec_Sifthenelse with (v1 := Vtrue) (b := true).
      - eapply eval_Ebinop; [apply eval_Etempvar; exact Hli|apply eval_Etempvar; exact Hln|].
        change (Some (Val.of_bool (Int64.ltu (Int64.repr i) (Int64.repr n))) = Some Vtrue).
        unfold Int64.ltu. rewrite (Int64.unsigned_repr i), (Int64.unsigned_repr n) by lia.
        rewrite zlt_true by lia. reflexivity.
      - reflexivity.
      - constructor. }
    assert (HS2 : Clight2.exec_stmt ge empty_env le m
      (Sset _t'2 (Ederef (Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar _i tulong) (tptr tuchar)) tuchar))
      E0 le2 m Out_normal).
    { apply exec_Sset. eapply mc_load; [exact Hlp|exact Hli|lia|lia|exact HX]. }
    assert (HS3 : Clight2.exec_stmt ge empty_env le2 m
      (Sset _t'3 (Ederef (Ebinop Oadd (Etempvar _q (tptr tuchar)) (Etempvar _i tulong) (tptr tuchar)) tuchar))
      E0 le3 m Out_normal).
    { apply exec_Sset. eapply mc_load;
        [unfold le2; rewrite PTree.gso by (vm_compute; discriminate); exact Hlq
        |unfold le2; rewrite PTree.gso by (vm_compute; discriminate); exact Hli|lia|lia|exact HY]. }
    cbn [bytes_cmp].
    destruct (Int.eq x y) eqn:HE.
    + (* equal bytes: next iteration *)
      pose proof (Int.eq_spec x y) as HS. rewrite HE in HS. subst y.
      rewrite Z.compare_refl.
      set (le4 := PTree.set _i (Vlong (Int64.repr (i + 1))) le3).
      destruct (IH l2 (i + 1) le4) as (le' & HEx).
      * injection HLen; auto.
      * lia.
      * lia.
      * intros j Hj. replace (Ptrofs.unsigned o1 + (i + 1) + Z.of_nat j) with
          (Ptrofs.unsigned o1 + i + Z.of_nat (S j)) by lia. apply (HB1 (S j)). cbn; lia.
      * intros j Hj. replace (Ptrofs.unsigned o2 + (i + 1) + Z.of_nat j) with
          (Ptrofs.unsigned o2 + i + Z.of_nat (S j)) by lia. apply (HB2 (S j)).
        cbn [length]. injection HLen as HLen. lia.
      * apply PTree.gss.
      * unfold le4. rewrite PTree.gso by (vm_compute; discriminate). exact H3n.
      * unfold le4. rewrite PTree.gso by (vm_compute; discriminate). exact H3p.
      * unfold le4. rewrite PTree.gso by (vm_compute; discriminate). exact H3q.
      * exists le'. change E0 with (E0 ** E0 ** E0).
        eapply exec_Sloop_loop with (le1 := le3) (m1 := m) (le2 := le4) (m2 := m) (out1 := Out_normal);
          [|constructor| |exact HEx].
        -- cbv delta [mc_s1] beta iota.
           eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HCond|].
           eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HS2|].
           eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HS3|].
           eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
           ++ eapply eval_Ebinop; [apply eval_Etempvar; unfold le3; rewrite PTree.gso by (vm_compute; discriminate); apply PTree.gss
                                  |apply eval_Etempvar; apply PTree.gss|].
              cbn. unfold sem_cmp, sem_binarith. cbn. rewrite Int.eq_true. reflexivity.
           ++ reflexivity.
           ++ constructor.
        -- cbv delta [mc_s2] beta iota. apply exec_Sset.
           eapply eval_Ebinop; [apply eval_Etempvar; exact H3i|apply eval_Econst_int|].
           change (Some (Vlong (Int64.add (Int64.repr i) (Int64.repr (Int.signed (Int.repr 1))))) =
                   Some (Vlong (Int64.repr (i + 1)))).
           do 2 f_equal. unfold Int64.add. rewrite (Int64.unsigned_repr i) by lia. reflexivity.
    + (* first difference: return *)
      assert (Hne : Int.unsigned x <> Int.unsigned y).
      { intros E. pose proof (Int.eq_spec x y) as HS. rewrite HE in HS. apply HS.
        rewrite <- (Int.repr_unsigned x), <- (Int.repr_unsigned y), E. reflexivity. }
      set (le4 := PTree.set _t'4 (Vint x) le3).
      set (le5 := PTree.set _t'5 (Vint y) le4).
      set (c := Z.compare (Int.unsigned x) (Int.unsigned y)).
      assert (Hc : c <> Eq) by (unfold c; intros E; apply Z.compare_eq in E; contradiction).
      assert (HLt : Int.lt x y = match c with Lt => true | _ => false end).
      { unfold Int.lt. rewrite !mc_byte_signed by assumption. unfold c.
        destruct (zlt (Int.unsigned x) (Int.unsigned y)) as [H|H].
        - rewrite (proj2 (Z.compare_lt_iff _ _) H). reflexivity.
        - assert (HG : (Int.unsigned x ?= Int.unsigned y) = Gt) by (apply Z.compare_gt_iff; lia).
          rewrite HG. reflexivity. }
      assert (HOo : mc_out (match c with Eq => bytes_cmp l1 l2 | Lt => Lt | Gt => Gt end) =
                    Out_return (Some (Vint (memcmp_ret c), tint)))
        by (destruct c; [contradiction|reflexivity|reflexivity]).
      rewrite HOo.
      exists (PTree.set _t'1 (Vint (memcmp_ret c)) le5).
      eapply exec_Sloop_stop1 with (out' := Out_return (Some (Vint (memcmp_ret c), tint))); [|constructor].
      cbv delta [mc_s1] beta iota.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HCond|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HS2|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HS3|].
      eapply exec_Sifthenelse with (v1 := Vtrue) (b := true).
      * eapply eval_Ebinop; [apply eval_Etempvar; unfold le3; rewrite PTree.gso by (vm_compute; discriminate); apply PTree.gss
                            |apply eval_Etempvar; apply PTree.gss|].
        cbn. unfold sem_cmp, sem_binarith. cbn. rewrite HE. reflexivity.
      * reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := PTree.set _t'1 (Vint (memcmp_ret c)) le5) (m1 := m).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m).
           { apply exec_Sset. eapply mc_load; [exact H3p|exact H3i|lia|lia|exact HX]. }
           eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le5) (m1 := m).
           { apply exec_Sset. eapply mc_load;
               [unfold le4; rewrite PTree.gso by (vm_compute; discriminate); exact H3q
               |unfold le4; rewrite PTree.gso by (vm_compute; discriminate); exact H3i|lia|lia|exact HY]. }
           assert (HCmp : eval_expr ge empty_env le5 m
             (Ebinop Olt (Etempvar _t'4 tuchar) (Etempvar _t'5 tuchar) tint) (Val.of_bool (Int.lt x y))).
           { eapply eval_Ebinop; [apply eval_Etempvar; unfold le5; rewrite PTree.gso by (vm_compute; discriminate); apply PTree.gss
                                 |apply eval_Etempvar; apply PTree.gss|].
             cbn. unfold sem_cmp, sem_binarith. cbn. reflexivity. }
           rewrite HLt in HCmp.
           destruct c; [contradiction| |].
           ++ eapply exec_Sifthenelse with (v1 := Vtrue) (b := true); [exact HCmp|reflexivity|].
              apply exec_Sset. eapply eval_Ecast with (v1 := Vint (Int.neg (Int.repr 1)));
                [eapply eval_Eunop; [apply eval_Econst_int|reflexivity]|reflexivity].
           ++ eapply exec_Sifthenelse with (v1 := Vfalse) (b := false); [exact HCmp|reflexivity|].
              apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
        -- apply exec_Sreturn_some. apply eval_Etempvar. apply PTree.gss.
Qed.
End Loop.

Theorem eval_memcmp_impl (ge : genv) m b1 o1 b2 o2 (l1 l2 : list int) :
  length l1 = length l2 ->
  Z.of_nat (length l1) <= Int64.max_unsigned ->
  Ptrofs.unsigned o1 + Z.of_nat (length l1) <= Ptrofs.max_unsigned + 1 ->
  Ptrofs.unsigned o2 + Z.of_nat (length l1) <= Ptrofs.max_unsigned + 1 ->
  bytes_at m b1 (Ptrofs.unsigned o1) l1 -> bytes_at m b2 (Ptrofs.unsigned o2) l2 ->
  Clight2.eval_funcall ge m (Internal f_memcmp)
    [Vptr b1 o1; Vptr b2 o2; Vlong (Int64.repr (Z.of_nat (length l1)))] E0 m
    (Vint (memcmp_ret (bytes_cmp l1 l2))).
Proof.
  intros HLen Hn H1e H2e HB1 HB2.
  set (n := Z.of_nat (length l1)) in *.
  pose (lei := create_undef_temps (fn_temps f_memcmp)).
  destruct (bind_parameter_temps (fn_params f_memcmp)
    [Vptr b1 o1; Vptr b2 o2; Vlong (Int64.repr n)] lei) as [le1|] eqn:Hbind;
    [|discriminate Hbind].
  assert (H1a : le1!_a = Some (Vptr b1 o1)) by (injection Hbind as <-; reflexivity).
  assert (H1b : le1!_b = Some (Vptr b2 o2)) by (injection Hbind as <-; reflexivity).
  assert (H1n : le1!_n = Some (Vlong (Int64.repr n))) by (injection Hbind as <-; reflexivity).
  set (le2 := PTree.set _p (Vptr b1 o1) le1).
  set (le3 := PTree.set _q (Vptr b2 o2) le2).
  set (le4 := PTree.set _i (Vlong (Int64.repr 0)) le3).
  destruct (mc_loop_exec ge m b1 b2 o1 o2 n Hn
      ltac:(unfold Ptrofs.max_unsigned in H1e; lia)
      ltac:(unfold Ptrofs.max_unsigned in H2e; lia) l1 l2 0 le4 HLen)
    as [le' HEx].
  - lia.
  - unfold n. lia.
  - rewrite Z.add_0_r. exact HB1.
  - rewrite Z.add_0_r. exact HB2.
  - apply PTree.gss.
  - unfold le4, le3, le2. rewrite !PTree.gso by (vm_compute; discriminate). exact H1n.
  - unfold le4, le3. rewrite !PTree.gso by (vm_compute; discriminate). apply PTree.gss.
  - unfold le4. rewrite PTree.gso by (vm_compute; discriminate). apply PTree.gss.
  - assert (HPre : Clight2.exec_stmt ge empty_env le1 m
      (Ssequence (Sset _p (Etempvar _a (tptr tvoid)))
        (Ssequence (Sset _q (Etempvar _b (tptr tvoid)))
          (Ssequence
            (Ssequence (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong)) (Sloop mc_s1 mc_s2))
            (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
      E0 le' m (Out_return (Some (Vint (memcmp_ret (bytes_cmp l1 l2)), tint)))).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m).
      { apply exec_Sset. apply eval_Etempvar. exact H1a. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m).
      { apply exec_Sset. apply eval_Etempvar. unfold le2. rewrite PTree.gso by (vm_compute; discriminate). exact H1b. }
      destruct (bytes_cmp l1 l2) eqn:HC; cbn [mc_out] in HEx.
      - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le') (m1 := m).
        + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m); [|exact HEx].
          apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
        + apply exec_Sreturn_some. apply eval_Econst_int.
      - change E0 with (E0 ** E0). eapply exec_Sseq_2; [|discriminate].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m); [|exact HEx].
        apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
      - change E0 with (E0 ** E0). eapply exec_Sseq_2; [|discriminate].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m); [|exact HEx].
        apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity]. }
    eapply eval_funcall_internal with (e := empty_env) (le1 := le1) (m1 := m)
      (le2 := le') (m2 := m) (out := Out_return (Some (Vint (memcmp_ret (bytes_cmp l1 l2)), tint))).
    + constructor.
      * apply list_norepet_nil.
      * vm_compute.
        repeat (apply list_norepet_cons; [cbn; intuition discriminate|]).
        apply list_norepet_nil.
      * intros x y Hx Hy. vm_compute in Hx, Hy. intuition (subst; discriminate).
      * constructor.
      * exact Hbind.
    + rewrite memcmp_body_shape. exact HPre.
    + cbn. split; [discriminate|reflexivity].
    + reflexivity.
Qed.

(** The reference implementation meets the result contract of the model. *)
Corollary eval_memcmp_impl_sign (ge : genv) m b1 o1 b2 o2 (l1 l2 : list int) :
  length l1 = length l2 ->
  Z.of_nat (length l1) <= Int64.max_unsigned ->
  Ptrofs.unsigned o1 + Z.of_nat (length l1) <= Ptrofs.max_unsigned + 1 ->
  Ptrofs.unsigned o2 + Z.of_nat (length l1) <= Ptrofs.max_unsigned + 1 ->
  bytes_at m b1 (Ptrofs.unsigned o1) l1 -> bytes_at m b2 (Ptrofs.unsigned o2) l2 ->
  exists r,
    Clight2.eval_funcall ge m (Internal f_memcmp)
      [Vptr b1 o1; Vptr b2 o2; Vlong (Int64.repr (Z.of_nat (length l1)))] E0 m (Vint r) /\
    memcmp_sign (bytes_cmp l1 l2) r.
Proof.
  intros. exists (memcmp_ret (bytes_cmp l1 l2)). split; [apply eval_memcmp_impl; assumption|apply memcmp_ret_sign].
Qed.
