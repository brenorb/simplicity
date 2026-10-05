(** Complete execution of [sha256_cmp_be(a, b)] (sha256.h): the
    lexicographic comparison of the eight words of two midstates. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_add_n_init C.jet_sha_hash_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Definition cmp_elem (p : ident) (i : Z) : expr :=
  Ederef (Ebinop Oadd (Efield (Ederef (Etempvar p (tptr MID)) MID) _s (tarray tuint 8))
    (Econst_int (Int.repr i) tint) (tptr tuint)) tuint.

Definition cmp_blk (i : Z) (ta tb tc td tr : ident) : statement :=
  Ssequence (Sset ta (cmp_elem _a i))
    (Ssequence (Sset tb (cmp_elem _b i))
      (Sifthenelse (Ebinop One (Etempvar ta tuint) (Etempvar tb tuint) tint)
        (Ssequence
          (Ssequence (Sset tc (cmp_elem _a i))
            (Ssequence (Sset td (cmp_elem _b i))
              (Sifthenelse (Ebinop Olt (Etempvar tc tuint) (Etempvar td tuint) tint)
                (Sset tr (Ecast (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint))
                (Sset tr (Ecast (Econst_int (Int.repr 1) tint) tint)))))
          (Sreturn (Some (Etempvar tr tint))))
        Sskip)).

Definition cmp_body : statement :=
  Ssequence (cmp_blk 0 _t'37 _t'38 _t'39 _t'40 _t'1)
  (Ssequence (cmp_blk 1 _t'33 _t'34 _t'35 _t'36 _t'2)
  (Ssequence (cmp_blk 2 _t'29 _t'30 _t'31 _t'32 _t'3)
  (Ssequence (cmp_blk 3 _t'25 _t'26 _t'27 _t'28 _t'4)
  (Ssequence (cmp_blk 4 _t'21 _t'22 _t'23 _t'24 _t'5)
  (Ssequence (cmp_blk 5 _t'17 _t'18 _t'19 _t'20 _t'6)
  (Ssequence (cmp_blk 6 _t'13 _t'14 _t'15 _t'16 _t'7)
  (Ssequence (cmp_blk 7 _t'9 _t'10 _t'11 _t'12 _t'8)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))).

Lemma cmp_body_eq : fn_body f_sha256_cmp_be = cmp_body.
Proof. reflexivity. Qed.

Definition cmp_res (x y : int) : int := if Int.ltu x y then Int.neg (Int.repr 1) else Int.repr 1.

Fixpoint cmp_model (xs ys : list int) : int :=
  match xs, ys with
  | x :: xs', y :: ys' => if Int.eq x y then cmp_model xs' ys' else cmp_res x y
  | _, _ => Int.zero
  end.

Lemma cmp_cmp_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_cmp_be = Some (sha_symbol_block _sha256_cmp_be).
Proof. vm_compute; reflexivity. Qed.
Lemma cmp_cmp_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_cmp_be) Ptrofs.zero) =
    Some (Internal f_sha256_cmp_be).
Proof. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

Lemma bool_val_of_bool (c : bool) m : bool_val (Val.of_bool c) tint m = Some c.
Proof. destruct c; reflexivity. Qed.

Section Cmp.
Variables (m : mem) (ba bb : block) (oa ob : ptrofs).
Hypothesis HoaM : Ptrofs.unsigned oa + 32 <= Ptrofs.max_unsigned.
Hypothesis HobM : Ptrofs.unsigned ob + 32 <= Ptrofs.max_unsigned.

Lemma cmp_elem_eval e le p b o i x :
  le!p = Some (Vptr b o) -> 0 <= i < 8 -> Ptrofs.unsigned o + 32 <= Ptrofs.max_unsigned ->
  Mem.load Mint32 m b (Ptrofs.unsigned o + 4 * i) = Some (Vint x) ->
  eval_expr sha_ge e le m (cmp_elem p i) (Vint x).
Proof.
  intros HP Hi HM HL. unfold cmp_elem. eapply eval_Elvalue.
  - eapply eval_Ederef.
    eapply eval_Ebinop with (v1 := Vptr b (Ptrofs.add o (Ptrofs.repr 0)));
      [|apply eval_Econst_int|reflexivity].
    eapply eval_Elvalue.
    + eapply eval_Efield_struct with (delta := 0).
      * eapply eval_Elvalue; [eapply eval_Ederef; apply eval_Etempvar; exact HP|apply deref_loc_copy; reflexivity].
      * reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
    + apply deref_loc_reference; reflexivity.
  - eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv.
    rewrite Ptrofs.add_zero. rewrite ptr_word_index by lia. exact HL.
Qed.

Lemma cmp_blk_exec e le i ta tb tc td tr x y :
  le!_a = Some (Vptr ba oa) -> le!_b = Some (Vptr bb ob) ->
  ta <> _a -> ta <> _b -> tb <> _a -> tb <> _b -> ta <> tb ->
  tc <> _a -> tc <> _b -> td <> _a -> td <> _b -> tc <> td ->
  0 <= i < 8 ->
  Mem.load Mint32 m ba (Ptrofs.unsigned oa + 4 * i) = Some (Vint x) ->
  Mem.load Mint32 m bb (Ptrofs.unsigned ob + 4 * i) = Some (Vint y) ->
  (x = y -> Clight2.exec_stmt sha_ge e le m (cmp_blk i ta tb tc td tr) E0
     (PTree.set tb (Vint y) (PTree.set ta (Vint x) le)) m Out_normal) /\
  (x <> y -> exists le', Clight2.exec_stmt sha_ge e le m (cmp_blk i ta tb tc td tr) E0
     le' m (Out_return (Some (Vint (cmp_res x y), tint)))).
Proof.
  intros HA HB N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 Hi HLa HLb.
  set (le1 := PTree.set ta (Vint x) le).
  set (le2 := PTree.set tb (Vint y) le1).
  assert (HA1 : le1!_a = Some (Vptr ba oa)) by (unfold le1; rewrite PTree.gso by auto; exact HA).
  assert (HB1 : le1!_b = Some (Vptr bb ob)) by (unfold le1; rewrite PTree.gso by auto; exact HB).
  assert (HA2 : le2!_a = Some (Vptr ba oa)) by (unfold le2; rewrite PTree.gso by auto; exact HA1).
  assert (HB2 : le2!_b = Some (Vptr bb ob)) by (unfold le2; rewrite PTree.gso by auto; exact HB1).
  assert (HS1 : Clight2.exec_stmt sha_ge e le m (Sset ta (cmp_elem _a i)) E0 le1 m Out_normal).
  { apply exec_Sset. eapply cmp_elem_eval; eauto. }
  assert (HS2 : Clight2.exec_stmt sha_ge e le1 m (Sset tb (cmp_elem _b i)) E0 le2 m Out_normal).
  { apply exec_Sset. eapply cmp_elem_eval; eauto. }
  assert (HC : eval_expr sha_ge e le2 m (Ebinop One (Etempvar ta tuint) (Etempvar tb tuint) tint)
    (Val.of_bool (negb (Int.eq x y)))).
  { eapply eval_Ebinop.
    - apply eval_Etempvar. unfold le2, le1. rewrite PTree.gso by auto. apply PTree.gss.
    - apply eval_Etempvar. unfold le2. apply PTree.gss.
    - reflexivity. }
  split.
  - intros Heq. unfold cmp_blk.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HS1|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HS2|].
    eapply exec_Sifthenelse with (b := false); [exact HC| |apply exec_Sskip].
    rewrite bool_val_of_bool. subst y. rewrite Int.eq_true. reflexivity.
  - intros Hne.
    set (le3 := PTree.set tc (Vint x) le2).
    set (le4 := PTree.set td (Vint y) le3).
    set (le5 := PTree.set tr (Vint (cmp_res x y)) le4).
    exists le5. unfold cmp_blk.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HS1|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HS2|].
    eapply exec_Sifthenelse with (b := true); [exact HC| |].
    { rewrite bool_val_of_bool, Int.eq_false by exact Hne. reflexivity. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le5) (m1 := m).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m).
      { apply exec_Sset. eapply cmp_elem_eval; eauto. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m).
      { apply exec_Sset. eapply cmp_elem_eval; eauto.
        unfold le3. rewrite PTree.gso by auto. exact HB2. }
      assert (HC2 : eval_expr sha_ge e le4 m (Ebinop Olt (Etempvar tc tuint) (Etempvar td tuint) tint)
        (Val.of_bool (Int.ltu x y))).
      { eapply eval_Ebinop.
        - apply eval_Etempvar. unfold le4, le3. rewrite PTree.gso by auto. apply PTree.gss.
        - apply eval_Etempvar. unfold le4. apply PTree.gss.
        - reflexivity. }
      eapply exec_Sifthenelse with (b := Int.ltu x y); [exact HC2|apply bool_val_of_bool|].
      unfold le5, cmp_res. destruct (Int.ltu x y).
      * apply exec_Sset. eapply eval_Ecast with (v1 := Vint (Int.neg (Int.repr 1))); [|reflexivity].
        eapply eval_Eunop; [apply eval_Econst_int|reflexivity].
      * apply exec_Sset. eapply eval_Ecast with (v1 := Vint (Int.repr 1)); [apply eval_Econst_int|reflexivity].
    + apply exec_Sreturn_some. apply eval_Etempvar. unfold le5. apply PTree.gss.
Qed.

End Cmp.

Section Chain.
Variables (m : mem) (ba bb : block) (oa ob : ptrofs).
Hypothesis HoaM : Ptrofs.unsigned oa + 32 <= Ptrofs.max_unsigned.
Hypothesis HobM : Ptrofs.unsigned ob + 32 <= Ptrofs.max_unsigned.

Definition cmp_good (le : temp_env) : Prop :=
  le!_a = Some (Vptr ba oa) /\ le!_b = Some (Vptr bb ob).

Lemma cmp_seq_step e le i ta tb tc td tr rest x y xs ys :
  cmp_good le ->
  ta <> _a -> ta <> _b -> tb <> _a -> tb <> _b -> ta <> tb ->
  tc <> _a -> tc <> _b -> td <> _a -> td <> _b -> tc <> td ->
  0 <= i < 8 ->
  Mem.load Mint32 m ba (Ptrofs.unsigned oa + 4 * i) = Some (Vint x) ->
  Mem.load Mint32 m bb (Ptrofs.unsigned ob + 4 * i) = Some (Vint y) ->
  (forall le', cmp_good le' -> exists le'',
     Clight2.exec_stmt sha_ge e le' m rest E0 le'' m (Out_return (Some (Vint (cmp_model xs ys), tint)))) ->
  exists le'',
    Clight2.exec_stmt sha_ge e le m (Ssequence (cmp_blk i ta tb tc td tr) rest) E0 le'' m
      (Out_return (Some (Vint (cmp_model (x :: xs) (y :: ys)), tint))).
Proof.
  intros [HA HB] N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 Hi HLa HLb HRest.
  destruct (cmp_blk_exec m ba bb oa ob HoaM HobM e le i ta tb tc td tr x y
    HA HB N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 Hi HLa HLb) as [HEq HNe].
  cbn [cmp_model].
  destruct (Int.eq_dec x y) as [E|E].
  - subst y. rewrite Int.eq_true.
    destruct (HRest (PTree.set tb (Vint x) (PTree.set ta (Vint x) le))) as [le'' HR].
    { split; rewrite !PTree.gso by auto; assumption. }
    exists le''. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact (HEq eq_refl)|exact HR].
  - rewrite Int.eq_false by exact E. destruct (HNe E) as [le' HX].
    exists le'. eapply exec_Sseq_2; [exact HX|discriminate].
Qed.

Theorem eval_sha256_cmp_be (xs ys : list int) :
  length xs = 8%nat -> length ys = 8%nat ->
  (forall j, (j < 8)%nat ->
     Mem.load Mint32 m ba (Ptrofs.unsigned oa + 4 * Z.of_nat j) = Some (Vint (nth j xs Int.zero))) ->
  (forall j, (j < 8)%nat ->
     Mem.load Mint32 m bb (Ptrofs.unsigned ob + 4 * Z.of_nat j) = Some (Vint (nth j ys Int.zero))) ->
  Clight2.eval_funcall sha_ge m (Internal f_sha256_cmp_be) [Vptr ba oa; Vptr bb ob] E0 m
    (Vint (cmp_model xs ys)).
Proof.
  intros HLx HLy HX HY.
  destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]]; try discriminate HLx.
  destruct ys as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|]]]]]]]]]; try discriminate HLy.
  set (le := PTree.set _b (Vptr bb ob) (PTree.set _a (Vptr ba oa)
    (create_undef_temps (fn_temps f_sha256_cmp_be)))).
  assert (HG : cmp_good le) by (split; reflexivity).
  assert (HEx : exists le'', Clight2.exec_stmt sha_ge empty_env le m cmp_body E0 le'' m
    (Out_return (Some (Vint (cmp_model [x0; x1; x2; x3; x4; x5; x6; x7]
      [y0; y1; y2; y3; y4; y5; y6; y7]), tint)))).
  { unfold cmp_body.
    Ltac cmp_step HX HY k :=
      eapply cmp_seq_step; try discriminate; try eassumption;
        [lia|exact (HX k ltac:(lia))|exact (HY k ltac:(lia))|
         let l := fresh "le" in let h := fresh "HG" in intros l h].
    cmp_step HX HY 0%nat. cmp_step HX HY 1%nat. cmp_step HX HY 2%nat. cmp_step HX HY 3%nat.
    cmp_step HX HY 4%nat. cmp_step HX HY 5%nat. cmp_step HX HY 6%nat. cmp_step HX HY 7%nat.
    eexists. cbn [cmp_model]. apply exec_Sreturn_some. apply eval_Econst_int. }
  destruct HEx as [le'' HEx].
  eapply eval_funcall_internal with (e := empty_env) (le1 := le) (le2 := le'') (m1 := m) (m2 := m)
    (out := Out_return (Some (Vint (cmp_model [x0; x1; x2; x3; x4; x5; x6; x7]
      [y0; y1; y2; y3; y4; y5; y6; y7]), tint))).
  - constructor.
    + constructor.
    + cbn. repeat constructor; cbn; intuition discriminate.
    + intros i j HI HJ Hij. cbn in HI. destruct HI as [HI|[HI|[]]]; subst i;
        cbn in HJ; repeat (destruct HJ as [HJ|HJ]; [subst j; discriminate|]); contradiction.
    + constructor.
    + reflexivity.
  - rewrite cmp_body_eq. exact HEx.
  - split; [discriminate|reflexivity].
  - reflexivity.
Qed.

End Chain.
