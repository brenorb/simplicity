(** Actual original uint128_rshift(52): no AST replacement or assumed call. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Events Values.
Require Import C.jet_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_u128_shift64_expr.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition shift52_low lo hi := Int64.or
  (Int64.shl (Int64.mul Int64.one hi) (Int64.repr 12))
  (Int64.shru lo (Int64.repr 52)).
Definition shift52_high hi := Int64.shru hi (Int64.repr 52).
Definition shift52_temps b := PTree.set jets_secp._n (Vint (Int.repr 52))
  (PTree.set jets_secp._r (Vptr b Ptrofs.zero)
    (create_undef_temps (fn_temps f_secp256k1_u128_rshift))).
Definition shift52_final le lo hi :=
  PTree.set jets_secp._t'1 (Vlong hi)
    (PTree.set jets_secp._t'3 (Vlong lo) (PTree.set jets_secp._t'2 (Vlong hi) le)).
Definition shift52_lhs := Ebinop Oshl
  (Ebinop Omul (Econst_int (Int.repr 1) tuint) (Etempvar jets_secp._t'2 tulong) tulong)
  (Ebinop Osub (Econst_int (Int.repr 64) tint) (Etempvar jets_secp._n tuint) tuint) tulong.
Definition shift52_rhs := Ebinop Oshr (Etempvar jets_secp._t'3 tulong)
  (Etempvar jets_secp._n tuint) tulong.

Lemma shift52_entry m b : function_entry2 secp_ge f_secp256k1_u128_rshift
  [Vptr b Ptrofs.zero; Vint (Int.repr 52)] m empty_env (shift52_temps b) m.
Proof.
  constructor.
  - cbn; constructor.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy; cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in Hxy; discriminate|congruence].
  - constructor.
  - reflexivity.
Qed.

Definition shift52_branch := Ssequence
  (Ssequence (Sset jets_secp._t'2 (u128_field jets_secp._hi))
    (Ssequence (Sset jets_secp._t'3 (u128_field jets_secp._lo))
      (Sassign (u128_field jets_secp._lo) (Ebinop Oor shift52_lhs shift52_rhs tulong))))
  (Ssequence (Sset jets_secp._t'1 (u128_field jets_secp._hi))
    (Sassign (u128_field jets_secp._hi)
      (Ebinop Oshr (Etempvar jets_secp._t'1 tulong) (Etempvar jets_secp._n tuint) tulong))).
Definition shift52_other := match fn_body f_secp256k1_u128_rshift with
  | Ssequence _ (Sifthenelse _ yes _) => yes | _ => Sskip end.
Lemma shift52_actual_body : fn_body f_secp256k1_u128_rshift =
  Ssequence (Sloop Sskip Sbreak)
    (Sifthenelse u128_shift_test shift52_other
      (Sifthenelse (Ebinop Ogt (Etempvar jets_secp._n tuint) (Econst_int Int.zero tint) tint)
        shift52_branch Sskip)).
Proof. reflexivity. Qed.

Lemma eval_shift52_lhs m le hi :
  le!jets_secp._n = Some (Vint (Int.repr 52)) ->
  le!jets_secp._t'2 = Some (Vlong hi) ->
  eval_expr secp_ge empty_env le m shift52_lhs
    (Vlong (Int64.shl (Int64.mul Int64.one hi) (Int64.repr 12))).
Proof.
  intros HN HH; unfold shift52_lhs.
  eapply eval_Ebinop with (v1 := Vlong (Int64.mul Int64.one hi)) (v2 := Vint (Int.repr 12)).
  - eapply eval_Ebinop with (v1 := Vint (Int.repr 1)) (v2 := Vlong hi).
    + constructor.
    + apply eval_Etempvar; exact HH.
    + reflexivity.
  - eapply eval_Ebinop with (v1 := Vint (Int.repr 64)) (v2 := Vint (Int.repr 52)).
    + constructor.
    + apply eval_Etempvar; exact HN.
    + reflexivity.
  - reflexivity.
Qed.

Lemma eval_shift52_right m le id value :
  le!jets_secp._n = Some (Vint (Int.repr 52)) -> le!id = Some (Vlong value) ->
  eval_expr secp_ge empty_env le m
    (Ebinop Oshr (Etempvar id tulong) (Etempvar jets_secp._n tuint) tulong)
    (Vlong (Int64.shru value (Int64.repr 52))).
Proof.
  intros HN HV. eapply eval_Ebinop with (v1 := Vlong value) (v2 := Vint (Int.repr 52)).
  - apply eval_Etempvar; exact HV.
  - apply eval_Etempvar; exact HN.
  - reflexivity.
Qed.

Lemma eval_shift52_low m le lo hi :
  le!jets_secp._n = Some (Vint (Int.repr 52)) ->
  le!jets_secp._t'2 = Some (Vlong hi) -> le!jets_secp._t'3 = Some (Vlong lo) ->
  eval_expr secp_ge empty_env le m (Ebinop Oor shift52_lhs shift52_rhs tulong)
    (Vlong (shift52_low lo hi)).
Proof.
  intros HN HH HL. eapply eval_Ebinop.
  - exact (eval_shift52_lhs m le hi HN HH).
  - exact (eval_shift52_right m le jets_secp._t'3 lo HN HL).
  - reflexivity.
Qed.

Lemma eval_shift52_lo_field m le b value :
  le!jets_secp._r = Some (Vptr b Ptrofs.zero) ->
  Mem.load Mint64 m b 0 = Some (Vlong value) ->
  eval_expr secp_ge empty_env le m (u128_field jets_secp._lo) (Vlong value).
Proof.
  intros HR HL. eapply eval_Elvalue.
  - apply u128_field_lvalue; [exact HR|left; split; reflexivity].
  - apply deref_loc_value with (chunk := Mint64); [reflexivity|exact HL].
Qed.

Theorem exec_shift52_body m m1 mf le b lo hi :
  le!jets_secp._r = Some (Vptr b Ptrofs.zero) ->
  le!jets_secp._n = Some (Vint (Int.repr 52)) ->
  Mem.load Mint64 m b 0 = Some (Vlong lo) ->
  Mem.load Mint64 m b 8 = Some (Vlong hi) ->
  Mem.store Mint64 m b 0 (Vlong (shift52_low lo hi)) = Some m1 ->
  Mem.store Mint64 m1 b 8 (Vlong (shift52_high hi)) = Some mf ->
  Clight2.exec_stmt secp_ge empty_env le m (fn_body f_secp256k1_u128_rshift)
    E0 (shift52_final le lo hi) mf Out_normal.
Proof.
  intros HR HN HL HH HSL HSH.
  set (le2 := PTree.set jets_secp._t'2 (Vlong hi) le).
  set (le3 := PTree.set jets_secp._t'3 (Vlong lo) le2).
  set (lef := PTree.set jets_secp._t'1 (Vlong hi) le3).
  assert (HR2 : le2!jets_secp._r = Some (Vptr b Ptrofs.zero)).
  { unfold le2; rewrite PTree.gso by discriminate; exact HR. }
  assert (HR3 : le3!jets_secp._r = Some (Vptr b Ptrofs.zero)).
  { unfold le3; rewrite PTree.gso by discriminate; exact HR2. }
  assert (HRF : lef!jets_secp._r = Some (Vptr b Ptrofs.zero)).
  { unfold lef; rewrite PTree.gso by discriminate; exact HR3. }
  assert (HN3 : le3!jets_secp._n = Some (Vint (Int.repr 52))).
  { unfold le3, le2; repeat rewrite PTree.gso by discriminate; exact HN. }
  assert (HNF : lef!jets_secp._n = Some (Vint (Int.repr 52))).
  { unfold lef; rewrite PTree.gso by discriminate; exact HN3. }
  assert (HH1 : Mem.load Mint64 m1 b 8 = Some (Vlong hi)).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ HSL); [exact HH|right; right; reflexivity]. }
  change (Clight2.exec_stmt secp_ge empty_env le m (fn_body f_secp256k1_u128_rshift)
    E0 lef mf Out_normal).
  rewrite shift52_actual_body.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le).
  - change E0 with (E0 ** E0).
    eapply exec_Sloop_stop2 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le)
      (out1 := Out_normal) (out2 := Out_break); constructor.
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
    + unfold u128_shift_test. eapply eval_Ebinop with (v1 := Vint (Int.repr 52)) (v2 := Vint (Int.repr 64)).
      * apply eval_Etempvar; exact HN.
      * constructor.
      * reflexivity.
    + reflexivity.
    + eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
      * eapply eval_Ebinop with (v1 := Vint (Int.repr 52)) (v2 := Vint Int.zero).
        -- apply eval_Etempvar; exact HN.
        -- constructor.
        -- reflexivity.
      * reflexivity.
      * unfold shift52_branch.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le3).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le2).
           ++ apply exec_Sset. exact (eval_u128_hi m le b hi HR HH).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le3).
              ** apply exec_Sset. exact (eval_shift52_lo_field m le2 b lo HR2 HL).
              ** eapply exec_Sassign with (loc := b)
                   (ofs := Ptrofs.add Ptrofs.zero (Ptrofs.repr 0)) (bf := Full)
                   (v2 := Vlong (shift52_low lo hi)) (v := Vlong (shift52_low lo hi)).
                 --- apply u128_field_lvalue; [exact HR3|left; split; reflexivity].
                 --- apply eval_shift52_low; [exact HN3|unfold le3, le2; rewrite PTree.gso by discriminate; apply PTree.gss|unfold le3; apply PTree.gss].
                 --- reflexivity.
                 --- apply assign_loc_value with (chunk := Mint64); [reflexivity|exact HSL].
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := lef).
           ++ apply exec_Sset. exact (eval_u128_hi m1 le3 b hi HR3 HH1).
           ++ eapply exec_Sassign with (loc := b)
                (ofs := Ptrofs.add Ptrofs.zero (Ptrofs.repr 8)) (bf := Full)
                (v2 := Vlong (shift52_high hi)) (v := Vlong (shift52_high hi)).
              ** apply u128_field_lvalue; [exact HRF|right; split; reflexivity].
              ** apply eval_shift52_right; [exact HNF|unfold lef; apply PTree.gss].
              ** reflexivity.
              ** apply assign_loc_value with (chunk := Mint64); [reflexivity|exact HSH].
Qed.

Lemma shift52_storage m b lo hi :
  Mem.range_perm m b 0 16 Cur Writable ->
  exists m1 mf,
    Mem.store Mint64 m b 0 (Vlong (shift52_low lo hi)) = Some m1 /\
    Mem.store Mint64 m1 b 8 (Vlong (shift52_high hi)) = Some mf /\
    Mem.load Mint64 mf b 0 = Some (Vlong (shift52_low lo hi)) /\
    Mem.load Mint64 mf b 8 = Some (Vlong (shift52_high hi)) /\
    (forall bb ofs k p, Mem.perm m bb ofs k p -> Mem.perm mf bb ofs k p) /\
    lframe (fun bb ofs => ~ (bb = b /\ 0 <= ofs < 16)) m mf.
Proof.
  intro HP.
  assert (HA0 : Mem.valid_access m Mint64 b 0 Writable).
  { split; [intros ofs HOfs; apply HP; cbn in HOfs; lia|exists 0; reflexivity]. }
  destruct (Mem.valid_access_store m Mint64 b 0 (Vlong (shift52_low lo hi)) HA0) as [m1 HS0].
  assert (HA8 : Mem.valid_access m1 Mint64 b 8 Writable).
  { split.
    - intros ofs HOfs. eapply Mem.perm_store_1; [exact HS0|apply HP; cbn in HOfs; lia].
    - exists 1; reflexivity. }
  destruct (Mem.valid_access_store m1 Mint64 b 8 (Vlong (shift52_high hi)) HA8) as [mf HS8].
  exists m1, mf; split; [exact HS0|]; split; [exact HS8|]; split.
  - rewrite (Mem.load_store_other _ _ _ _ _ _ HS8); [exact (Mem.load_store_same _ _ _ _ _ _ HS0)|right; left; reflexivity].
  - split; [exact (Mem.load_store_same _ _ _ _ _ _ HS8)|]; split.
    + intros. eapply Mem.perm_store_1; [exact HS8|]. eapply Mem.perm_store_1; [exact HS0|assumption].
    + eapply lframe_trans.
      * apply lframe_unchanged. eapply Mem.store_unchanged_on; [exact HS0|].
        intros ofs HOfs HOutside; apply HOutside; split; [reflexivity|cbn in HOfs; lia].
      * apply lframe_unchanged. eapply Mem.store_unchanged_on; [exact HS8|].
        intros ofs HOfs HOutside; apply HOutside; split; [reflexivity|cbn in HOfs; lia].
Qed.

Theorem eval_u128_shift52 m b lo hi :
  Mem.range_perm m b 0 16 Cur Writable ->
  Mem.load Mint64 m b 0 = Some (Vlong lo) ->
  Mem.load Mint64 m b 8 = Some (Vlong hi) ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_u128_rshift)
      [Vptr b Ptrofs.zero; Vint (Int.repr 52)] E0 mf Vundef /\
    Mem.load Mint64 mf b 0 = Some (Vlong (shift52_low lo hi)) /\
    Mem.load Mint64 mf b 8 = Some (Vlong (shift52_high hi)) /\
    (forall bb ofs k p, Mem.perm m bb ofs k p -> Mem.perm mf bb ofs k p) /\
    lframe (fun bb ofs => ~ (bb = b /\ 0 <= ofs < 16)) m mf.
Proof.
  intros HP HL HH.
  destruct (shift52_storage m b lo hi HP) as (m1 & mf & HS0 & HS8 & HLow & HHigh & HPerm & HFrame).
  exists mf; split.
  - eapply eval_funcall_internal with (e := empty_env) (le1 := shift52_temps b)
      (le2 := shift52_final (shift52_temps b) lo hi)
      (m1 := m) (m2 := mf) (out := Out_normal).
    + apply shift52_entry.
    + apply exec_shift52_body with (m1 := m1) (b := b); try assumption; reflexivity.
    + reflexivity.
    + reflexivity.
  - split; [exact HLow|]; split; [exact HHigh|]; split; [exact HPerm|exact HFrame].
Qed.
