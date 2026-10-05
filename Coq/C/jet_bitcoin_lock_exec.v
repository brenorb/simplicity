(** Execution of the static Bitcoin helpers
      [lockHeight(tx) = !tx->isFinal && tx->lockTime < 500000000U ? tx->lockTime : 0]
      [lockTime(tx)   = !tx->isFinal && 500000000U <= tx->lockTime ? tx->lockTime : 0]
    from the generated Clight bodies.  Both are pure reads of the transaction. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import C.jet_exec C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_field_eval C.jet_bitcoin_call.
Require Import C.jet_bitcoin_is_final_local.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque bitcoin_ge.
Local Transparent Archi.ptr64.
Set Default Timeout 60.

Definition lock_fn (cmp : expr) : function := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_tx, (tptr (Tstruct _bitcoinTransaction noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tulong) :: (_t'1, tint) :: (_t'5, tulong) ::
               (_t'4, tbool) :: (_t'3, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _tx (tptr (Tstruct _bitcoinTransaction noattr)))
            (Tstruct _bitcoinTransaction noattr)) _isFinal tbool))
      (Sifthenelse (Eunop Onotbool (Etempvar _t'4 tbool) tint)
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef
                (Etempvar _tx (tptr (Tstruct _bitcoinTransaction noattr)))
                (Tstruct _bitcoinTransaction noattr)) _lockTime tulong))
          (Sset _t'1 (Ecast cmp tbool)))
        (Sset _t'1 (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Etempvar _t'1 tint)
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef
              (Etempvar _tx (tptr (Tstruct _bitcoinTransaction noattr)))
              (Tstruct _bitcoinTransaction noattr)) _lockTime tulong))
        (Sset _t'2 (Ecast (Etempvar _t'3 tulong) tulong)))
      (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tulong))))
  (Sreturn (Some (Etempvar _t'2 tulong))))
|}.

Definition lock_height_cmp : expr :=
  Ebinop Olt (Etempvar _t'5 tulong) (Econst_int (Int.repr 500000000) tuint) tint.
Definition lock_time_cmp : expr :=
  Ebinop Ole (Econst_int (Int.repr 500000000) tuint) (Etempvar _t'5 tulong) tint.

Lemma f_lockHeight_shape : f_lockHeight = lock_fn lock_height_cmp.
Proof. reflexivity. Qed.
Lemma f_lockTime_shape : f_lockTime = lock_fn lock_time_cmp.
Proof. reflexivity. Qed.

Lemma bitcoin_tx_lockTime : bitcoin_field_at _bitcoinTransaction _lockTime 472.
Proof. vm_compute; reflexivity. Qed.

Definition lock_result (b c : bool) (lt : int64) : int64 :=
  if negb b && c then lt else Int64.zero.

Ltac tx_field d ch HF HL :=
  eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := d) (chunk := ch);
    [reflexivity|exact HF|reflexivity|apply eval_bitcoin_deref_struct; reflexivity|
     rewrite bitcoin_ptr_add_repr by lia; apply bitcoin_loadv_repr; [lia|exact HL]].

Ltac lock_entry m :=
  eapply ClightBigstep.eval_funcall_internal with (e := empty_env) (m1 := m) (m2 := m);
  [ apply function_entry2_intro;
    [ apply list_norepet_nil
    | repeat constructor; simpl; intuition discriminate
    | intros x y HX HY Hxy; cbn in HX, HY;
      repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
        first [contradiction | vm_compute in Hxy; discriminate | congruence]
    | apply alloc_variables_nil
    | reflexivity ]
  | cbn [lock_fn fn_body] | | ].

Ltac lock_exit := [> cbn; split; [discriminate|reflexivity] | reflexivity ].

Ltac lock_return :=
  apply ClightBigstep.exec_Sreturn_some; apply eval_Etempvar; apply PTree.gss.

Lemma eval_lock_fn cmp m bt tbase (b c : bool) (lt : int64) :
  0 <= tbase -> tbase + 488 <= Ptrofs.max_unsigned ->
  Mem.load Mint8unsigned m bt (tbase + 480) = Some (Vint (bool_int b)) ->
  Mem.load Mint64 m bt (tbase + 472) = Some (Vlong lt) ->
  (forall le, le!_t'5 = Some (Vlong lt) ->
    eval_expr bitcoin_ge empty_env le m (Ecast cmp tbool) (Vint (bool_int c))) ->
  Clight2.eval_funcall bitcoin_ge m (Internal (lock_fn cmp))
    [Vptr bt (Ptrofs.repr tbase)] E0 m (Vlong (lock_result b c lt)).
Proof.
  intros Ht HtM HLb HLt Hcmp.
  destruct b; [|destruct c].
  - (* final: both conditions false *)
    lock_entry m.
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m); [|lock_return].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
      + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
        * apply exec_set. tx_field 480 Mint8unsigned bitcoin_tx_isFinal HLb.
        * eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
          -- eapply eval_Eunop; [apply eval_Etempvar; apply PTree.gss|reflexivity].
          -- reflexivity.
          -- apply exec_set. apply eval_Econst_int.
      + eapply exec_Sifthenelse with (b := false).
        * apply eval_Etempvar. apply PTree.gss.
        * reflexivity.
        * apply exec_set. eapply eval_Ecast; [apply eval_Econst_int|reflexivity]. }
    all: lock_exit.
  - lock_entry m.
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m); [|lock_return].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
      + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
        * apply exec_set. tx_field 480 Mint8unsigned bitcoin_tx_isFinal HLb.
        * eapply exec_Sifthenelse with (v1 := Vtrue) (b := true).
          -- eapply eval_Eunop; [apply eval_Etempvar; apply PTree.gss|reflexivity].
          -- reflexivity.
          -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
             ++ apply exec_set. tx_field 472 Mint64 bitcoin_tx_lockTime HLt.
             ++ apply exec_set. apply Hcmp. apply PTree.gss.
      + eapply exec_Sifthenelse with (b := true).
        * apply eval_Etempvar. apply PTree.gss.
        * reflexivity.
        * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
          -- apply exec_set. tx_field 472 Mint64 bitcoin_tx_lockTime HLt.
          -- apply exec_set. eapply eval_Ecast; [apply eval_Etempvar; apply PTree.gss|reflexivity]. }
    all: lock_exit.
  - lock_entry m.
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m); [|lock_return].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
      + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
        * apply exec_set. tx_field 480 Mint8unsigned bitcoin_tx_isFinal HLb.
        * eapply exec_Sifthenelse with (v1 := Vtrue) (b := true).
          -- eapply eval_Eunop; [apply eval_Etempvar; apply PTree.gss|reflexivity].
          -- reflexivity.
          -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
             ++ apply exec_set. tx_field 472 Mint64 bitcoin_tx_lockTime HLt.
             ++ apply exec_set. apply Hcmp. apply PTree.gss.
      + eapply exec_Sifthenelse with (b := false).
        * apply eval_Etempvar. apply PTree.gss.
        * reflexivity.
        * apply exec_set. eapply eval_Ecast; [apply eval_Econst_int|reflexivity]. }
    all: lock_exit.
Qed.
