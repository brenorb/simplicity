(** Execution of the static Bitcoin helpers [lockDistance] / [lockDuration]
    from the generated Clight bodies, for an in-range input index:
      if (2 <= tx->version && tx->input[ix].sequence < 0x80000000 && BIT22TEST)
        return tx->input[ix].sequence & 0xffff;  else return 0;
    Both are pure reads of the transaction. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import C.jet_exec C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_field_eval C.jet_bitcoin_call.
Require Import C.jet_bitcoin_index_eval C.jet_bitcoin_is_final_local C.jet_parse_sequence_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque bitcoin_ge.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Definition tx_field_expr (field : ident) (ty : type) : expr :=
  Efield (Ederef (Etempvar _tx (tptr (Tstruct _bitcoinTransaction noattr)))
    (Tstruct _bitcoinTransaction noattr)) field ty.

Definition seq_elem_expr (t : ident) : expr :=
  Efield (Ederef (Ebinop Oadd (Etempvar t (tptr (Tstruct _sigInput noattr))) (Etempvar _ix tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr)) _sequence tulong.

Definition bit22_expr : expr :=
  Ebinop Oand (Etempvar _t'6 tulong)
    (Ebinop Oshl (Ecast (Econst_int (Int.repr 1) tint) tulong) (Econst_int (Int.repr 22) tint) tulong)
    tulong.

Definition dist_fn (afail : statement) (bitexpr : expr) : function := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_tx, (tptr (Tstruct _bitcoinTransaction noattr))) :: (_ix, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: (_t'10, tulong) ::
               (_t'9, tulong) :: (_t'8, (tptr (Tstruct _sigInput noattr))) ::
               (_t'7, tulong) :: (_t'6, tulong) ::
               (_t'5, (tptr (Tstruct _sigInput noattr))) :: (_t'4, tulong) ::
               (_t'3, (tptr (Tstruct _sigInput noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'10 (tx_field_expr _numInputs tulong))
    (Sifthenelse (Ebinop Olt (Etempvar _ix tulong) (Etempvar _t'10 tulong) tint) Sskip afail))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'7 (tx_field_expr _version tulong))
        (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 2) tint) (Etempvar _t'7 tulong) tint)
          (Ssequence
            (Sset _t'8 (tx_field_expr _input (tptr (Tstruct _sigInput noattr))))
            (Ssequence
              (Sset _t'9 (seq_elem_expr _t'8))
              (Sset _t'1
                (Ecast
                  (Ebinop Olt (Etempvar _t'9 tulong)
                    (Econst_int (Int.repr (-2147483648)) tuint) tint) tbool))))
          (Sset _t'1 (Econst_int (Int.repr 0) tint))))
      (Sifthenelse (Etempvar _t'1 tint)
        (Ssequence
          (Sset _t'5 (tx_field_expr _input (tptr (Tstruct _sigInput noattr))))
          (Ssequence
            (Sset _t'6 (seq_elem_expr _t'5))
            (Sset _t'2 (Ecast bitexpr tbool))))
        (Sset _t'2 (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Etempvar _t'2 tint)
      (Ssequence
        (Sset _t'3 (tx_field_expr _input (tptr (Tstruct _sigInput noattr))))
        (Ssequence
          (Sset _t'4 (seq_elem_expr _t'3))
          (Sreturn (Some (Ebinop Oand (Etempvar _t'4 tulong)
                           (Econst_int (Int.repr 65535) tint) tulong)))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition assert_fail_stmt (strA strB : ident) (lenA lenB line : Z) (fname : ident) : statement :=
  Scall None
    (Evar ___assert_fail (Tfunction
      (Tcons (tptr tschar) (Tcons (tptr tschar) (Tcons tuint (Tcons (tptr tschar) Tnil))))
      tvoid cc_default))
    ((Evar strA (tarray tschar lenA)) :: (Evar strB (tarray tschar lenB)) ::
     (Econst_int (Int.repr line) tint) :: (Evar fname (tarray tschar 13)) :: nil).

Definition lock_distance_bit : expr := Eunop Onotbool bit22_expr tint.
Definition lock_duration_bit : expr := Eunop Onotbool (Eunop Onotbool bit22_expr tint) tint.

Lemma f_lockDistance_shape :
  f_lockDistance = dist_fn (assert_fail_stmt ___stringlit_13 ___stringlit_12 19 36 45 ___func____7)
    lock_distance_bit.
Proof. reflexivity. Qed.
Lemma f_lockDuration_shape :
  f_lockDuration = dist_fn (assert_fail_stmt ___stringlit_13 ___stringlit_12 19 36 56 ___func____8)
    lock_duration_bit.
Proof. reflexivity. Qed.

Definition version_ok (ver : int64) : bool := negb (Int64.ltu ver (Int64.repr 2)).

Definition dist_result (ver seq : int64) (c : bool) : int64 :=
  if version_ok ver && parse_sequence_enabled seq && c
  then parse_sequence_payload seq else Int64.zero.

Lemma bitcoin_tx_numInputs : bitcoin_field_at _bitcoinTransaction _numInputs 448.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_tx_version : bitcoin_field_at _bitcoinTransaction _version 464.
Proof. vm_compute; reflexivity. Qed.

Section DistExec.
Variables (afail : statement) (bitexpr : expr).
Variables (m : mem) (bt : block) (tbase : Z) (bin : block) (inbase : Z).
Variables (ix nI ver seq : int64) (c : bool).
Hypothesis Ht : 0 <= tbase.
Hypothesis HtM : tbase + 488 <= Ptrofs.max_unsigned.
Hypothesis Hi : 0 <= inbase.
Hypothesis HiM : inbase + 160 * Int64.unsigned ix + 144 + 8 <= Ptrofs.max_unsigned.
Hypothesis HLn : Mem.load Mint64 m bt (tbase + 448) = Some (Vlong nI).
Hypothesis HLv : Mem.load Mint64 m bt (tbase + 464) = Some (Vlong ver).
Hypothesis HLi : Mem.load Mptr m bt (tbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)).
Hypothesis HLs : Mem.load Mint64 m bin (inbase + 160 * Int64.unsigned ix + 144) = Some (Vlong seq).
Hypothesis Hlt : Int64.ltu ix nI = true.
Hypothesis Hbit : forall le, le!_t'6 = Some (Vlong seq) ->
  eval_expr bitcoin_ge empty_env le m (Ecast bitexpr tbool) (Vint (bool_int c)).

Lemma eval_tx_field64 le field delta v :
  le!_tx = Some (Vptr bt (Ptrofs.repr tbase)) ->
  bitcoin_field_at _bitcoinTransaction field delta -> 0 <= delta <= 480 ->
  Mem.load Mint64 m bt (tbase + delta) = Some (Vlong v) ->
  eval_expr bitcoin_ge empty_env le m (tx_field_expr field tulong) (Vlong v).
Proof.
  intros HT HF HD HL. unfold tx_field_expr.
  eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := delta) (chunk := Mint64).
  - reflexivity.
  - exact HF.
  - reflexivity.
  - apply eval_bitcoin_deref_struct. exact HT.
  - rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact HL].
Qed.

Lemma eval_tx_input le :
  le!_tx = Some (Vptr bt (Ptrofs.repr tbase)) ->
  eval_expr bitcoin_ge empty_env le m (tx_field_expr _input (tptr (Tstruct _sigInput noattr)))
    (Vptr bin (Ptrofs.repr inbase)).
Proof.
  intros HT. unfold tx_field_expr.
  eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := 0) (chunk := Mptr).
  - reflexivity.
  - exact bitcoin_bitcoinTransaction_input.
  - reflexivity.
  - apply eval_bitcoin_deref_struct. exact HT.
  - rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact HLi].
Qed.

Lemma eval_seq_elem le t :
  le!t = Some (Vptr bin (Ptrofs.repr inbase)) -> le!_ix = Some (Vlong ix) ->
  eval_expr bitcoin_ge empty_env le m (seq_elem_expr t) (Vlong seq).
Proof.
  intros HT HI. unfold seq_elem_expr.
  exact (eval_bitcoin_elem_field_at empty_env le m t _ix _sigInput 160 _sequence 144 bin inbase ix seq
    bitcoin_sizeof_sigInput bitcoin_sigInput_sequence HT HI Hi ltac:(lia) ltac:(lia) HiM HLs).
Qed.

Ltac dist_entry :=
  eapply ClightBigstep.eval_funcall_internal with (e := empty_env) (m1 := m) (m2 := m);
  [ apply function_entry2_intro;
    [ apply list_norepet_nil
    | repeat constructor; simpl; intuition discriminate
    | intros x y HX HY Hxy; cbn in HX, HY;
      repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
        first [contradiction | vm_compute in Hxy; discriminate | congruence]
    | apply alloc_variables_nil
    | reflexivity ]
  | cbn [dist_fn fn_body] | | ].

Ltac tx_get := repeat rewrite PTree.gso by discriminate; first [apply PTree.gss | reflexivity].
Ltac seq1 := eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).

Ltac dist_guard :=
  seq1;
  [ apply exec_set; eapply eval_tx_field64; [reflexivity|exact bitcoin_tx_numInputs|lia|exact HLn]
  | eapply exec_Sifthenelse with (v1 := Vtrue) (b := true);
    [ eapply eval_Ebinop;
      [ apply eval_Etempvar; tx_get | apply eval_Etempvar; apply PTree.gss
      | change (Some (Val.of_bool (Int64.ltu ix nI)) = Some Vtrue); rewrite Hlt; reflexivity ]
    | reflexivity
    | apply exec_Sskip ] ].

Ltac set_version :=
  apply exec_set; eapply eval_tx_field64; [tx_get|exact bitcoin_tx_version|lia|exact HLv].

Ltac version_test bb :=
  eapply exec_Sifthenelse with (v1 := Val.of_bool bb) (b := bb);
  [ eapply eval_Ebinop;
    [ apply eval_Econst_int | apply eval_Etempvar; apply PTree.gss
    | change (Some (Val.of_bool (version_ok ver)) = Some (Val.of_bool bb));
      match goal with H : version_ok ver = _ |- _ => rewrite H end; reflexivity ]
  | reflexivity | ].

Ltac load_seq t :=
  seq1;
  [ apply exec_set; apply eval_tx_input; tx_get
  | seq1;
    [ apply exec_set; apply eval_seq_elem; [apply PTree.gss|tx_get] | ] ].

Lemma eval_enabled_cmp le :
  le!_t'9 = Some (Vlong seq) ->
  eval_expr bitcoin_ge empty_env le m
    (Ecast (Ebinop Olt (Etempvar _t'9 tulong) (Econst_int (Int.repr (-2147483648)) tuint) tint) tbool)
    (Vint (bool_int (parse_sequence_enabled seq))).
Proof.
  intro HT.
  eapply eval_Ecast with (v1 := Val.of_bool (parse_sequence_enabled seq)).
  - eapply eval_Ebinop; [apply eval_Etempvar; exact HT|apply eval_Econst_int|reflexivity].
  - destruct (parse_sequence_enabled seq); reflexivity.
Qed.

Lemma eval_dist_fn :
  Clight2.eval_funcall bitcoin_ge m (Internal (dist_fn afail bitexpr))
    [Vptr bt (Ptrofs.repr tbase); Vlong ix] E0 m (Vlong (dist_result ver seq c)).
Proof.
  unfold dist_result.
  destruct (version_ok ver) eqn:Hver; [destruct (parse_sequence_enabled seq) eqn:Hen; [destruct c|]|].
  - (* all tests pass *)
    dist_entry.
    { seq1; [dist_guard|].
      seq1.
      - seq1.
        + seq1; [set_version|].
          version_test true.
          load_seq _t'8.
          apply exec_set. apply eval_enabled_cmp. apply PTree.gss.
        + eapply exec_Sifthenelse with (b := true);
            [apply eval_Etempvar; apply PTree.gss|rewrite Hen; reflexivity|].
          load_seq _t'5.
          apply exec_set. apply (Hbit _ (PTree.gss _ _ _)).
      - eapply exec_Sifthenelse with (b := true);
          [apply eval_Etempvar; apply PTree.gss|reflexivity|].
        load_seq _t'3.
        apply ClightBigstep.exec_Sreturn_some.
        eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|apply eval_Econst_int|reflexivity]. }
    { cbn; split; [discriminate|reflexivity]. }
    { reflexivity. }
  - (* bit-22 test fails *)
    dist_entry.
    { seq1; [dist_guard|].
      seq1.
      - seq1.
        + seq1; [set_version|].
          version_test true.
          load_seq _t'8.
          apply exec_set. apply eval_enabled_cmp. apply PTree.gss.
        + eapply exec_Sifthenelse with (b := true);
            [apply eval_Etempvar; apply PTree.gss|rewrite Hen; reflexivity|].
          load_seq _t'5.
          apply exec_set. apply (Hbit _ (PTree.gss _ _ _)).
      - eapply exec_Sifthenelse with (b := false);
          [apply eval_Etempvar; apply PTree.gss|reflexivity|].
        apply ClightBigstep.exec_Sreturn_some. apply eval_Econst_int. }
    { cbn; split; [discriminate|reflexivity]. }
    { reflexivity. }
  - (* disabled sequence *)
    dist_entry.
    { seq1; [dist_guard|].
      seq1.
      - seq1.
        + seq1; [set_version|].
          version_test true.
          load_seq _t'8.
          apply exec_set. apply eval_enabled_cmp. apply PTree.gss.
        + eapply exec_Sifthenelse with (b := false);
            [apply eval_Etempvar; apply PTree.gss|rewrite Hen; reflexivity|].
          apply exec_set. apply eval_Econst_int.
      - eapply exec_Sifthenelse with (b := false);
          [apply eval_Etempvar; apply PTree.gss|reflexivity|].
        apply ClightBigstep.exec_Sreturn_some. apply eval_Econst_int. }
    { cbn; split; [discriminate|reflexivity]. }
    { reflexivity. }
  - (* version below 2 *)
    dist_entry.
    { seq1; [dist_guard|].
      seq1.
      - seq1.
        + seq1; [set_version|].
          version_test false.
          apply exec_set. apply eval_Econst_int.
        + eapply exec_Sifthenelse with (b := false);
            [apply eval_Etempvar; apply PTree.gss|reflexivity|].
          apply exec_set. apply eval_Econst_int.
      - eapply exec_Sifthenelse with (b := false);
          [apply eval_Etempvar; apply PTree.gss|reflexivity|].
        apply ClightBigstep.exec_Sreturn_some. apply eval_Econst_int. }
    { cbn; split; [discriminate|reflexivity]. }
    { reflexivity. }
Qed.
End DistExec.
