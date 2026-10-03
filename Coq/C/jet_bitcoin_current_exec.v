(** Execution skeleton of the "current input" Bitcoin getters:
      if (env->tx->COUNT <= env->ix) return false;
      WRITER(dst, env->tx->ARRAY[env->ix].FIELD);  return true;
    All environment loads precede the single write. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_frame_layout C.jets_bitcoin C.jet_bitcoin_linkage.
Require C.jets.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_indexed_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge.
Set Default Timeout 60.

Definition bitcoin_env_tx_expr : expr :=
  Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
    _tx (tptr (Tstruct _bitcoinTransaction noattr)).
Definition bitcoin_env_ix_expr : expr :=
  Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr)) _ix tulong.

Definition bitcoin_current_rest (t1 t2 t3 t4 t5 t6 t7 arrfield countfield sid : ident) (ve : expr)
    (wid : ident) : statement :=
  Ssequence
    (Ssequence (Sset t5 bitcoin_env_tx_expr)
      (Ssequence
        (Sset t6 (Efield (Ederef (Etempvar t5 (tptr (Tstruct _bitcoinTransaction noattr)))
          (Tstruct _bitcoinTransaction noattr)) countfield tulong))
        (Ssequence (Sset t7 bitcoin_env_ix_expr)
          (Sifthenelse (Ebinop Ole (Etempvar t6 tulong) (Etempvar t7 tulong) tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip))))
    (Ssequence
      (Ssequence (Sset t1 bitcoin_env_tx_expr)
        (Ssequence
          (Sset t2 (Efield (Ederef (Etempvar t1 (tptr (Tstruct _bitcoinTransaction noattr)))
            (Tstruct _bitcoinTransaction noattr)) arrfield (tptr (Tstruct sid noattr))))
          (Ssequence (Sset t3 bitcoin_env_ix_expr)
            (Ssequence (Sset t4 ve)
              (Scall None
                (Evar wid (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
                [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar t4 tulong])))))
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))).

Lemma eval_bitcoin_env_ix e le m be ebase v :
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> 0 <= ebase -> ebase + 56 <= Ptrofs.max_unsigned ->
  Mem.load Mint64 m be (ebase + 48) = Some (Vlong v) ->
  eval_expr bitcoin_ge e le m bitcoin_env_ix_expr (Vlong v).
Proof.
  intros HE H0 HM HL. unfold bitcoin_env_ix_expr.
  eapply eval_bitcoin_field_value with (sid := _txEnv) (delta := 48) (chunk := Mint64).
  - reflexivity.
  - exact bitcoin_txEnv_ix.
  - reflexivity.
  - apply eval_bitcoin_deref_struct; exact HE.
  - rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact HL].
Qed.

Lemma eval_bitcoin_env_tx_expr e le m be ebase bt txbase :
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> 0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
  eval_expr bitcoin_ge e le m bitcoin_env_tx_expr (Vptr bt (Ptrofs.repr txbase)).
Proof.
  intros HE H0 HM HL. unfold bitcoin_env_tx_expr.
  eapply eval_bitcoin_field_value with (sid := _txEnv) (delta := 0) (chunk := Mptr).
  - reflexivity.
  - exact bitcoin_txEnv_tx.
  - reflexivity.
  - apply eval_bitcoin_deref_struct; exact HE.
  - rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact HL].
Qed.

Ltac gsoc := rewrite PTree.gso by (first [assumption | apply not_eq_sym; assumption | discriminate]).

Lemma exec_bitcoin_current_rest e le0 t1 t2 t3 t4 t5 t6 t7 arrfield countfield sid ve wid wf
    cdelta adelta mc me be ebase bt txbase bin inbase bd dbase nI ixv v :
  t5 <> _env -> t6 <> _env -> t7 <> _env -> t1 <> _env -> t2 <> _env -> t3 <> _env ->
  t1 <> _dst -> t2 <> _dst -> t3 <> _dst -> t4 <> _dst -> t5 <> _dst -> t6 <> _dst -> t7 <> _dst ->
  t7 <> t6 -> t3 <> t2 ->
  In (wid, wf) bitcoin_core_helpers ->
  type_of_fundef (Internal wf) =
    Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default ->
  e!wid = None ->
  le0!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le0!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ebase -> ebase + 56 <= Ptrofs.max_unsigned ->
  0 <= txbase -> 0 <= cdelta -> txbase + cdelta + 8 <= Ptrofs.max_unsigned ->
  0 <= adelta -> txbase + adelta + 8 <= Ptrofs.max_unsigned ->
  bitcoin_field_at _bitcoinTransaction countfield cdelta ->
  bitcoin_field_at _bitcoinTransaction arrfield adelta ->
  Mem.load Mptr mc be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mint64 mc bt (txbase + cdelta) = Some (Vlong nI) ->
  Mem.load Mint64 mc be (ebase + 48) = Some (Vlong ixv) ->
  Mem.load Mptr mc bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) ->
  Int64.ltu ixv nI = true ->
  (forall le', le'!t2 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!t3 = Some (Vlong ixv) ->
    eval_expr bitcoin_ge e le' mc ve (Vlong v)) ->
  Clight2.eval_funcall bitcoin_ge mc (Internal wf) [Vptr bd (Ptrofs.repr dbase); Vlong v] E0 me Vundef ->
  exists le1, Clight2.exec_stmt bitcoin_ge e le0 mc
    (bitcoin_current_rest t1 t2 t3 t4 t5 t6 t7 arrfield countfield sid ve wid) E0 le1 me bitcoin_returned_one.
Proof.
  intros H5 H6 H7 H1 H2 H3 H1d H2d H3d H4d H5d H6d H7d H76 H32 Hin Hty He HEnv HDst He0 He1 Ht0 Hc0 HcM Ha0 HaM
    HFc HFa Hl_tx Hl_cnt Hl_ix Hl_arr Hlt Hval Hcall.
  set (la5 := PTree.set t5 (Vptr bt (Ptrofs.repr txbase)) le0).
  set (la6 := PTree.set t6 (Vlong nI) la5).
  set (la7 := PTree.set t7 (Vlong ixv) la6).
  set (lb1 := PTree.set t1 (Vptr bt (Ptrofs.repr txbase)) la7).
  set (lb2 := PTree.set t2 (Vptr bin (Ptrofs.repr inbase)) lb1).
  set (lb3 := PTree.set t3 (Vlong ixv) lb2).
  set (lb4 := PTree.set t4 (Vlong v) lb3).
  assert (HE5 : la5!_env = Some (Vptr be (Ptrofs.repr ebase))) by (unfold la5; gsoc; exact HEnv).
  assert (HE6 : la6!_env = Some (Vptr be (Ptrofs.repr ebase))) by (unfold la6; gsoc; exact HE5).
  assert (HE7 : la7!_env = Some (Vptr be (Ptrofs.repr ebase))) by (unfold la7; gsoc; exact HE6).
  assert (HEb1 : lb1!_env = Some (Vptr be (Ptrofs.repr ebase))) by (unfold lb1; gsoc; exact HE7).
  assert (HEb2 : lb2!_env = Some (Vptr be (Ptrofs.repr ebase))) by (unfold lb2; gsoc; exact HEb1).
  eexists. unfold bitcoin_current_rest.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la7).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la5).
    + apply exec_set. eapply eval_bitcoin_env_tx_expr; [exact HEnv|exact He0|lia|exact Hl_tx].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la6).
      * apply exec_set.
        eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := cdelta) (chunk := Mint64).
        -- reflexivity.
        -- exact HFc.
        -- reflexivity.
        -- apply eval_bitcoin_deref_struct. unfold la5. apply PTree.gss.
        -- rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact Hl_cnt].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la7).
        -- apply exec_set. eapply eval_bitcoin_env_ix; [exact HE6|exact He0|exact He1|exact Hl_ix].
        -- eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
           ++ eapply eval_Ebinop with (v1 := Vlong nI) (v2 := Vlong ixv).
              ** apply eval_Etempvar. unfold la7. gsoc. apply PTree.gss.
              ** apply eval_Etempvar. unfold la7. apply PTree.gss.
              ** change (Some (Val.of_bool (negb (Int64.ltu ixv nI))) = Some (Vint Int.zero)).
                 rewrite Hlt. reflexivity.
           ++ reflexivity.
           ++ apply exec_Sskip.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := lb4); [|apply exec_Sreturn_some, eval_Econst_int].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := lb1).
    + apply exec_set. eapply eval_bitcoin_env_tx_expr; [exact HE7|exact He0|lia|exact Hl_tx].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := lb2).
      * apply exec_set.
        eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := adelta) (chunk := Mptr).
        -- reflexivity.
        -- exact HFa.
        -- reflexivity.
        -- apply eval_bitcoin_deref_struct. unfold lb1. apply PTree.gss.
        -- rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact Hl_arr].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := lb3).
        -- apply exec_set. eapply eval_bitcoin_env_ix; [exact HEb2|exact He0|exact He1|exact Hl_ix].
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := lb4).
           ++ apply exec_set. apply Hval.
              ** unfold lb3. gsoc. apply PTree.gss.
              ** unfold lb3. apply PTree.gss.
           ++ eapply exec_bitcoin_helper_call with (id := wid) (f := wf)
                (vargs := [Vptr bd (Ptrofs.repr dbase); Vlong v]) (vres := Vundef).
              ** exact Hin.
              ** exact He.
              ** eapply eval_Econs.
                 --- apply eval_Etempvar. unfold lb4, lb3, lb2, lb1, la7, la6, la5. gsoc. gsoc. gsoc. gsoc. gsoc.
                     gsoc. gsoc. exact HDst.
                 --- reflexivity.
                 --- eapply eval_Econs; [apply eval_Etempvar; unfold lb4; apply PTree.gss|reflexivity|apply eval_Enil].
              ** exact Hty.
              ** exact Hcall.
Qed.
