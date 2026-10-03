(** The success branch of an indexed Bitcoin getter:
      t3 = env->tx; t4 = t3->ARRAY; t5 = VALUE; WRITER(dst, t5);
    with the value expression and the writer chosen by the consumer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_frame_layout C.jets_bitcoin C.jet_bitcoin_linkage.
Require C.jets.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_transport C.jet_bitcoin_call.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge.
Set Default Timeout 60.

Definition bitcoin_indexed_then (t3 t4 t5 arrfield sid : ident) (ve : expr) (wid : ident) : statement :=
  Ssequence
    (Sset t3 (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
      _tx (tptr (Tstruct _bitcoinTransaction noattr))))
    (Ssequence
      (Sset t4 (Efield (Ederef (Etempvar t3 (tptr (Tstruct _bitcoinTransaction noattr)))
        (Tstruct _bitcoinTransaction noattr)) arrfield (tptr (Tstruct sid noattr))))
      (Ssequence
        (Sset t5 ve)
        (Scall None
          (Evar wid (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
          [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar t5 tulong]))).

Ltac gso2 := rewrite PTree.gso by (first [assumption | apply not_eq_sym; assumption | discriminate]).

Lemma exec_bitcoin_indexed_then e le t3 t4 t5 arrfield adelta sid ve wid wf
    mb me be ebase bt txbase bin inbase bd dbase r v :
  t3 <> _i -> t3 <> _dst -> t4 <> _i -> t4 <> _dst -> t5 <> _dst ->
  In (wid, wf) bitcoin_core_helpers ->
  type_of_fundef (Internal wf) =
    Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default ->
  e!wid = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_i = Some (Vlong r) ->
  0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  0 <= txbase -> 0 <= adelta -> txbase + adelta + 8 <= Ptrofs.max_unsigned ->
  bitcoin_field_at _bitcoinTransaction arrfield adelta ->
  Mem.load Mptr mb be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mptr mb bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) ->
  (forall le', le'!t4 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!_i = Some (Vlong r) ->
    eval_expr bitcoin_ge e le' mb ve (Vlong v)) ->
  Clight2.eval_funcall bitcoin_ge mb (Internal wf)
    [Vptr bd (Ptrofs.repr dbase); Vlong v] E0 me Vundef ->
  exists le', Clight2.exec_stmt bitcoin_ge e le mb (bitcoin_indexed_then t3 t4 t5 arrfield sid ve wid)
    E0 le' me Out_normal.
Proof.
  intros Ht3i Ht3d Ht4i Ht4d Ht5d Hin Hty He HEnv HDst HI He0 He1 Ht0 Ha0 HaM HF Hload1 Hload2 Hval Hcall.
  set (le_a := PTree.set t3 (Vptr bt (Ptrofs.repr txbase)) le).
  set (le_b := PTree.set t4 (Vptr bin (Ptrofs.repr inbase)) le_a).
  set (le_c := PTree.set t5 (Vlong v) le_b).
  exists le_c. unfold bitcoin_indexed_then.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le_a).
  - apply exec_set.
    eapply eval_bitcoin_field_value with (sid := _txEnv) (delta := 0) (chunk := Mptr).
    + reflexivity.
    + exact bitcoin_txEnv_tx.
    + reflexivity.
    + apply eval_bitcoin_deref_struct; exact HEnv.
    + rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact Hload1].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le_b).
    + apply exec_set.
      eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := adelta) (chunk := Mptr).
      * reflexivity.
      * exact HF.
      * reflexivity.
      * apply eval_bitcoin_deref_struct. unfold le_a. apply PTree.gss.
      * rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact Hload2].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le_c).
      * apply exec_set. apply Hval; [unfold le_b; apply PTree.gss|].
        unfold le_b, le_a. gso2. gso2. exact HI.
      * eapply exec_bitcoin_helper_call with (id := wid) (f := wf)
          (vargs := [Vptr bd (Ptrofs.repr dbase); Vlong v]) (vres := Vundef).
        -- exact Hin.
        -- exact He.
        -- eapply eval_Econs.
           ++ apply eval_Etempvar. unfold le_c, le_b, le_a. gso2. gso2. gso2. exact HDst.
           ++ reflexivity.
           ++ eapply eval_Econs; [apply eval_Etempvar; unfold le_c; apply PTree.gss|reflexivity|apply eval_Enil].
        -- exact Hty.
        -- exact Hcall.
Qed.
