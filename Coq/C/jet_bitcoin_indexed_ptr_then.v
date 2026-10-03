(** Success branch of an indexed Bitcoin getter whose payload is written by a
    Bitcoin-unit helper taking a pointer into the selected element:
      t3 = env->tx; t4 = t3->ARRAY; HELPER(dst, &t4[i].FIELD); *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_frame_layout C.jets_bitcoin C.jet_bitcoin_linkage.
Require Import C.jet_bitcoin_field_eval.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge.
Set Default Timeout 60.

Definition bitcoin_indexed_then_ptr (t3 t4 arrfield sid : ident) (pexpr : expr) (cid : ident) (pt : type) : statement :=
  Ssequence
    (Sset t3 (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
      _tx (tptr (Tstruct _bitcoinTransaction noattr))))
    (Ssequence
      (Sset t4 (Efield (Ederef (Etempvar t3 (tptr (Tstruct _bitcoinTransaction noattr)))
        (Tstruct _bitcoinTransaction noattr)) arrfield (tptr (Tstruct sid noattr))))
      (Scall None
        (Evar cid (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr pt) Tnil)) tvoid cc_default))
        [Etempvar _dst (tptr (Tstruct _frameItem noattr)); pexpr])).

Ltac gsop := rewrite PTree.gso by (first [assumption | apply not_eq_sym; assumption | discriminate]).

Lemma exec_bitcoin_indexed_then_ptr e le t3 t4 arrfield adelta sid pexpr cid pt cf pofs
    mb me be ebase bt txbase bin inbase bd dbase r :
  t3 <> _i -> t3 <> _dst -> t4 <> _i -> t4 <> _dst -> typeof pexpr = tptr pt ->
  e!cid = None ->
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) cid = Some (bitcoin_symbol_block cid) ->
  Genv.find_funct (Clight.genv_genv bitcoin_ge) (Vptr (bitcoin_symbol_block cid) Ptrofs.zero) = Some (Internal cf) ->
  type_of_fundef (Internal cf) = Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr pt) Tnil)) tvoid cc_default ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_i = Some (Vlong r) ->
  0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  0 <= txbase -> 0 <= adelta -> txbase + adelta + 8 <= Ptrofs.max_unsigned ->
  bitcoin_field_at _bitcoinTransaction arrfield adelta ->
  Mem.load Mptr mb be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mptr mb bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) ->
  (forall le', le'!t4 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!_i = Some (Vlong r) ->
    eval_expr bitcoin_ge e le' mb pexpr (Vptr bin (Ptrofs.repr pofs))) ->
  Clight2.eval_funcall bitcoin_ge mb (Internal cf)
    [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr pofs)] E0 me Vundef ->
  exists le', Clight2.exec_stmt bitcoin_ge e le mb (bitcoin_indexed_then_ptr t3 t4 arrfield sid pexpr cid pt)
    E0 le' me Out_normal.
Proof.
  intros Ht3i Ht3d Ht4i Ht4d Hpty He Hsym Hfun Hty HEnv HDst HI He0 He1 Ht0 Ha0 HaM HF Hl1 Hl2 Hptr Hcall.
  set (le_a := PTree.set t3 (Vptr bt (Ptrofs.repr txbase)) le).
  set (le_b := PTree.set t4 (Vptr bin (Ptrofs.repr inbase)) le_a).
  exists le_b. unfold bitcoin_indexed_then_ptr.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le_a).
  - apply exec_set.
    eapply eval_bitcoin_field_value with (sid := _txEnv) (delta := 0) (chunk := Mptr).
    + reflexivity.
    + exact bitcoin_txEnv_tx.
    + reflexivity.
    + apply eval_bitcoin_deref_struct; exact HEnv.
    + rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact Hl1].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le_b).
    + apply exec_set.
      eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := adelta) (chunk := Mptr).
      * reflexivity.
      * exact HF.
      * reflexivity.
      * apply eval_bitcoin_deref_struct. unfold le_a. apply PTree.gss.
      * rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact Hl2].
    + eapply exec_Scall with (vf := Vptr (bitcoin_symbol_block cid) Ptrofs.zero) (f := Internal cf)
        (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr pofs)]) (vres := Vundef).
      * reflexivity.
      * eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact Hsym]|apply deref_loc_reference; reflexivity].
      * eapply eval_Econs; [apply eval_Etempvar; unfold le_b, le_a; gsop; gsop; exact HDst|reflexivity|].
        eapply eval_Econs.
        -- apply Hptr; [unfold le_b; apply PTree.gss|unfold le_b, le_a; gsop; gsop; exact HI].
        -- rewrite Hpty. reflexivity.
        -- apply eval_Enil.
      * exact Hfun.
      * exact Hty.
      * exact Hcall.
Qed.
