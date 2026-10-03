(** Calling a transported core helper from Bitcoin jet code. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Ctypes Clight Maps Globalenvs ClightBigstep Memory Events Values.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_transport.
Require C.jets.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Local Opaque bitcoin_ge.
Set Default Timeout 60.

Lemma bitcoin_helper_lookup id f :
  In (id, f) bitcoin_core_helpers ->
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) id = Some (bitcoin_symbol_block id) /\
  Genv.find_funct (Clight.genv_genv bitcoin_ge) (Vptr (bitcoin_symbol_block id) Ptrofs.zero) =
    Some (Internal f).
Proof.
  intros Hin. destruct (bitcoin_core_helpers_entries id f Hin) as (b1 & b2 & _ & _ & Hs & Hf).
  assert (Hb : bitcoin_symbol_block id = b2).
  { unfold bitcoin_symbol_block. rewrite Hs. reflexivity. }
  rewrite Hb. split; [exact Hs|].
  unfold Genv.find_funct. rewrite pred_dec_true by reflexivity. exact Hf.
Qed.

Lemma exec_bitcoin_helper_call e le m optid id f al tyargs tyres cc vargs vres m' :
  In (id, f) bitcoin_core_helpers ->
  e!id = None -> eval_exprlist bitcoin_ge e le m al tyargs vargs ->
  type_of_fundef (Internal f) = Tfunction tyargs tyres cc ->
  Clight2.eval_funcall bitcoin_ge m (Internal f) vargs E0 m' vres ->
  Clight2.exec_stmt bitcoin_ge e le m (Scall optid (Evar id (Tfunction tyargs tyres cc)) al) E0
    (set_opttemp optid vres le) m' Out_normal.
Proof.
  intros Hin He Hargs Hty Hcall. destruct (bitcoin_helper_lookup id f Hin) as [Hs Hf].
  eapply exec_Scall with (vf := Vptr (bitcoin_symbol_block id) Ptrofs.zero) (f := Internal f).
  - reflexivity.
  - eapply eval_Elvalue.
    + apply eval_Evar_global; [exact He|exact Hs].
    + apply deref_loc_reference; reflexivity.
  - exact Hargs.
  - exact Hf.
  - exact Hty.
  - exact Hcall.
Qed.
