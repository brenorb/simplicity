(** Execution of the real [copyWords] helper on an initialized UWORD.
    Its one-word branch is a Clight load and store, with no library premise.
    Larger copies still use libc and are outside this theorem's scope. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque ge0.
Set Default Timeout 10.

Definition block_copyWords := jet_symbol_block _copyWords.

Lemma symbol_copyWords :
  Genv.find_symbol (Clight.genv_genv ge0) _copyWords = Some block_copyWords.
Proof. vm_compute; reflexivity. Qed.

Lemma funct_copyWords :
  Genv.find_funct (Clight.genv_genv ge0) (Vptr block_copyWords Ptrofs.zero) =
    Some (Internal f_copyWords).
Proof. vm_compute; reflexivity. Qed.

Definition copy_word_env bd dst bs src :=
  PTree.set _bytes (Vlong (Int64.repr 8))
    (PTree.set _src (Vptr bs src)
      (PTree.set _dst (Vptr bd dst) (create_undef_temps f_copyWords.(fn_temps)))).

Lemma copy_word_entry m bd dst bs src :
  function_entry2 ge0 f_copyWords
    [Vptr bd dst; Vptr bs src; Vlong (Int64.repr 8)]
    m empty_env (copy_word_env bd dst bs src) m.
Proof.
  constructor.
  - constructor.
  - cbn. unfold _dst, _src, _bytes.
    repeat constructor; simpl; intuition discriminate.
  - change (list_disjoint [_dst; _src; _bytes] [_t'1]).
    intros i j HI HJ Heq; cbn in HI, HJ; subst j.
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
      try contradiction; vm_compute in *; congruence.
  - constructor.
  - reflexivity.
Qed.

Lemma eval_copy_word m m' bd dst bs src v :
  Mem.load Mint64 m bs (Ptrofs.unsigned src) = Some (Vlong v) ->
  Mem.store Mint64 m bd (Ptrofs.unsigned dst) (Vlong v) = Some m' ->
  Clight2.eval_funcall ge0 m (Internal f_copyWords)
    [Vptr bd dst; Vptr bs src; Vlong (Int64.repr 8)] E0 m' Vundef.
Proof.
  intros HL HS.
  set (le := copy_word_env bd dst bs src).
  set (le' := PTree.set _t'1 (Vlong v) le).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le) (le2 := le')
    (m1 := m) (m2 := m') (out := Out_normal).
  - apply copy_word_entry.
  - unfold f_copyWords; cbn [fn_body].
    eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
    + eapply eval_Ebinop with (v1 := Vlong (Int64.repr 8)) (v2 := Vlong (Int64.repr 8)).
      * apply eval_Etempvar. reflexivity.
      * apply eval_Esizeof.
      * reflexivity.
    + reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le').
      * apply exec_Sset. eapply eval_Elvalue.
        -- apply eval_Ederef. apply eval_Etempvar. reflexivity.
        -- eapply deref_loc_value with (chunk := Mint64); [reflexivity|exact HL].
      * eapply exec_Sassign with (loc := bd) (ofs := dst) (bf := Full)
          (v2 := Vlong v) (v := Vlong v).
        -- apply eval_Ederef. apply eval_Etempvar. reflexivity.
        -- apply eval_Etempvar. reflexivity.
        -- reflexivity.
        -- eapply assign_loc_value with (chunk := Mint64); [reflexivity|exact HS].
  - reflexivity.
  - reflexivity.
Qed.
