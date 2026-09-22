(** Direct Clight execution lemmas for [f_writeBit]. *)

From Coq Require Import ZArith List PArith.BinPos.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.

Require Import C.jet_exec.
Require Import jets.

Import Clightdefs Clightdefs.ClightNotations.
Import Values Mem Ctypes.
Import Events.

Local Open Scope Z_scope.
Local Open Scope clight_scope.

Lemma exec_writeBit_debug_loop : forall (ge : genv) (e : env)
    (le : temp_env) (m : mem),
  ClightBigstep.Clight2.exec_stmt ge e le m
    (Sloop
      (Sifthenelse
        (Eunop Onotbool (Econst_int (Int.repr 0) tint) tint)
        Sskip Sskip)
      Sbreak)
    E0 le m Out_normal.
Proof.
  intros ge e le m.
  eapply ClightBigstep.exec_Sloop_stop2
    with (t1 := E0) (le1 := le) (m1 := m) (out1 := Out_normal)
         (t2 := E0) (le2 := le) (m2 := m) (out2 := Out_break).
  - eapply ClightBigstep.exec_Sifthenelse
      with (v1 := Vint Int.one) (b := true).
    + eapply eval_Eunop.
      * apply eval_Econst_int.
      * cbn; reflexivity.
    + reflexivity.
    + apply ClightBigstep.exec_Sskip.
  - constructor.
  - apply ClightBigstep.exec_Sbreak.
  - constructor.
Qed.

Definition le_writeBit0 (bf : block) : temp_env :=
  PTree.set _bit (Vint Int.zero)
    (PTree.set _frame (Vptr bf Ptrofs.zero)
      (create_undef_temps f_writeBit.(fn_temps))).

Lemma entry_writeBit0 : forall (m : mem) (bf : block),
  function_entry2 ge0 f_writeBit
    (Vptr bf Ptrofs.zero :: Vint Int.zero :: nil) m
    empty_env (le_writeBit0 bf) m.
Proof.
  intros m bf.
  constructor.
  - constructor.
  - constructor.
    + simpl; intro H; destruct H as [H | H].
      * vm_compute in H; congruence.
      * contradiction.
    + constructor.
      * simpl; intro H; contradiction.
      * constructor.
  - intros id1 id2 H1 H2 Heq.
    simpl in H1, H2.
    subst id2.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H
    end.
    all: vm_compute in *; congruence.
  - constructor.
  - reflexivity.
Qed.

Definition le_writeBit_offset (bf : block) : temp_env :=
  PTree.set _t'8 (Vlong (Int64.repr 9)) (le_writeBit0 bf).

Definition le_writeBit_edge (bf bw : block) : temp_env :=
  PTree.set _t'6 (Vptr bw Ptrofs.zero) (le_writeBit_offset bf).

Definition le_writeBit_t7 (bf bw : block) : temp_env :=
  PTree.set _t'7 (Vlong (Int64.repr 8)) (le_writeBit_edge bf bw).

Definition le_writeBit_ptr (bf bw : block) : temp_env :=
  PTree.set _dst_ptr (Vptr bw Ptrofs.zero) (le_writeBit_t7 bf bw).

Definition le_writeBit_t2 (bf bw : block) : temp_env :=
  PTree.set _t'2 (Vlong Int64.zero) (le_writeBit_ptr bf bw).

Definition le_writeBit_t3 (bf bw : block) : temp_env :=
  PTree.set _t'3 (Vlong (Int64.repr 8)) (le_writeBit_t2 bf bw).

Definition le_writeBit_t1 (bf bw : block) : temp_env :=
  PTree.set _t'1 (Vlong Int64.zero) (le_writeBit_t3 bf bw).

Ltac eval_writeBit_closed :=
  first [ eapply eval_Ecast;
          [ eval_writeBit_closed | cbn; vm_compute; reflexivity ]
        | eapply eval_Eunop;
          [ eval_writeBit_closed | cbn; vm_compute; reflexivity ]
        | eapply eval_Ebinop;
          [ eval_writeBit_closed | eval_writeBit_closed |
            cbn; vm_compute; reflexivity ]
        | eapply eval_Etempvar;
          simpl [le_writeBit_t3 le_writeBit_t2 le_writeBit_ptr
            le_writeBit_t7 le_writeBit_edge le_writeBit_offset le_writeBit0];
          reflexivity
        | apply eval_Econst_int
        | (cbn; vm_compute; reflexivity) ].

Lemma eval_dst_word_lvalue : forall (m : mem) (le : temp_env) (bw : block),
  le!_dst_ptr = Some (Vptr bw Ptrofs.zero) ->
  eval_lvalue ge0 empty_env le m
    (Ederef (Etempvar _dst_ptr (tptr tulong)) tulong)
    bw Ptrofs.zero Full.
Proof.
  intros m le bw Hle.
  eapply eval_Ederef.
  eapply eval_Etempvar; exact Hle.
Qed.

Lemma eval_dst_word : forall (m : mem) (le : temp_env) (bw : block)
    (v : int64),
  le!_dst_ptr = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bw 0 = Some (Vlong v) ->
  eval_expr ge0 empty_env le m
    (Ederef (Etempvar _dst_ptr (tptr tulong)) tulong)
    (Vlong v).
Proof.
  intros m le bw v Hle Hload.
  eapply eval_Elvalue.
  - eapply eval_Ederef; eapply eval_Etempvar; exact Hle.
  - apply deref_loc_value with (chunk := Mint64).
    + reflexivity.
    + simpl [Mem.loadv]; exact Hload.
Qed.

Lemma assign_dst_word : forall (m m' : mem) (le : temp_env) (bw : block)
    (v : int64),
  le!_dst_ptr = Some (Vptr bw Ptrofs.zero) ->
  Mem.store Mint64 m bw 0 (Vlong v) = Some m' ->
  assign_loc (prog_comp_env prog) tulong m bw Ptrofs.zero Full
    (Vlong v) m'.
Proof.
  intros m m' le bw v Hle Hstore.
  apply assign_loc_value with (chunk := Mint64).
  - reflexivity.
  - simpl [Mem.storev]; exact Hstore.
Qed.

Lemma eval_writeBit_zero : forall (m m1 m2 : mem) (bf bw : block),
  Mem.load Mptr m bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr 9)) ->
  Mem.store Mint64 m bf 8 (Vlong (Int64.repr 8)) = Some m1 ->
  Mem.load Mptr m1 bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m1 bf 8 = Some (Vlong (Int64.repr 8)) ->
  Mem.load Mint64 m1 bw 0 = Some (Vlong Int64.zero) ->
  Mem.store Mint64 m1 bw 0 (Vlong Int64.zero) = Some m2 ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBclear = Some 71%positive ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr 71%positive Ptrofs.zero) =
    Some (Internal f_LSBclear) ->
  ClightBigstep.Clight2.eval_funcall ge0 m1 (Internal f_LSBclear)
    (Vlong Int64.zero :: Vlong (Int64.repr 9) :: nil) E0 m1
    (Vlong Int64.zero) ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env (le_writeBit0 bf) m
    (fn_body f_writeBit) E0 (le_writeBit_t1 bf bw) m2
    (Out_return (Some (Vint Int.zero, tbool))).
Proof.
  intros m m1 m2 bf bw Hedge Hoffset Hstore_offset Hedge1 Hoffset1
    Hword Hstore_word Hsym Hfun Hclear.
  unfold f_writeBit; cbn.
  eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - apply exec_writeBit_debug_loop.
  - eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_set.
        eapply eval_frame_offset.
        { simpl [le_writeBit0]; reflexivity. }
        { exact Hoffset. }
      * eapply exec_Sassign_value.
        -- apply eval_frame_offset_lvalue.
           simpl [le_writeBit_offset le_writeBit0]; reflexivity.
        -- eapply eval_Ebinop.
           ++ eapply eval_Etempvar.
              simpl [le_writeBit_offset le_writeBit0]; reflexivity.
           ++ apply eval_Econst_int.
           ++ cbn; reflexivity.
        -- cbn; reflexivity.
        -- apply assign_frame_offset with
             (le := le_writeBit_offset bf).
           ++ simpl [le_writeBit_offset le_writeBit0]; reflexivity.
           ++ exact Hstore_offset.
    + eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply exec_set.
           eapply eval_frame_edge.
           ++ simpl [le_writeBit_offset le_writeBit0]; reflexivity.
           ++ exact Hedge1.
        -- eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ apply exec_set.
              eapply eval_frame_offset.
              { simpl [le_writeBit_edge le_writeBit_offset le_writeBit0].
                reflexivity. }
              { exact Hoffset1. }
           ++ apply exec_set.
              eapply eval_Ebinop.
              ** eapply eval_Etempvar.
                 simpl [le_writeBit_edge le_writeBit_offset le_writeBit0].
                 reflexivity.
              ** eapply eval_Ebinop.
                 --- eapply eval_Etempvar.
                     simpl [le_writeBit_t7 le_writeBit_edge
                       le_writeBit_offset le_writeBit0]. reflexivity.
                 --- eval_writeBit_closed.
                 --- cbn; vm_compute; reflexivity.
              ** cbn; vm_compute; reflexivity.
      * eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- eapply ClightBigstep.exec_Sifthenelse
             with (v1 := Vint Int.zero) (b := false).
           ++ eapply eval_Etempvar.
              simpl [le_writeBit0]; reflexivity.
           ++ reflexivity.
           ++ eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
              ** eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
                 --- apply exec_set.
                     eapply eval_dst_word.
                     +++ simpl [le_writeBit_ptr le_writeBit_t7
                           le_writeBit_edge le_writeBit_offset le_writeBit0].
                         reflexivity.
                     +++ exact Hword.
                 --- eapply ClightBigstep.exec_Sseq_1
                       with (t1 := E0) (t2 := E0).
                     +++ apply exec_set.
                         eapply eval_frame_offset.
                         { simpl [le_writeBit_t2 le_writeBit_ptr
                             le_writeBit_t7 le_writeBit_edge
                             le_writeBit_offset le_writeBit0]. reflexivity. }
                         { exact Hoffset1. }
                     +++ eapply ClightBigstep.exec_Scall
                           with (vf := Vptr 71%positive Ptrofs.zero)
                                (vargs := Vlong Int64.zero ::
                                  Vlong (Int64.repr 9) :: nil)
                                (f := Internal f_LSBclear)
                                (vres := Vlong Int64.zero).
                         ---- vm_compute; reflexivity.
                         ---- eapply eval_Elvalue.
                              { eapply eval_Evar_global.
                                - simpl; reflexivity.
                                - exact Hsym. }
                              { apply deref_loc_reference.
                                change (access_mode
                                  (Tfunction
                                    (Tcons tulong (Tcons tulong Tnil))
                                    tulong cc_default) = By_reference).
                                reflexivity. }
                         ---- eapply eval_Econs.
                              { eapply eval_Etempvar.
                                simpl [le_writeBit_t2 le_writeBit_ptr
                                  le_writeBit_t7 le_writeBit_edge
                                  le_writeBit_offset le_writeBit0].
                                reflexivity. }
                              { reflexivity. }
                              { eapply eval_Econs.
                                - eval_writeBit_closed.
                                - reflexivity.
                                - apply eval_Enil. }
                         ---- exact Hfun.
                         ---- vm_compute; reflexivity.
                         ---- exact Hclear.
              ** eapply exec_Sassign_value.
                   { apply eval_dst_word_lvalue.
                     simpl [le_writeBit_ptr le_writeBit_t7 le_writeBit_edge
                       le_writeBit_offset le_writeBit0]. reflexivity. }
                   { eapply eval_Etempvar.
                     simpl [le_writeBit_t1 le_writeBit_t3 le_writeBit_t2
                       le_writeBit_ptr le_writeBit_t7 le_writeBit_edge
                       le_writeBit_offset le_writeBit0]. reflexivity. }
                   { cbn; reflexivity. }
                   { apply assign_dst_word with
                       (le := le_writeBit_t1 bf bw).
                     - simpl [le_writeBit_t1 le_writeBit_t3 le_writeBit_t2
                         le_writeBit_ptr le_writeBit_t7 le_writeBit_edge
                         le_writeBit_offset le_writeBit0]. reflexivity.
                     - exact Hstore_word. }
    -- apply ClightBigstep.exec_Sreturn_some.
    eapply eval_Etempvar.
    simpl [le_writeBit_t1 le_writeBit_t3 le_writeBit_t2 le_writeBit_ptr
      le_writeBit_t7 le_writeBit_edge le_writeBit_offset le_writeBit0].
    reflexivity.
Qed.

Definition le_writeBit1 (bf : block) : temp_env :=
  PTree.set _bit (Vint Int.one) (le_writeBit0 bf).

Lemma entry_writeBit1 : forall (m : mem) (bf : block),
  function_entry2 ge0 f_writeBit
    (Vptr bf Ptrofs.zero :: Vint Int.one :: nil) m
    empty_env (le_writeBit1 bf) m.
Proof.
  intros m bf.
  constructor.
  - constructor.
  - constructor.
    + simpl; intro H; destruct H as [H | H].
      * vm_compute in H; congruence.
      * contradiction.
    + constructor.
      * simpl; intro H; contradiction.
      * constructor.
  - intros id1 id2 H1 H2 Heq.
    simpl in H1, H2.
    subst id2.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H
    end.
    all: vm_compute in *; congruence.
  - constructor.
  - reflexivity.
Qed.

Definition le_writeBit1_offset (bf : block) : temp_env :=
  PTree.set _t'8 (Vlong (Int64.repr 9)) (le_writeBit1 bf).

Definition le_writeBit1_edge (bf bw : block) : temp_env :=
  PTree.set _t'6 (Vptr bw Ptrofs.zero) (le_writeBit1_offset bf).

Definition le_writeBit1_t7 (bf bw : block) : temp_env :=
  PTree.set _t'7 (Vlong (Int64.repr 8)) (le_writeBit1_edge bf bw).

Definition le_writeBit1_ptr (bf bw : block) : temp_env :=
  PTree.set _dst_ptr (Vptr bw Ptrofs.zero) (le_writeBit1_t7 bf bw).

Definition le_writeBit1_t4 (bf bw : block) : temp_env :=
  PTree.set _t'4 (Vlong Int64.zero) (le_writeBit1_ptr bf bw).

Definition le_writeBit1_t5 (bf bw : block) : temp_env :=
  PTree.set _t'5 (Vlong (Int64.repr 8)) (le_writeBit1_t4 bf bw).

Lemma eval_writeBit_one : forall (m m1 m2 : mem) (bf bw : block),
  Mem.load Mptr m bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr 9)) ->
  Mem.store Mint64 m bf 8 (Vlong (Int64.repr 8)) = Some m1 ->
  Mem.load Mptr m1 bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m1 bf 8 = Some (Vlong (Int64.repr 8)) ->
  Mem.load Mint64 m1 bw 0 = Some (Vlong Int64.zero) ->
  Mem.store Mint64 m1 bw 0 (Vlong (Int64.repr 256)) = Some m2 ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env (le_writeBit1 bf) m
    (fn_body f_writeBit) E0 (le_writeBit1_t5 bf bw) m2
    (Out_return (Some (Vint Int.one, tbool))).
Proof.
  intros m m1 m2 bf bw Hedge Hoffset Hstore_offset Hedge1 Hoffset1
    Hword Hstore_word.
  unfold f_writeBit; cbn.
  eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - apply exec_writeBit_debug_loop.
  - eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_set.
        eapply eval_frame_offset.
        { simpl [le_writeBit1]; reflexivity. }
        { exact Hoffset. }
      * eapply exec_Sassign_value.
        -- apply eval_frame_offset_lvalue.
           simpl [le_writeBit1_offset le_writeBit1]; reflexivity.
        -- eapply eval_Ebinop.
           ++ eapply eval_Etempvar.
              simpl [le_writeBit1_offset le_writeBit1]; reflexivity.
           ++ apply eval_Econst_int.
           ++ cbn; reflexivity.
        -- cbn; reflexivity.
        -- apply assign_frame_offset with (le := le_writeBit1_offset bf).
           ++ simpl [le_writeBit1_offset le_writeBit1]; reflexivity.
           ++ exact Hstore_offset.
    + eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply exec_set.
           eapply eval_frame_edge.
           ++ simpl [le_writeBit1_offset le_writeBit1]; reflexivity.
           ++ exact Hedge1.
        -- eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ apply exec_set.
              eapply eval_frame_offset.
              { simpl [le_writeBit1_edge le_writeBit1_offset le_writeBit1].
                reflexivity. }
              { exact Hoffset1. }
           ++ apply exec_set.
              eapply eval_Ebinop.
              ** eapply eval_Etempvar.
                 simpl [le_writeBit1_edge le_writeBit1_offset le_writeBit1].
                 reflexivity.
              ** eapply eval_Ebinop.
                 --- eapply eval_Etempvar.
                     simpl [le_writeBit1_t7 le_writeBit1_edge
                       le_writeBit1_offset le_writeBit1]. reflexivity.
                 --- eval_writeBit_closed.
                 --- cbn; vm_compute; reflexivity.
              ** cbn; vm_compute; reflexivity.
      * eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- eapply ClightBigstep.exec_Sifthenelse
             with (v1 := Vint Int.one) (b := true).
           ++ eapply eval_Etempvar.
              simpl [le_writeBit1]; reflexivity.
           ++ reflexivity.
           ++ eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
              ** apply exec_set.
                 eapply eval_dst_word.
                 { simpl [le_writeBit1_ptr le_writeBit1_t7
                     le_writeBit1_edge le_writeBit1_offset le_writeBit1].
                   reflexivity. }
                 { exact Hword. }
              ** eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
                 --- apply exec_set.
                     eapply eval_frame_offset.
                     { simpl [le_writeBit1_t4 le_writeBit1_ptr
                         le_writeBit1_t7 le_writeBit1_edge
                         le_writeBit1_offset le_writeBit1]. reflexivity. }
                     { exact Hoffset1. }
                 --- eapply exec_Sassign_value.
                     { apply eval_dst_word_lvalue.
                       simpl [le_writeBit1_ptr le_writeBit1_t7
                         le_writeBit1_edge le_writeBit1_offset le_writeBit1].
                       reflexivity. }
                     { eapply eval_Ebinop.
                       - eapply eval_Etempvar.
                         simpl [le_writeBit1_t4 le_writeBit1_ptr
                           le_writeBit1_t7 le_writeBit1_edge
                           le_writeBit1_offset le_writeBit1]. reflexivity.
                       - eapply eval_Ecast.
                         + eapply eval_Ebinop.
                           * eapply eval_Ecast.
                             { apply eval_Econst_int. }
                             { cbn; reflexivity. }
                           * eapply eval_Ebinop.
                             { eapply eval_Etempvar.
                               simpl [le_writeBit1_t5 le_writeBit1_t4
                                 le_writeBit1_ptr le_writeBit1_t7
                                 le_writeBit1_edge le_writeBit1_offset
                                 le_writeBit1]. reflexivity. }
                             { eval_writeBit_closed. }
                             { cbn; vm_compute; reflexivity. }
                           * cbn; vm_compute; reflexivity.
                         + cbn; reflexivity.
                       - cbn; reflexivity. }
                     { cbn; reflexivity. }
                     { apply assign_dst_word with
                         (le := le_writeBit1_t5 bf bw).
                       - simpl [le_writeBit1_t5 le_writeBit1_t4
                           le_writeBit1_ptr le_writeBit1_t7 le_writeBit1_edge
                           le_writeBit1_offset le_writeBit1]. reflexivity.
                       - exact Hstore_word. }
    -- apply ClightBigstep.exec_Sreturn_some.
    eapply eval_Etempvar.
    simpl [le_writeBit1_t5 le_writeBit1_t4 le_writeBit1_ptr le_writeBit1_t7
      le_writeBit1_edge le_writeBit1_offset le_writeBit1]. reflexivity.
Qed.

Definition le_LSBclear9 (w : int64) : temp_env :=
  PTree.set _n (Vlong (Int64.repr 9))
    (PTree.set _x (Vlong w) (PTree.empty val)).

Lemma entry_LSBclear9_value : forall (m : mem) (w : int64),
  function_entry2 ge0 f_LSBclear
    (Vlong w :: Vlong (Int64.repr 9) :: nil) m
    empty_env (le_LSBclear9 w) m.
Proof.
  intros m w.
  constructor.
  - constructor.
  - constructor.
    + simpl; intro H; destruct H as [H | H].
      * vm_compute in H; congruence.
      * contradiction.
    + constructor.
      * simpl; intro H; contradiction.
      * constructor.
  - intros id1 id2 H1 H2 Heq; simpl in H1, H2; tauto.
  - constructor.
  - reflexivity.
Qed.

Lemma eval_LSBclear9_n_minus_one : forall (m : mem) (w : int64),
  eval_expr ge0 empty_env (le_LSBclear9 w) m
    (Ebinop Osub (Etempvar _n tulong)
      (Econst_int (Int.repr 1) tint) tulong)
    (Vlong (Int64.repr 8)).
Proof.
  intros m w.
  eapply eval_Ebinop.
  - eapply eval_Etempvar.
    simpl [le_LSBclear9]. reflexivity.
  - apply eval_Econst_int.
  - cbn; vm_compute; reflexivity.
Qed.

Ltac eval_LSBclear9_value :=
  first [ eapply eval_Ecast; [ eval_LSBclear9_value | cbn; reflexivity ]
        | eapply eval_Ebinop;
            [ eval_LSBclear9_value | eval_LSBclear9_value | cbn; reflexivity ]
        | eapply eval_Etempvar; simpl [le_LSBclear9]; reflexivity
        | (cbn; vm_compute; reflexivity) ].

Lemma eval_LSBclear9_zero : forall (m : mem),
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBclear)
    (Vlong Int64.zero :: Vlong (Int64.repr 9) :: nil) E0 m
    (Vlong Int64.zero).
Proof.
  intros m.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_LSBclear9 Int64.zero) (m1 := m)
         (le2 := le_LSBclear9 Int64.zero) (m2 := m).
  - apply entry_LSBclear9_value.
  - simpl [f_LSBclear].
    apply ClightBigstep.exec_Sreturn_some.
    pose proof (eval_LSBclear9_n_minus_one m Int64.zero) as Hn.
    eapply eval_Ecast.
    + eapply eval_Ebinop.
      * eapply eval_Ebinop.
        -- eapply eval_Ebinop.
           ++ eapply eval_Ebinop.
              --- eapply eval_Etempvar.
                  simpl [le_LSBclear9]. reflexivity.
              --- apply eval_Econst_int.
              --- cbn; reflexivity.
           ++ exact Hn.
           ++ cbn; reflexivity.
      -- apply eval_Econst_int.
      -- cbn; reflexivity.
      * exact Hn.
      * cbn; reflexivity.
    + cbn; reflexivity.
  - cbn; split; [discriminate | reflexivity].
  - simpl; reflexivity.
Qed.
