(** Direct Clight execution setup for [simplicity_read8] at a one-word,
    byte-aligned layout. *)

From Coq Require Import ZArith List PArith.BinPos.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.

Require Import C.jet_exec.
Require Import C.jet_write8.
Require Import C.jets.

Import Clightdefs Clightdefs.ClightNotations.
Import Values Mem Ctypes.
Import Events.

Local Open Scope Z_scope.
Local Open Scope clight_scope.

Definition le_read8 (bf : block) : temp_env :=
  PTree.set _frame (Vptr bf Ptrofs.zero)
    (create_undef_temps f_simplicity_read8.(fn_temps)).

Lemma entry_read8 : forall (m : mem) (bf : block),
  function_entry2 ge0 f_simplicity_read8
    (Vptr bf Ptrofs.zero :: nil) m empty_env (le_read8 bf) m.
Proof.
  intros m bf.
  constructor.
  - constructor.
  - constructor.
    + simpl; tauto.
    + constructor.
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

Definition le_read8_result (bf : block) : temp_env :=
  PTree.set _result (Vint Int.zero) (le_read8 bf).
Definition le_read8_edge (bf bs : block) : temp_env :=
  PTree.set _t'10 (Vptr bs (Ptrofs.repr 8)) (le_read8_result bf).
Definition le_read8_offset (bf bs : block) : temp_env :=
  PTree.set _t'11 (Vlong (Int64.repr 56)) (le_read8_edge bf bs).
Definition le_read8_ptr (bf bs : block) : temp_env :=
  PTree.set _frame_ptr (Vptr bs Ptrofs.zero) (le_read8_offset bf bs).
Definition le_read8_t9 (bf bs : block) : temp_env :=
  PTree.set _t'9 (Vlong (Int64.repr 56)) (le_read8_ptr bf bs).
Definition le_read8_shift (bf bs : block) : temp_env :=
  PTree.set _frame_shift (Vlong (Int64.repr 8)) (le_read8_t9 bf bs).
Definition le_read8_n (bf bs : block) : temp_env :=
  PTree.set _n (Vlong (Int64.repr 8)) (le_read8_shift bf bs).
Definition le_read8_word (bf bs : block) (w : int64) : temp_env :=
  PTree.set _t'4 (Vlong w) (le_read8_n bf bs).
Definition le_read8_keep (bf bs : block) (w k : int64) : temp_env :=
  PTree.set _t'2 (Vlong k) (le_read8_word bf bs w).
Definition le_read8_result_final (bf bs : block) (w k : int64)
    (r : int) : temp_env :=
  PTree.set _result (Vint r) (le_read8_keep bf bs w k).
Definition le_read8_t3 (bf bs : block) (w k : int64) (r : int) : temp_env :=
  PTree.set _t'3 (Vlong (Int64.repr 56))
    (le_read8_result_final bf bs w k r).

Ltac eval_closed_read8 :=
  lazymatch goal with
  | |- eval_expr _ _ _ _ (Ecast _ _) _ =>
      eapply eval_Ecast;
      [ eval_closed_read8 | cbn; vm_compute; reflexivity ]
  | |- eval_expr _ _ _ _ (Eunop _ _ _) _ =>
      eapply eval_Eunop;
      [ eval_closed_read8 | cbn; vm_compute; reflexivity ]
  | |- eval_expr _ _ _ _ (Ebinop _ _ _ _) _ =>
      eapply eval_Ebinop;
      [ eval_closed_read8 | eval_closed_read8 | cbn; vm_compute; reflexivity ]
  | |- eval_expr _ _ _ _ (Econst_int _ _) _ => apply eval_Econst_int
  | |- eval_expr _ _ _ _ (Econst_long _ _) _ => apply eval_Econst_long
  end.

Lemma eval_frame_edge_ofs_early : forall (m : mem) (le : temp_env)
    (bf bs : block) (ofs : ptrofs),
  le!_frame = Some (Vptr bf Ptrofs.zero) ->
  Mem.load Mptr m bf 0 = Some (Vptr bs ofs) ->
  eval_expr ge0 empty_env le m
    (Efield (Ederef (Etempvar _frame (tptr (Tstruct _frameItem noattr)))
       (Tstruct _frameItem noattr)) _edge (tptr tulong))
    (Vptr bs ofs).
Proof.
  intros m le bf bs ofs Hle Hload.
  eapply eval_Elvalue.
  - eapply eval_Efield_struct.
    + eapply eval_Elvalue.
      * eapply eval_Ederef.
        eapply eval_Etempvar; exact Hle.
      * apply deref_loc_copy.
        change (access_mode (Tstruct _frameItem noattr) = By_copy).
        reflexivity.
    + reflexivity.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
  - apply deref_loc_value with (chunk := Mptr).
    + vm_compute; reflexivity.
    + simpl [Mem.loadv]. exact Hload.
Qed.

Definition read8_keep_stmt_early : statement :=
  Scall (Some _t'2)
    (Evar _LSBkeep
      (Tfunction (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
    ((Ecast
       (Ebinop Oshr (Etempvar _t'4 tulong)
         (Ebinop Osub (Etempvar _frame_shift tulong)
           (Etempvar _n tulong) tulong) tulong) tulong) ::
     (Etempvar _n tulong) :: nil).

Lemma call_read8_keep_early : forall (le : temp_env) (m : mem)
    (w k : int64) (b : block),
  le!_t'4 = Some (Vlong w) ->
  le!_frame_shift = Some (Vlong (Int64.repr 8)) ->
  le!_n = Some (Vlong (Int64.repr 8)) ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBkeep = Some b ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr b Ptrofs.zero) =
    Some (Internal f_LSBkeep) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBkeep)
    (Vlong w :: Vlong (Int64.repr 8) :: nil) E0 m (Vlong k) ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env le m read8_keep_stmt_early
    E0 (PTree.set _t'2 (Vlong k) le) m Out_normal.
Proof.
  intros le m w k b Hword Hshift Hn Hsym Hfun Heval.
  change (ClightBigstep.exec_stmt function_entry2 ge0 empty_env le m
    read8_keep_stmt_early E0 (set_opttemp (Some _t'2) (Vlong k) le) m
    Out_normal).
  eapply ClightBigstep.exec_Scall
    with (vf := Vptr b Ptrofs.zero)
         (vargs := Vlong w :: Vlong (Int64.repr 8) :: nil)
         (f := Internal f_LSBkeep) (vres := Vlong k).
  - vm_compute; reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global.
      * simpl; reflexivity.
      * exact Hsym.
    + apply deref_loc_reference.
      change (access_mode
        (Tfunction (Tcons tulong (Tcons tulong Tnil)) tulong cc_default) =
        By_reference).
      reflexivity.
  - eapply eval_Econs.
    + eapply eval_Ecast with (v1 := Vlong w).
      * eapply eval_Ebinop with (v1 := Vlong w)
          (v2 := Vlong Int64.zero).
        -- apply eval_Etempvar; exact Hword.
        -- eapply eval_Ebinop with (v1 := Vlong (Int64.repr 8))
             (v2 := Vlong (Int64.repr 8)).
           ++ apply eval_Etempvar; exact Hshift.
           ++ apply eval_Etempvar; exact Hn.
           ++ reflexivity.
        -- change (Some (Vlong (Int64.shru w Int64.zero)) =
             Some (Vlong w)).
           rewrite Int64.shru_zero; reflexivity.
      * reflexivity.
    + reflexivity.
    + eapply eval_Econs.
      * eapply eval_Etempvar; exact Hn.
      * reflexivity.
      * apply eval_Enil.
  - exact Hfun.
  - vm_compute; reflexivity.
  - exact Heval.
Qed.

Definition read8_result (w : int64) : int :=
  Int.zero_ext 8
    (Int.or Int.zero
      (Int.zero_ext 8
        (Int.repr (Int64.unsigned (Int64.and w (Int64.repr 255)))))).

Definition read8_result_expr : expr :=
  Ecast
    (Ebinop Oor (Etempvar _result tuchar)
      (Ecast (Etempvar _t'2 tulong) tuchar) tint)
    tuchar.

Lemma eval_read8_body : forall (m m' : mem) (bf bs : block) (w : int64),
  Mem.load Mptr m bf 0 = Some (Vptr bs (Ptrofs.repr 8)) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr 56)) ->
  Mem.load Mint64 m bs 0 = Some (Vlong w) ->
  Mem.store Mint64 m bf 8 (Vlong (Int64.repr 64)) = Some m' ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBkeep = Some 72%positive ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr 72%positive Ptrofs.zero) =
    Some (Internal f_LSBkeep) ->
  eval_expr ge0 empty_env
    (le_read8_keep bf bs w (Int64.and w (Int64.repr 255))) m
    read8_result_expr (Vint (read8_result w)) ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env (le_read8 bf) m
    (fn_body f_simplicity_read8) E0
    (le_read8_t3 bf bs w (Int64.and w (Int64.repr 255))
      (read8_result w)) m'
    (Out_return (Some (Vint (read8_result w), tuchar))).
Proof.
  intros m m' bf bs w Hedge Hoffset Hword Hstore Hsym Hfun Hresult.
  unfold f_simplicity_read8; cbn.
  eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - apply exec_set.
    eapply eval_Ecast.
    + apply eval_Econst_int.
    + cbn; reflexivity.
  - eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_set.
        eapply eval_frame_edge_ofs_early.
        -- simpl [le_read8_result le_read8]; reflexivity.
        -- exact Hedge.
      * eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply exec_set.
           eapply eval_frame_offset.
           ++ simpl [le_read8_edge le_read8_result le_read8]; reflexivity.
           ++ exact Hoffset.
        -- apply exec_set.
           eapply eval_Ebinop with (v1 := Vptr bs Ptrofs.zero)
             (v2 := Vlong Int64.zero).
           ++ eapply eval_Ebinop with
                (v1 := Vptr bs (Ptrofs.repr 8))
                (v2 := Vint (Int.repr 1)).
              ** eapply eval_Etempvar.
                 simpl [le_read8_offset le_read8_edge le_read8_result
                   le_read8]. reflexivity.
              ** apply eval_Econst_int.
              ** cbn; reflexivity.
           ++ eapply eval_Ebinop with
                (v1 := Vlong (Int64.repr 56))
                (v2 := Vlong (Int64.repr 64)).
              ** eapply eval_Etempvar.
                 simpl [le_read8_offset le_read8_edge le_read8_result
                   le_read8]. reflexivity.
              ** eval_closed_read8.
              ** cbn; reflexivity.
           ++ cbn; reflexivity.
    + eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply exec_set.
        eapply eval_frame_offset.
        --- simpl [le_read8_ptr le_read8_offset le_read8_edge
             le_read8_result le_read8]; reflexivity.
        --- exact Hoffset.
        -- apply exec_set.
        eapply eval_Ebinop with (v1 := Vlong (Int64.repr 64))
          (v2 := Vlong (Int64.repr 56)).
        --- eval_closed_read8.
        --- eapply eval_Ebinop with (v1 := Vlong (Int64.repr 56))
             (v2 := Vlong (Int64.repr 64)).
           +++ eapply eval_Etempvar.
              simpl [le_read8_t9 le_read8_ptr le_read8_offset le_read8_edge
                le_read8_result le_read8]; reflexivity.
           +++ eval_closed_read8.
           +++ cbn; reflexivity.
        --- cbn; reflexivity.
      * eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply exec_set.
        eapply eval_Ecast.
        --- apply eval_Econst_int.
        --- cbn; reflexivity.
        -- eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
              +++ eapply eval_Ebinop with (v1 := Vlong (Int64.repr 8))
                (v2 := Vlong (Int64.repr 8)).
              **** eapply eval_Etempvar.
                 simpl [le_read8_shift le_read8_t9 le_read8_ptr
                   le_read8_offset le_read8_edge le_read8_result le_read8].
                 reflexivity.
              **** eapply eval_Etempvar.
                 simpl [le_read8_n le_read8_shift le_read8_t9 le_read8_ptr
                   le_read8_offset le_read8_edge le_read8_result le_read8].
                 reflexivity.
              **** cbn; reflexivity.
              +++ reflexivity.
              +++ apply exec_Sskip.
           ++ eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
              ** eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
              --- eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
                 ---- apply exec_set.
                 eapply eval_word.
                 ----- simpl [le_read8_n le_read8_shift le_read8_t9
                       le_read8_ptr le_read8_offset le_read8_edge
                       le_read8_result le_read8]; reflexivity.
                 ----- exact Hword.
                 ---- eapply call_read8_keep_early.
                 ----- simpl [le_read8_word le_read8_n le_read8_shift
                       le_read8_t9 le_read8_ptr le_read8_offset
                       le_read8_edge le_read8_result le_read8]; reflexivity.
                 ----- simpl [le_read8_word le_read8_n le_read8_shift
                       le_read8_t9 le_read8_ptr le_read8_offset
                       le_read8_edge le_read8_result le_read8]; reflexivity.
                 ----- simpl [le_read8_word le_read8_n le_read8_shift
                       le_read8_t9 le_read8_ptr le_read8_offset
                       le_read8_edge le_read8_result le_read8]; reflexivity.
                 ----- exact Hsym.
                 ----- exact Hfun.
                 ----- apply eval_LSBkeep8_value.
              --- apply exec_set.
                 exact Hresult.
           ** eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
              --- eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
                 ---- apply exec_set.
                     eapply eval_frame_offset.
                     ----- simpl [le_read8_keep le_read8_word le_read8_n
                           le_read8_shift le_read8_t9 le_read8_ptr
                           le_read8_offset le_read8_edge le_read8_result
                           le_read8]; reflexivity.
                     ----- exact Hoffset.
              ---- eapply exec_Sassign_value.
                     ----- apply eval_frame_offset_lvalue.
                         simpl [le_read8_t3 le_read8_result_final
                           le_read8_keep le_read8_word le_read8_n
                           le_read8_shift le_read8_t9 le_read8_ptr
                           le_read8_offset le_read8_edge le_read8_result
                           le_read8]; reflexivity.
                     ----- eapply eval_Ebinop.
                         ------ eapply eval_Etempvar.
                             simpl [le_read8_t3 le_read8_result_final
                               le_read8_keep le_read8_word le_read8_n
                               le_read8_shift le_read8_t9 le_read8_ptr
                               le_read8_offset le_read8_edge le_read8_result
                               le_read8]; reflexivity.
                         ------ eapply eval_Etempvar.
                             simpl [le_read8_t3 le_read8_result_final
                               le_read8_keep le_read8_word le_read8_n
                               le_read8_shift le_read8_t9 le_read8_ptr
                               le_read8_offset le_read8_edge le_read8_result
                               le_read8]; reflexivity.
                         ------ cbn; reflexivity.
                     ----- cbn; reflexivity.
                     ----- apply assign_frame_offset with
                           (le := le_read8_t3 bf bs w
                             (Int64.and w (Int64.repr 255))
                             (read8_result w)).
                         ------ simpl [le_read8_t3 le_read8_result_final
                               le_read8_keep le_read8_word le_read8_n
                               le_read8_shift le_read8_t9 le_read8_ptr
                               le_read8_offset le_read8_edge le_read8_result
                               le_read8]; reflexivity.
                         ------ exact Hstore.
           --- apply ClightBigstep.exec_Sreturn_some.
              eapply eval_Etempvar.
              simpl [le_read8_t3 le_read8_result_final le_read8_keep
                le_read8_word le_read8_n le_read8_shift le_read8_t9
                le_read8_ptr le_read8_offset le_read8_edge le_read8_result
                le_read8]. reflexivity.
Qed.

Lemma eval_read8_result : forall (m : mem) (bf bs : block) (w : int64),
  eval_expr ge0 empty_env
    (le_read8_keep bf bs w (Int64.and w (Int64.repr 255))) m
    read8_result_expr (Vint (read8_result w)).
Proof.
  intros m bf bs w.
  eapply eval_Ecast.
  - eapply eval_Ebinop with
      (v1 := Vint Int.zero)
      (v2 := Vint
        (Int.zero_ext 8
          (Int.repr
            (Int64.unsigned (Int64.and w (Int64.repr 255)))))).
    + eapply eval_Etempvar.
      simpl [le_read8_keep le_read8_word le_read8_n le_read8_shift
        le_read8_t9 le_read8_ptr le_read8_offset le_read8_edge
        le_read8_result le_read8]. reflexivity.
    + eapply eval_Ecast.
      * eapply eval_Etempvar.
        simpl [le_read8_keep le_read8_word le_read8_n le_read8_shift
          le_read8_t9 le_read8_ptr le_read8_offset le_read8_edge
          le_read8_result le_read8]. reflexivity.
      * cbn; reflexivity.
    + cbn; reflexivity.
  - cbn; reflexivity.
Qed.

Lemma eval_read8_body_fixed : forall (m m' : mem) (bf bs : block) (w : int64),
  Mem.load Mptr m bf 0 = Some (Vptr bs (Ptrofs.repr 8)) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr 56)) ->
  Mem.load Mint64 m bs 0 = Some (Vlong w) ->
  Mem.store Mint64 m bf 8 (Vlong (Int64.repr 64)) = Some m' ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBkeep = Some 72%positive ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr 72%positive Ptrofs.zero) =
    Some (Internal f_LSBkeep) ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env (le_read8 bf) m
    (fn_body f_simplicity_read8) E0
    (le_read8_t3 bf bs w (Int64.and w (Int64.repr 255))
      (read8_result w)) m'
    (Out_return (Some (Vint (read8_result w), tuchar))).
Proof.
  intros m m' bf bs w Hedge Hoffset Hword Hstore Hsym Hfun.
  eapply eval_read8_body; eauto.
  apply eval_read8_result.
Qed.

Lemma eval_read8 : forall (m m' : mem) (bf bs : block) (w : int64),
  Mem.load Mptr m bf 0 = Some (Vptr bs (Ptrofs.repr 8)) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr 56)) ->
  Mem.load Mint64 m bs 0 = Some (Vlong w) ->
  Mem.store Mint64 m bf 8 (Vlong (Int64.repr 64)) = Some m' ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBkeep = Some 72%positive ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr 72%positive Ptrofs.zero) =
    Some (Internal f_LSBkeep) ->
  ClightBigstep.Clight2.eval_funcall ge0 m
    (Internal f_simplicity_read8)
    (Vptr bf Ptrofs.zero :: nil) E0 m'
    (Vint (read8_result w)).
Proof.
  intros m m' bf bs w Hedge Hoffset Hword Hstore Hsym Hfun.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_read8 bf) (m1 := m)
         (le2 := le_read8_t3 bf bs w (Int64.and w (Int64.repr 255))
           (read8_result w)) (m2 := m')
         (out := Out_return (Some (Vint (read8_result w), tuchar)))
         (vres := Vint (read8_result w)).
  - apply entry_read8.
  - apply eval_read8_body_fixed; assumption.
  - cbn; split; [discriminate |].
    change (Some (Vint (Int.zero_ext 8 (read8_result w))) =
      Some (Vint (read8_result w))).
    unfold read8_result.
    rewrite Int.zero_ext_idem by lia.
    reflexivity.
  - simpl; reflexivity.
Qed.

Lemma eval_frame_edge_ofs : forall (m : mem) (le : temp_env)
    (bf bs : block) (ofs : ptrofs),
  le!_frame = Some (Vptr bf Ptrofs.zero) ->
  Mem.load Mptr m bf 0 = Some (Vptr bs ofs) ->
  eval_expr ge0 empty_env le m
    (Efield (Ederef (Etempvar _frame (tptr (Tstruct _frameItem noattr)))
       (Tstruct _frameItem noattr)) _edge (tptr tulong))
    (Vptr bs ofs).
Proof.
  intros m le bf bs ofs Hle Hload.
  eapply eval_Elvalue.
  - eapply eval_Efield_struct.
    + eapply eval_Elvalue.
      * eapply eval_Ederef.
        eapply eval_Etempvar; exact Hle.
      * apply deref_loc_copy.
        change (access_mode (Tstruct _frameItem noattr) = By_copy).
        reflexivity.
    + reflexivity.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
  - apply deref_loc_value with (chunk := Mptr).
    + vm_compute; reflexivity.
    + simpl [Mem.loadv]. exact Hload.
Qed.

Definition read8_keep_stmt : statement :=
  Scall (Some _t'2)
    (Evar _LSBkeep
      (Tfunction (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
    ((Ecast
       (Ebinop Oshr (Etempvar _t'4 tulong)
         (Ebinop Osub (Etempvar _frame_shift tulong)
           (Etempvar _n tulong) tulong) tulong) tulong) ::
     (Etempvar _n tulong) :: nil).

Lemma call_read8_keep : forall (le : temp_env) (m : mem)
    (w k : int64) (b : block),
  le!_t'4 = Some (Vlong w) ->
  le!_frame_shift = Some (Vlong (Int64.repr 8)) ->
  le!_n = Some (Vlong (Int64.repr 8)) ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBkeep = Some b ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr b Ptrofs.zero) =
    Some (Internal f_LSBkeep) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBkeep)
    (Vlong w :: Vlong (Int64.repr 8) :: nil) E0 m (Vlong k) ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env le m read8_keep_stmt
    E0 (PTree.set _t'2 (Vlong k) le) m Out_normal.
Proof.
  intros le m w k b Hword Hshift Hn Hsym Hfun Heval.
  change (ClightBigstep.exec_stmt function_entry2 ge0 empty_env le m
    read8_keep_stmt E0 (set_opttemp (Some _t'2) (Vlong k) le) m
    Out_normal).
  eapply ClightBigstep.exec_Scall
    with (vf := Vptr b Ptrofs.zero)
         (vargs := Vlong w :: Vlong (Int64.repr 8) :: nil)
         (f := Internal f_LSBkeep) (vres := Vlong k).
  - vm_compute; reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global.
      * simpl; reflexivity.
      * exact Hsym.
    + apply deref_loc_reference.
      change (access_mode
        (Tfunction (Tcons tulong (Tcons tulong Tnil)) tulong cc_default) =
        By_reference).
      reflexivity.
  - eapply eval_Econs.
    + eapply eval_Ecast with (v1 := Vlong w).
      * eapply eval_Ebinop with (v1 := Vlong w)
          (v2 := Vlong Int64.zero).
        -- apply eval_Etempvar; exact Hword.
        -- eapply eval_Ebinop with (v1 := Vlong (Int64.repr 8))
             (v2 := Vlong (Int64.repr 8)).
           ++ apply eval_Etempvar; exact Hshift.
           ++ apply eval_Etempvar; exact Hn.
           ++ reflexivity.
        -- change (Some (Vlong (Int64.shru w Int64.zero)) =
             Some (Vlong w)).
           rewrite Int64.shru_zero; reflexivity.
      * reflexivity.
    + reflexivity.
    + eapply eval_Econs.
      * eapply eval_Etempvar; exact Hn.
      * reflexivity.
      * apply eval_Enil.
  - exact Hfun.
  - vm_compute; reflexivity.
  - exact Heval.
Qed.
