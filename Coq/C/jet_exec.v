(*
   Direct Clight execution lemmas for the generated jet AST.

   This file deliberately uses CompCert's big-step Clight2 semantics rather
   than VST: the public jet functions take frameItem by value, so their
   normalized bodies contain a genuine struct-copy assignment.
*)

From Coq Require Import ZArith List PArith.BinPos.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.

(* The generated file is compiled as the top-level [jets] library by the
   direct, standalone command documented in the handoff. *)
Require Import C.jets.

Import Clightdefs Clightdefs.ClightNotations.
Import Values Mem Ctypes.
Import Events.

Local Open Scope Z_scope.
Local Open Scope clight_scope.

Section DIRECT_CLIGHT.

Variable ge : genv.

Lemma exec_Sassign_copy
      (e : env) (le : temp_env) (m m' : mem)
      (a1 a2 : expr) (b b' : block) (ofs ofs' : ptrofs)
      (v : val)
      (Hlv : eval_lvalue ge e le m a1 b ofs Full)
      (Hev : eval_expr ge e le m a2 (Vptr b' ofs'))
      (Hcast : sem_cast (Vptr b' ofs') (typeof a2) (typeof a1) m = Some v)
      (Hassign : assign_loc ge (typeof a1) m b ofs Full v m') :
  ClightBigstep.Clight2.exec_stmt ge e le m (Sassign a1 a2)
    E0 le m' Out_normal.
Proof.
  econstructor; eauto.
Qed.



Lemma assign_frameItem_copy
      (m m' : mem) (dst src : block) (src_ofs dst_ofs : ptrofs)
      (bytes : list memval)
      (Hmode : access_mode (Tstruct _frameItem noattr) = By_copy)
      (Hsrc_align : sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr) > 0 ->
                    (alignof_blockcopy prog.(prog_comp_env) (Tstruct _frameItem noattr) |
                       Ptrofs.unsigned src_ofs))
      (Hdst_align : sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr) > 0 ->
                    (alignof_blockcopy prog.(prog_comp_env) (Tstruct _frameItem noattr) |
                       Ptrofs.unsigned dst_ofs))
      (Hdisjoint : dst <> src \/
                   Ptrofs.unsigned src_ofs = Ptrofs.unsigned dst_ofs \/
                   Ptrofs.unsigned src_ofs + sizeof prog.(prog_comp_env)
                     (Tstruct _frameItem noattr) <= Ptrofs.unsigned dst_ofs \/
                   Ptrofs.unsigned dst_ofs + sizeof prog.(prog_comp_env)
                     (Tstruct _frameItem noattr) <= Ptrofs.unsigned src_ofs)
      (Hload : Mem.loadbytes m src (Ptrofs.unsigned src_ofs)
                 (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr)) = Some bytes)
      (Hstore : Mem.storebytes m dst (Ptrofs.unsigned dst_ofs) bytes = Some m') :
  assign_loc prog.(prog_comp_env) (Tstruct _frameItem noattr) m dst dst_ofs Full
    (Vptr src src_ofs) m'.
Proof.
  eapply assign_loc_copy with (b' := src) (ofs' := src_ofs)
    (bytes := bytes) (m' := m'); eauto.
  destruct Hdisjoint as [Hneq | Hdisjoint].
  - left; congruence.
  - right; exact Hdisjoint.
Qed.

End DIRECT_CLIGHT.

Definition ge0 : genv := Clight.globalenv prog.

Lemma eval_frame_edge : forall (m : mem) (le : temp_env) (bf bw : block),
  le!_frame = Some (Vptr bf Ptrofs.zero) ->
  Mem.load Mptr m bf 0 = Some (Vptr bw Ptrofs.zero) ->
  eval_expr ge0 empty_env le m
    (Efield (Ederef (Etempvar _frame (tptr (Tstruct _frameItem noattr)))
       (Tstruct _frameItem noattr)) _edge (tptr tulong))
    (Vptr bw Ptrofs.zero).
Proof.
  intros m le bf bw Hle Hload.
  eapply eval_Elvalue.
  { eapply eval_Efield_struct.
    { eapply eval_Elvalue.
      { eapply eval_Ederef.
        eapply eval_Etempvar; exact Hle. }
      { apply deref_loc_copy.
        change (access_mode (Tstruct _frameItem noattr) = By_copy).
        reflexivity. } }
    { reflexivity. }
    { vm_compute; reflexivity. }
    { vm_compute; reflexivity. } }
  { apply deref_loc_value with (chunk := Mptr).
    { vm_compute; reflexivity. }
    { simpl [Mem.loadv]. exact Hload. } }
Qed.

Lemma eval_frame_offset : forall (m : mem) (le : temp_env) (bf : block) (n : int64),
  le!_frame = Some (Vptr bf Ptrofs.zero) ->
  Mem.load Mint64 m bf 8 = Some (Vlong n) ->
  eval_expr ge0 empty_env le m
    (Efield (Ederef (Etempvar _frame (tptr (Tstruct _frameItem noattr)))
       (Tstruct _frameItem noattr)) _offset tulong)
    (Vlong n).
Proof.
  intros m le bf n Hle Hload.
  eapply eval_Elvalue.
  { eapply eval_Efield_struct.
    { eapply eval_Elvalue.
      { eapply eval_Ederef.
        eapply eval_Etempvar; exact Hle. }
      { apply deref_loc_copy.
        change (access_mode (Tstruct _frameItem noattr) = By_copy).
        reflexivity. } }
    { reflexivity. }
    { vm_compute; reflexivity. }
    { vm_compute; reflexivity. } }
  { apply deref_loc_value with (chunk := Mint64).
    { vm_compute; reflexivity. }
    { simpl [Mem.loadv]. exact Hload. } }
Qed.

Lemma eval_frame_offset_lvalue : forall (m : mem) (le : temp_env) (bf : block),
  le!_frame = Some (Vptr bf Ptrofs.zero) ->
  eval_lvalue ge0 empty_env le m
    (Efield (Ederef (Etempvar _frame (tptr (Tstruct _frameItem noattr)))
       (Tstruct _frameItem noattr)) _offset tulong)
    bf (Ptrofs.add Ptrofs.zero (Ptrofs.repr 8)) Full.
Proof.
  intros m le bf Hle.
  eapply eval_Efield_struct.
  - eapply eval_Elvalue.
    + eapply eval_Ederef.
      eapply eval_Etempvar; exact Hle.
    + apply deref_loc_copy.
      change (access_mode (Tstruct _frameItem noattr) = By_copy).
      reflexivity.
  - reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Lemma assign_frame_offset : forall (m m' : mem) (le : temp_env) (bf : block)
    (n : int64),
  le!_frame = Some (Vptr bf Ptrofs.zero) ->
  Mem.store Mint64 m bf 8 (Vlong n) = Some m' ->
  assign_loc (prog_comp_env prog) tulong m bf
    (Ptrofs.add Ptrofs.zero (Ptrofs.repr 8)) Full
    (Vlong n) m'.
Proof.
  intros m m' le bf n Hle Hstore.
  apply assign_loc_value with (chunk := Mint64).
  - reflexivity.
  - simpl [Mem.storev]. exact Hstore.
Qed.

Lemma eval_word_lvalue : forall (m : mem) (le : temp_env) (bw : block),
  le!_frame_ptr = Some (Vptr bw Ptrofs.zero) ->
  eval_lvalue ge0 empty_env le m
    (Ederef (Etempvar _frame_ptr (tptr tulong)) tulong)
    bw Ptrofs.zero Full.
Proof.
  intros m le bw Hle.
  eapply eval_Ederef.
  eapply eval_Etempvar; exact Hle.
Qed.

Lemma assign_word : forall (m m' : mem) (le : temp_env) (bw : block) (v : int64),
  le!_frame_ptr = Some (Vptr bw Ptrofs.zero) ->
  Mem.store Mint64 m bw 0 (Vlong v) = Some m' ->
  assign_loc (prog_comp_env prog) tulong m bw Ptrofs.zero Full
    (Vlong v) m'.
Proof.
  intros m m' le bw v Hle Hstore.
  apply assign_loc_value with (chunk := Mint64).
  - reflexivity.
  - simpl [Mem.storev]. exact Hstore.
Qed.

Lemma eval_word : forall (m : mem) (le : temp_env) (bw : block) (v : int64),
  le!_frame_ptr = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bw 0 = Some (Vlong v) ->
  eval_expr ge0 empty_env le m
    (Ederef (Etempvar _frame_ptr (tptr tulong)) tulong)
    (Vlong v).
Proof.
  intros m le bw v Hle Hload.
  eapply eval_Elvalue.
  - eapply eval_Ederef.
    eapply eval_Etempvar; exact Hle.
  - apply deref_loc_value with (chunk := Mint64).
    { reflexivity. }
    { simpl [Mem.loadv]; exact Hload. }
Qed.


Definition le_keep : temp_env :=
  PTree.set _n (Vlong (Int64.repr 8))
    (PTree.set _x (Vlong (Int64.repr 1)) (PTree.empty val)).

Lemma keep_entry : forall (m : mem),
  function_entry2 ge0 f_LSBkeep
    (Vlong (Int64.repr 1) :: Vlong (Int64.repr 8) :: nil) m
    empty_env le_keep m.
Proof.
  intros m.
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
    tauto.
  - constructor.
  - reflexivity.
Qed.

Ltac pure_keep_eval :=
  first [ eapply eval_Ecast; [ pure_keep_eval | cbn; reflexivity ]
        | eapply eval_Eunop; [ pure_keep_eval | cbn; reflexivity ]
        | eapply eval_Ebinop;
            [ pure_keep_eval | pure_keep_eval | cbn; reflexivity ]
        | eapply eval_Etempvar; simpl [le_keep]; reflexivity
        | constructor
        | (cbn; reflexivity) ].


Section CALLS.
Variable ge : genv.
Lemma call_LSBclear8 : forall (le : temp_env) (m : mem)
    (w c : int64) (b : block),
  le!_t'6 = Some (Vlong w) ->
  le!_frame_shift = Some (Vlong (Int64.repr 8)) ->
  Genv.find_symbol (Clight.genv_genv ge) _LSBclear = Some b ->
  Genv.find_funct (Clight.genv_genv ge) (Vptr b Ptrofs.zero) =
    Some (Internal f_LSBclear) ->
  ClightBigstep.Clight2.eval_funcall ge m (Internal f_LSBclear)
    (Vlong w :: Vlong (Int64.repr 8) :: nil) E0 m (Vlong c) ->
  ClightBigstep.Clight2.exec_stmt ge empty_env le m
    (Scall (Some _t'3)
      (Evar _LSBclear (Tfunction (Tcons tulong (Tcons tulong Tnil))
                         tulong cc_default))
      ((Etempvar _t'6 tulong) :: (Etempvar _frame_shift tulong) :: nil))
    E0 (PTree.set _t'3 (Vlong c) le) m Out_normal.
Proof.
  intros le m w c b Hw Hshift Hsym Hfun Heval.
  change (ClightBigstep.exec_stmt function_entry2 ge empty_env le m
    (Scall (Some _t'3)
      (Evar _LSBclear (Tfunction (Tcons tulong (Tcons tulong Tnil))
                         tulong cc_default))
      ((Etempvar _t'6 tulong) :: (Etempvar _frame_shift tulong) :: nil))
    E0 (set_opttemp (Some _t'3) (Vlong c) le) m Out_normal).
  eapply ClightBigstep.exec_Scall
    with (vf := Vptr b Ptrofs.zero)
         (vargs := Vlong w :: Vlong (Int64.repr 8) :: nil)
         (f := Internal f_LSBclear) (vres := Vlong c).
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
    + eapply eval_Etempvar; exact Hw.
    + reflexivity.
    + eapply eval_Econs.
      * eapply eval_Etempvar; exact Hshift.
      * reflexivity.
      * apply eval_Enil.
  - exact Hfun.
  - vm_compute; reflexivity.
  - exact Heval.
Qed.


End CALLS.

Definition le_write8 (bf : block) : temp_env :=
  PTree.set _x (Vint (Int.repr 1))
    (PTree.set _frame (Vptr bf Ptrofs.zero)
       (create_undef_temps f_simplicity_write8.(fn_temps))).

Lemma exec_set : forall (ge : genv) (e : env) (le : temp_env) (m : mem)
    (id : ident) (a : expr) (v : val),
  eval_expr ge e le m a v ->
  ClightBigstep.Clight2.exec_stmt ge e le m (Sset id a)
    E0 (PTree.set id v le) m Out_normal.
Proof.
  intros; constructor; assumption.
Qed.

Lemma exec_Sassign_value
      (ge : genv) (e : env) (le : temp_env) (m m' : mem)
      (a1 a2 : expr) (b : block) (ofs : ptrofs)
      (v2 v : val)
      (Hlv : eval_lvalue ge e le m a1 b ofs Full)
      (Hev : eval_expr ge e le m a2 v2)
      (Hcast : sem_cast v2 (typeof a2) (typeof a1) m = Some v)
      (Hassign : assign_loc (Clight.genv_cenv ge) (typeof a1) m b ofs Full v m') :
  ClightBigstep.Clight2.exec_stmt ge e le m (Sassign a1 a2)
    E0 le m' Out_normal.
Proof.
  econstructor; eauto.
Qed.

Lemma eval_LSBkeep8 : forall (m : mem),
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBkeep)
    (Vlong (Int64.repr 1) :: Vlong (Int64.repr 8) :: nil)
    E0 m (Vlong (Int64.repr 1)).
Proof.
  intros m.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_keep) (m1 := m)
         (le2 := le_keep) (m2 := m).
  - apply keep_entry.
  - simpl [f_LSBkeep].
    apply ClightBigstep.exec_Sreturn_some.
    eapply eval_Ecast.
    pure_keep_eval.
    vm_compute; reflexivity.
  - cbn; split; [discriminate | reflexivity].
  - simpl; reflexivity.
Qed.

Lemma call_LSBkeep8 : forall (le : temp_env) (m : mem)
    (b : block),
  le!_x = Some (Vint (Int.repr 1)) ->
  le!_n = Some (Vlong (Int64.repr 8)) ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBkeep = Some b ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr b Ptrofs.zero) =
    Some (Internal f_LSBkeep) ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env le m
    (Scall (Some _t'4)
      (Evar _LSBkeep (Tfunction
        (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
      ((Ecast (Etempvar _x tuchar) tulong) ::
       (Etempvar _n tulong) :: nil))
    E0 (PTree.set _t'4 (Vlong (Int64.repr 1)) le) m Out_normal.
Proof.
  intros le m b Hx Hn Hsym Hfun.
  change (ClightBigstep.exec_stmt function_entry2 ge0 empty_env le m
    (Scall (Some _t'4)
      (Evar _LSBkeep (Tfunction
        (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
      ((Ecast (Etempvar _x tuchar) tulong) ::
       (Etempvar _n tulong) :: nil))
    E0 (set_opttemp (Some _t'4) (Vlong (Int64.repr 1)) le) m Out_normal).
  eapply ClightBigstep.exec_Scall
    with (vf := Vptr b Ptrofs.zero)
         (vargs := Vlong (Int64.repr 1) :: Vlong (Int64.repr 8) :: nil)
         (f := Internal f_LSBkeep) (vres := Vlong (Int64.repr 1)).
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
    + eapply eval_Ecast.
      * eapply eval_Etempvar; exact Hx.
      * cbn; reflexivity.
    + reflexivity.
    + eapply eval_Econs.
      * eapply eval_Etempvar; exact Hn.
      * reflexivity.
      * apply eval_Enil.
  - exact Hfun.
  - vm_compute; reflexivity.
  - apply eval_LSBkeep8.
Qed.
Definition le_w8_0 (bf : block) : temp_env := le_write8 bf.
Definition le_w8_1 (bf bw : block) : temp_env :=
  PTree.set _t'11 (Vptr bw Ptrofs.zero) (le_w8_0 bf).
Definition le_w8_2 (bf bw : block) : temp_env :=
  PTree.set _t'12 (Vlong (Int64.repr 8)) (le_w8_1 bf bw).
Definition le_w8_3 (bf bw : block) : temp_env :=
  PTree.set _frame_ptr (Vptr bw Ptrofs.zero) (le_w8_2 bf bw).
Definition le_w8_4 (bf bw : block) : temp_env :=
  PTree.set _t'10 (Vlong (Int64.repr 8)) (le_w8_3 bf bw).
Definition le_w8_5 (bf bw : block) : temp_env :=
  PTree.set _frame_shift (Vlong (Int64.repr 8)) (le_w8_4 bf bw).
Definition le_w8_6 (bf bw : block) : temp_env :=
  PTree.set _n (Vlong (Int64.repr 8)) (le_w8_5 bf bw).

Definition le_w8_7 (bf bw : block) (w : int64) : temp_env :=
  PTree.set _t'6 (Vlong w) (le_w8_6 bf bw).
Definition le_w8_8 (bf bw : block) (w c : int64) : temp_env :=
  PTree.set _t'3 (Vlong c) (le_w8_7 bf bw w).
Definition le_w8_9 (bf bw : block) (w c : int64) : temp_env :=
  PTree.set _t'4 (Vlong (Int64.repr 1)) (le_w8_8 bf bw w c).
Definition le_w8_final (bf bw : block) (w c : int64) : temp_env :=
  PTree.set _t'5 (Vlong (Int64.repr 8)) (le_w8_9 bf bw w c).

Ltac eval_w8 :=
  first [ (eapply eval_frame_edge; [ simpl; reflexivity | eassumption ])
        | (eapply eval_frame_offset; [ simpl; reflexivity | eassumption ])
        | (eapply eval_word; [ simpl; reflexivity | eassumption ])
        | (eapply eval_Etempvar; simpl [le_write8]; reflexivity)
        | (eapply eval_Ecast; [ eval_w8 | cbn; reflexivity ])
        | (eapply eval_Eunop; [ eval_w8 | cbn; reflexivity ])
        | (eapply eval_Ebinop; [ eval_w8 | eval_w8 | cbn; reflexivity ])
        | constructor
        | (cbn; vm_compute; reflexivity) ].

Lemma write8_prefix_probe : forall (m : mem) (bf bw : block)
  (w c q : int64) (m1 m2 : mem),
  Mem.load Mptr m bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr 8)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong w) ->
  Mem.store Mint64 m bw 0 (Vlong q) = Some m1 ->
  Mem.load Mint64 m1 bf 8 = Some (Vlong (Int64.repr 8)) ->
  Mem.store Mint64 m1 bf 8 (Vlong (Int64.repr 0)) = Some m2 ->
  q = Int64.or c
        (Int64.shl (Int64.repr 1)
          (Int64.sub (Int64.repr 8) (Int64.repr 8))) ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBclear = Some 71%positive ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr 71%positive Ptrofs.zero) =
    Some (Internal f_LSBclear) ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBkeep = Some 72%positive ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr 72%positive Ptrofs.zero) =
    Some (Internal f_LSBkeep) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBclear)
    (Vlong w :: Vlong (Int64.repr 8) :: nil) E0 m (Vlong c) ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env (le_w8_0 bf) m
    (fn_body f_simplicity_write8) E0 (le_w8_final bf bw w c) m2
    Out_normal.
Proof.
  intros m bf bw w c q m1 m2 H_edge H_offset H_word H_store_word H_offset1
    H_store_offset Hq Hsym_clear Hfun_clear Hsym_keep Hfun_keep Hclear.
  unfold f_simplicity_write8; cbn.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + apply exec_set; eval_w8.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_set; eval_w8.
      * apply exec_set; eval_w8.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_set; eval_w8.
      * apply exec_set; eval_w8.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_set; eval_w8.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
           ++ eval_w8.
           ++ reflexivity.
           ++ apply exec_Sskip.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
              ** eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
                 --- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
                     +++ apply exec_set; eval_w8.
                     +++ eapply call_LSBclear8.
                         *** simpl [le_w8_7]; reflexivity.
                         *** simpl [le_w8_6]; reflexivity.
                         *** exact Hsym_clear.
                         *** exact Hfun_clear.
                         *** exact Hclear.
              --- eapply call_LSBkeep8.
                  +++ simpl [le_w8_8]; reflexivity.
                  +++ simpl [le_w8_8]; reflexivity.
                  +++ exact Hsym_keep.
                  +++ exact Hfun_keep.
           ** eapply exec_Sassign_value.
              *** apply eval_word_lvalue.
                 simpl [le_w8_9]; reflexivity.
              *** eapply eval_Ecast.
                 --- eapply eval_Ebinop.
                     { eapply eval_Etempvar; simpl [le_w8_9]; reflexivity. }
                     { eapply eval_Ebinop.
                       { eapply eval_Etempvar; simpl [le_w8_9]; reflexivity. }
                       { eapply eval_Ebinop.
                         { eapply eval_Etempvar; simpl [le_w8_9]; reflexivity. }
                         { eapply eval_Etempvar; simpl [le_w8_9]; reflexivity. }
                         { cbn; reflexivity. } }
                       { cbn; reflexivity. } }
                     { cbn; reflexivity. }
                 --- cbn; reflexivity.
              *** cbn; reflexivity.
              *** apply assign_word with (le := le_w8_9 bf bw w c).
                 --- simpl [le_w8_9 le_w8_8 le_w8_7 le_w8_6 le_w8_5 le_w8_4 le_w8_3 le_w8_2 le_w8_1 le_w8_0 le_write8]; reflexivity.
                 --- match goal with
                     | |- Mem.store Mint64 ?mm ?bb ?ofs
                           (Vlong (Int64.or c
                             (Int64.shl (Int64.repr 1)
                               (Int64.sub ?shift ?n)))) = Some ?mm' =>
                         assert (Hs : shift = Int64.repr 8) by
                           (vm_compute; reflexivity);
                         assert (Hn : n = Int64.repr 8) by
                           (vm_compute; reflexivity);
                         rewrite Hs, Hn, <- Hq; exact H_store_word
                     end.
    ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      ** apply exec_set.
        eapply eval_frame_offset.
        { simpl [le_w8_8]; reflexivity. }
        { exact H_offset1. }
      ** eapply exec_Sassign_value.
        *** apply eval_frame_offset_lvalue.
           simpl [le_w8_final]; reflexivity.
        *** eapply eval_Ebinop.
           --- eapply eval_Etempvar; simpl [le_w8_final]; reflexivity.
           --- eapply eval_Etempvar; simpl [le_w8_final]; reflexivity.
           --- cbn; reflexivity.
        *** cbn; reflexivity.
        *** apply assign_frame_offset with (le := le_w8_final bf bw w c).
           --- simpl [le_w8_final]; reflexivity.
           --- exact H_store_offset.

Qed.

Lemma entry_write8 : forall (m : mem) (bf : block),
  function_entry2 ge0 f_simplicity_write8
    (Vptr bf Ptrofs.zero :: Vint (Int.repr 1) :: nil) m
    empty_env (le_write8 bf) m.
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

Lemma symbol_LSBclear :
  Genv.find_symbol (Clight.genv_genv ge0) _LSBclear = Some 71%positive.
Proof. vm_compute; reflexivity. Qed.

Lemma funct_LSBclear :
  Genv.find_funct (Clight.genv_genv ge0) (Vptr 71%positive Ptrofs.zero) =
    Some (Internal f_LSBclear).
Proof.
  change (Some (Internal f_LSBclear) = Some (Internal f_LSBclear)).
  reflexivity.
Qed.

Lemma symbol_LSBkeep :
  Genv.find_symbol (Clight.genv_genv ge0) _LSBkeep = Some 72%positive.
Proof. vm_compute; reflexivity. Qed.

Lemma funct_LSBkeep :
  Genv.find_funct (Clight.genv_genv ge0) (Vptr 72%positive Ptrofs.zero) =
    Some (Internal f_LSBkeep).
Proof.
  change (Some (Internal f_LSBkeep) = Some (Internal f_LSBkeep)).
  reflexivity.
Qed.

Lemma eval_write8 : forall (m : mem) (bf bw : block)
    (w c q : int64) (m1 m2 : mem),
  Mem.load Mptr m bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr 8)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong w) ->
  Mem.store Mint64 m bw 0 (Vlong q) = Some m1 ->
  Mem.load Mint64 m1 bf 8 = Some (Vlong (Int64.repr 8)) ->
  Mem.store Mint64 m1 bf 8 (Vlong (Int64.repr 0)) = Some m2 ->
  q = Int64.or c
        (Int64.shl (Int64.repr 1)
          (Int64.sub (Int64.repr 8) (Int64.repr 8))) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBclear)
    (Vlong w :: Vlong (Int64.repr 8) :: nil) E0 m (Vlong c) ->
  ClightBigstep.Clight2.eval_funcall ge0 m
    (Internal f_simplicity_write8)
    (Vptr bf Ptrofs.zero :: Vint (Int.repr 1) :: nil)
    E0 m2 Vundef.
Proof.
  intros m bf bw w c q m1 m2 H_edge H_offset H_word H_store_word H_offset1
    H_store_offset Hq Hclear.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_write8 bf) (m1 := m)
         (le2 := le_w8_final bf bw w c) (m2 := m2)
         (out := Out_normal) (vres := Vundef).
  - apply entry_write8.
  - eapply write8_prefix_probe; eauto using
      symbol_LSBclear, funct_LSBclear, symbol_LSBkeep, funct_LSBkeep.
  - cbn; reflexivity.
  - simpl; reflexivity.
Qed.
