(** Generalized execution infrastructure for [simplicity_write8].

    The one8 proof fixes the byte argument to one.  This file starts the
    input-dependent version without changing that checked proof: the byte is
    kept as an explicit [int] value at function entry. *)

From Coq Require Import ZArith List PArith.BinPos.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.

Require Import C.jet_exec.
Require Import C.jets.

Import Clightdefs Clightdefs.ClightNotations.
Import Values Mem Ctypes.
Import Events.

Local Open Scope Z_scope.
Local Open Scope clight_scope.

Definition le_write8_x (bf : block) (x : int) : temp_env :=
  PTree.set _x (Vint x)
    (PTree.set _frame (Vptr bf Ptrofs.zero)
       (create_undef_temps f_simplicity_write8.(fn_temps))).

Lemma entry_write8_x : forall (m : mem) (bf : block) (x : int),
  function_entry2 ge0 f_simplicity_write8
    (Vptr bf Ptrofs.zero :: Vint x :: nil) m
    empty_env (le_write8_x bf x) m.
Proof.
  intros m bf x.
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

Definition le_LSBclear8 (w : int64) : temp_env :=
  PTree.set _n (Vlong (Int64.repr 8))
    (PTree.set _x (Vlong w) (PTree.empty val)).

Definition le_LSBkeep8 (w : int64) : temp_env :=
  le_LSBclear8 w.

Lemma entry_LSBclear8_value : forall (m : mem) (w : int64),
  function_entry2 ge0 f_LSBclear
    (Vlong w :: Vlong (Int64.repr 8) :: nil) m
    empty_env (le_LSBclear8 w) m.
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

Lemma entry_LSBkeep8_value : forall (m : mem) (w : int64),
  function_entry2 ge0 f_LSBkeep
    (Vlong w :: Vlong (Int64.repr 8) :: nil) m
    empty_env (le_LSBkeep8 w) m.
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

Ltac eval_LSBclear8_value :=
  first [ eapply eval_Ecast; [ eval_LSBclear8_value | cbn; reflexivity ]
        | eapply eval_Ebinop;
            [ eval_LSBclear8_value | eval_LSBclear8_value | cbn; reflexivity ]
        | eapply eval_Etempvar; simpl [le_LSBclear8]; reflexivity
        | (cbn; vm_compute; reflexivity) ].

Lemma eval_LSBclear8_n_minus_one : forall (m : mem) (w : int64),
  eval_expr ge0 empty_env (le_LSBclear8 w) m
    (Ebinop Osub (Etempvar _n tulong)
      (Econst_int (Int.repr 1) tint) tulong)
    (Vlong (Int64.repr 7)).
Proof.
  intros m w.
  eapply eval_Ebinop.
  - eapply eval_Etempvar.
    simpl [le_LSBclear8].
    reflexivity.
  - apply eval_Econst_int.
  - cbn; vm_compute; reflexivity.
Qed.

Lemma eval_LSBclear8_value : forall (m : mem) (w : int64),
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBclear)
    (Vlong w :: Vlong (Int64.repr 8) :: nil) E0 m
    (Vlong (Int64.shl (Int64.shl
      (Int64.shru (Int64.shru w (Int64.repr 1)) (Int64.repr 7))
      (Int64.repr 1)) (Int64.repr 7))).
Proof.
  intros m w.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_LSBclear8 w) (m1 := m)
         (le2 := le_LSBclear8 w) (m2 := m).
  - change (function_entry2 ge0 f_LSBclear
      (Vlong w :: Vlong (Int64.repr 8) :: nil) m
      empty_env (le_LSBclear8 w) m).
    apply entry_LSBclear8_value.
  - simpl [f_LSBclear].
    apply ClightBigstep.exec_Sreturn_some.
    pose proof (eval_LSBclear8_n_minus_one m w) as Hn.
    eapply eval_Ecast.
    + eapply eval_Ebinop.
      * eapply eval_Ebinop.
        -- eapply eval_Ebinop.
           ++ eapply eval_Ebinop.
              --- eapply eval_Etempvar.
                  simpl [le_LSBclear8].
                  reflexivity.
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

Lemma eval_write8_x_cast : forall (m : mem) (bf : block) (x : int),
  eval_expr ge0 empty_env (le_write8_x bf x) m
    (Ecast (Etempvar _x tuchar) tulong)
    (Vlong (Int64.repr (Int.unsigned x))).
Proof.
  intros m bf x.
  eapply eval_Ecast.
  - eapply eval_Etempvar.
    simpl [le_write8_x].
    reflexivity.
  - cbn; reflexivity.
Qed.

Ltac eval_closed_mask :=
  lazymatch goal with
  | |- eval_expr _ _ _ _ (Ecast _ _) _ =>
      eapply eval_Ecast;
      [ eval_closed_mask | cbn; vm_compute; reflexivity ]
  | |- eval_expr _ _ _ _ (Eunop _ _ _) _ =>
      eapply eval_Eunop;
      [ eval_closed_mask | cbn; vm_compute; reflexivity ]
  | |- eval_expr _ _ _ _ (Ebinop _ _ _ _) _ =>
      eapply eval_Ebinop;
      [ eval_closed_mask | eval_closed_mask | cbn; vm_compute; reflexivity ]
  | |- eval_expr _ _ _ _ (Etempvar _ _) _ =>
      eapply eval_Etempvar;
      simpl [le_LSBkeep8 le_LSBclear8]; reflexivity
  | |- eval_expr _ _ _ _ (Econst_int _ _) _ => apply eval_Econst_int
  end.

Lemma eval_LSBkeep8_value : forall (m : mem) (w : int64),
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBkeep)
    (Vlong w :: Vlong (Int64.repr 8) :: nil) E0 m
    (Vlong (Int64.and w (Int64.repr 255))).
Proof.
  intros m w.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_LSBkeep8 w) (m1 := m)
         (le2 := le_LSBkeep8 w) (m2 := m).
  - apply entry_LSBkeep8_value.
  - simpl [f_LSBkeep].
    apply ClightBigstep.exec_Sreturn_some.
    eapply eval_Ecast.
    + eapply eval_Ebinop.
      * eapply eval_Etempvar.
        simpl [le_LSBkeep8 le_LSBclear8].
        reflexivity.
      * eval_closed_mask.
      * cbn; reflexivity.
    + cbn; reflexivity.
  - cbn; split; [discriminate | reflexivity].
  - simpl; reflexivity.
Qed.

Lemma call_LSBkeep8_x : forall (le : temp_env) (m : mem)
    (x : int) (k : int64) (b : block),
  le!_x = Some (Vint x) ->
  le!_n = Some (Vlong (Int64.repr 8)) ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBkeep = Some b ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr b Ptrofs.zero) =
    Some (Internal f_LSBkeep) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBkeep)
    (Vlong (Int64.repr (Int.unsigned x)) ::
     Vlong (Int64.repr 8) :: nil) E0 m (Vlong k) ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env le m
    (Scall (Some _t'4)
      (Evar _LSBkeep (Tfunction
        (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
      ((Ecast (Etempvar _x tuchar) tulong) ::
       (Etempvar _n tulong) :: nil))
    E0 (PTree.set _t'4 (Vlong k) le) m Out_normal.
Proof.
  intros le m x k b Hx Hn Hsym Hfun Heval.
  change (ClightBigstep.exec_stmt function_entry2 ge0 empty_env le m
    (Scall (Some _t'4)
      (Evar _LSBkeep (Tfunction
        (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
      ((Ecast (Etempvar _x tuchar) tulong) ::
       (Etempvar _n tulong) :: nil))
    E0 (set_opttemp (Some _t'4) (Vlong k) le) m Out_normal).
  eapply ClightBigstep.exec_Scall
    with (vf := Vptr b Ptrofs.zero)
         (vargs := Vlong (Int64.repr (Int.unsigned x)) ::
                   Vlong (Int64.repr 8) :: nil)
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
  - exact Heval.
Qed.

Definition le_w8_x_0 (bf : block) (x : int) : temp_env :=
  le_write8_x bf x.
Definition le_w8_x_1 (bf bw : block) (x : int) : temp_env :=
  PTree.set _t'11 (Vptr bw Ptrofs.zero) (le_w8_x_0 bf x).
Definition le_w8_x_2 (bf bw : block) (x : int) : temp_env :=
  PTree.set _t'12 (Vlong (Int64.repr 8)) (le_w8_x_1 bf bw x).
Definition le_w8_x_3 (bf bw : block) (x : int) : temp_env :=
  PTree.set _frame_ptr (Vptr bw Ptrofs.zero) (le_w8_x_2 bf bw x).
Definition le_w8_x_4 (bf bw : block) (x : int) : temp_env :=
  PTree.set _t'10 (Vlong (Int64.repr 8)) (le_w8_x_3 bf bw x).
Definition le_w8_x_5 (bf bw : block) (x : int) : temp_env :=
  PTree.set _frame_shift (Vlong (Int64.repr 8)) (le_w8_x_4 bf bw x).
Definition le_w8_x_6 (bf bw : block) (x : int) : temp_env :=
  PTree.set _n (Vlong (Int64.repr 8)) (le_w8_x_5 bf bw x).
Definition le_w8_x_7 (bf bw : block) (x : int) (w : int64) : temp_env :=
  PTree.set _t'6 (Vlong w) (le_w8_x_6 bf bw x).
Definition le_w8_x_8 (bf bw : block) (x : int) (w c : int64) : temp_env :=
  PTree.set _t'3 (Vlong c) (le_w8_x_7 bf bw x w).
Definition le_w8_x_9 (bf bw : block) (x : int) (w c k : int64) : temp_env :=
  PTree.set _t'4 (Vlong k) (le_w8_x_8 bf bw x w c).
Definition le_w8_x_final (bf bw : block) (x : int)
    (w c k : int64) : temp_env :=
  PTree.set _t'5 (Vlong (Int64.repr 8)) (le_w8_x_9 bf bw x w c k).

Ltac eval_w8_x :=
  first [ (eapply eval_frame_edge; [ simpl; reflexivity | eassumption ])
        | (eapply eval_frame_offset; [ simpl; reflexivity | eassumption ])
        | (eapply eval_word; [ simpl; reflexivity | eassumption ])
        | (eapply eval_Etempvar;
           simpl [le_w8_x_final le_w8_x_9 le_w8_x_8 le_w8_x_7
             le_w8_x_6 le_w8_x_5 le_w8_x_4 le_w8_x_3 le_w8_x_2
             le_w8_x_1 le_w8_x_0 le_write8_x]; reflexivity)
        | (eapply eval_Ecast; [ eval_w8_x | cbn; reflexivity ])
        | (eapply eval_Eunop; [ eval_w8_x | cbn; reflexivity ])
        | (eapply eval_Ebinop;
           [ eval_w8_x | eval_w8_x | cbn; reflexivity ])
        | apply eval_Econst_int
        | constructor
        | (cbn; vm_compute; reflexivity) ].

Lemma write8_body_x : forall (m : mem) (bf bw : block) (x : int)
    (w c k q : int64) (m1 m2 : mem),
  Mem.load Mptr m bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr 8)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong w) ->
  Mem.store Mint64 m bw 0 (Vlong q) = Some m1 ->
  Mem.load Mint64 m1 bf 8 = Some (Vlong (Int64.repr 8)) ->
  Mem.store Mint64 m1 bf 8 (Vlong (Int64.repr 0)) = Some m2 ->
  q = Int64.or c (Int64.shl k
        (Int64.sub (Int64.repr 8) (Int64.repr 8))) ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBclear = Some block_LSBclear ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr block_LSBclear Ptrofs.zero) =
    Some (Internal f_LSBclear) ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBkeep = Some block_LSBkeep ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr block_LSBkeep Ptrofs.zero) =
    Some (Internal f_LSBkeep) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBclear)
    (Vlong w :: Vlong (Int64.repr 8) :: nil) E0 m (Vlong c) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBkeep)
    (Vlong (Int64.repr (Int.unsigned x)) ::
     Vlong (Int64.repr 8) :: nil) E0 m (Vlong k) ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env (le_w8_x_0 bf x) m
    (fn_body f_simplicity_write8) E0
    (le_w8_x_final bf bw x w c k) m2 Out_normal.
Proof.
  intros m bf bw x w c k q m1 m2 H_edge H_offset H_word H_store_word
    H_offset1 H_store_offset Hq Hsym_clear Hfun_clear Hsym_keep Hfun_keep
    Hclear Hkeep.
  unfold f_simplicity_write8; cbn.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + apply exec_set; eval_w8_x.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_set; eval_w8_x.
      * apply exec_set; eval_w8_x.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_set; eval_w8_x.
      * apply exec_set; eval_w8_x.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_set; eval_w8_x.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
           ++ eval_w8_x.
           ++ reflexivity.
           ++ apply exec_Sskip.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
              ** eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
                 --- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
                     +++ apply exec_set; eval_w8_x.
                     +++ eapply call_LSBclear8.
                         *** simpl [le_w8_x_7]; reflexivity.
                         *** simpl [le_w8_x_6]; reflexivity.
                         *** exact Hsym_clear.
                         *** exact Hfun_clear.
                         *** exact Hclear.
              --- eapply call_LSBkeep8_x.
                  +++ simpl [le_w8_x_8]; reflexivity.
                  +++ simpl [le_w8_x_8]; reflexivity.
                  +++ exact Hsym_keep.
                  +++ exact Hfun_keep.
                  +++ exact Hkeep.
              ** eapply exec_Sassign_value.
                 --- apply eval_word_lvalue.
                     simpl [le_w8_x_9]; reflexivity.
                 --- eapply eval_Ecast.
                     +++ eapply eval_Ebinop.
                         { eapply eval_Etempvar; simpl [le_w8_x_9]; reflexivity. }
                         { eapply eval_Ebinop.
                           { eapply eval_Etempvar; simpl [le_w8_x_9]; reflexivity. }
                           { eapply eval_Ebinop.
                             { eapply eval_Etempvar; simpl [le_w8_x_9]; reflexivity. }
                             { eapply eval_Etempvar; simpl [le_w8_x_9]; reflexivity. }
                             { cbn; reflexivity. } }
                           { cbn; reflexivity. } }
                         { cbn; reflexivity. }
                     +++ cbn; reflexivity.
                 --- cbn; reflexivity.
                 --- apply assign_word with (le := le_w8_x_9 bf bw x w c k).
                     +++ simpl [le_w8_x_9 le_w8_x_8 le_w8_x_7 le_w8_x_6
                           le_w8_x_5 le_w8_x_4 le_w8_x_3 le_w8_x_2
                           le_w8_x_1 le_w8_x_0 le_write8_x]; reflexivity.
                     +++ match goal with
                         | |- Mem.store Mint64 ?mm ?bb ?ofs
                               (Vlong (Int64.or c
                                 (Int64.shl k
                                   (Int64.sub ?shift ?n)))) = Some ?mm' =>
                             assert (Hs : shift = Int64.repr 8) by
                               (timeout 10 (vm_compute; reflexivity));
                             assert (Hn : n = Int64.repr 8) by
                               (timeout 10 (vm_compute; reflexivity));
                             rewrite Hs, Hn, <- Hq; exact H_store_word
                         end.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
              ** apply exec_set.
                 eapply eval_frame_offset.
                 { simpl [le_w8_x_8]; reflexivity. }
                 { exact H_offset1. }
              ** eapply exec_Sassign_value.
                 --- apply eval_frame_offset_lvalue.
                     simpl [le_w8_x_final]; reflexivity.
                 --- eapply eval_Ebinop.
                     +++ eapply eval_Etempvar; simpl [le_w8_x_final]; reflexivity.
                     +++ eapply eval_Etempvar; simpl [le_w8_x_final]; reflexivity.
                     +++ cbn; reflexivity.
                 --- cbn; reflexivity.
                 --- apply assign_frame_offset with
                       (le := le_w8_x_final bf bw x w c k).
                     +++ simpl [le_w8_x_final]; reflexivity.
                     +++ exact H_store_offset.
Qed.

Lemma eval_write8_x : forall (m : mem) (bf bw : block) (x : int)
    (w c k q : int64) (m1 m2 : mem),
  Mem.load Mptr m bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr 8)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong w) ->
  Mem.store Mint64 m bw 0 (Vlong q) = Some m1 ->
  Mem.load Mint64 m1 bf 8 = Some (Vlong (Int64.repr 8)) ->
  Mem.store Mint64 m1 bf 8 (Vlong (Int64.repr 0)) = Some m2 ->
  q = Int64.or c
        (Int64.shl k
          (Int64.sub (Int64.repr 8) (Int64.repr 8))) ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBclear = Some block_LSBclear ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr block_LSBclear Ptrofs.zero) =
    Some (Internal f_LSBclear) ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBkeep = Some block_LSBkeep ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr block_LSBkeep Ptrofs.zero) =
    Some (Internal f_LSBkeep) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBclear)
    (Vlong w :: Vlong (Int64.repr 8) :: nil) E0 m (Vlong c) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBkeep)
    (Vlong (Int64.repr (Int.unsigned x)) ::
     Vlong (Int64.repr 8) :: nil) E0 m (Vlong k) ->
  ClightBigstep.Clight2.eval_funcall ge0 m
    (Internal f_simplicity_write8)
    (Vptr bf Ptrofs.zero :: Vint x :: nil)
    E0 m2 Vundef.
Proof.
  intros m bf bw x w c k q m1 m2 H_edge H_offset H_word H_store_word
    H_offset1 H_store_offset Hq Hsym_clear Hfun_clear Hsym_keep Hfun_keep
    Hclear Hkeep.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_write8_x bf x) (m1 := m)
         (le2 := le_w8_x_final bf bw x w c k) (m2 := m2)
         (out := Out_normal) (vres := Vundef).
  - apply entry_write8_x.
  - eapply write8_body_x; eauto.
  - cbn; reflexivity.
  - simpl; reflexivity.
Qed.
