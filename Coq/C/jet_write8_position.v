(** Generated write8 execution for a byte contained in one backing word. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_write8 C.jets C.jet_frame_arith
  C.jet_frame_constants C.jet_LSBclear_width C.jet_word_bits.
Import Clightdefs Clightdefs.ClightNotations Values Mem Ctypes Events.
Local Open Scope Z_scope.
Local Open Scope clight_scope.
Local Transparent Archi.ptr64.

Lemma call_LSBclear_width : forall (le : temp_env) (m : mem)
    (w c : int64) (n : Z) (b : block),
  le!_t'6 = Some (Vlong w) ->
  le!_frame_shift = Some (Vlong (Int64.repr n)) ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBclear = Some b ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr b Ptrofs.zero) =
    Some (Internal f_LSBclear) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBclear)
    (Vlong w :: Vlong (Int64.repr n) :: nil) E0 m (Vlong c) ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env le m
    (Scall (Some _t'3)
      (Evar _LSBclear (Tfunction (Tcons tulong (Tcons tulong Tnil))
                         tulong cc_default))
      ((Etempvar _t'6 tulong) :: (Etempvar _frame_shift tulong) :: nil))
    E0 (PTree.set _t'3 (Vlong c) le) m Out_normal.
Proof.
  intros le m w c n b Hw Hshift Hsym Hfun Heval.
  change (ClightBigstep.exec_stmt function_entry2 ge0 empty_env le m
    (Scall (Some _t'3)
      (Evar _LSBclear (Tfunction (Tcons tulong (Tcons tulong Tnil))
                         tulong cc_default))
      ((Etempvar _t'6 tulong) :: (Etempvar _frame_shift tulong) :: nil))
    E0 (set_opttemp (Some _t'3) (Vlong c) le) m Out_normal).
  eapply ClightBigstep.exec_Scall
    with (vf := Vptr b Ptrofs.zero)
         (vargs := Vlong w :: Vlong (Int64.repr n) :: nil)
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

Section Position.
Variable cursor : Z.
Hypothesis Hcursor : 8 <= cursor <= 64.

Definition le_w8_pos_0 (bf : block) (x : int) : temp_env :=
  le_write8_x bf x.
Definition le_w8_pos_1 (bf bw : block) (x : int) : temp_env :=
  PTree.set _t'11 (Vptr bw Ptrofs.zero) (le_w8_pos_0 bf x).
Definition le_w8_pos_2 (bf bw : block) (x : int) : temp_env :=
  PTree.set _t'12 (Vlong (Int64.repr cursor)) (le_w8_pos_1 bf bw x).
Definition le_w8_pos_3 (bf bw : block) (x : int) : temp_env :=
  PTree.set _frame_ptr (Vptr bw Ptrofs.zero) (le_w8_pos_2 bf bw x).
Definition le_w8_pos_4 (bf bw : block) (x : int) : temp_env :=
  PTree.set _t'10 (Vlong (Int64.repr cursor)) (le_w8_pos_3 bf bw x).
Definition le_w8_pos_5 (bf bw : block) (x : int) : temp_env :=
  PTree.set _frame_shift (Vlong (Int64.repr cursor)) (le_w8_pos_4 bf bw x).
Definition le_w8_pos_6 (bf bw : block) (x : int) : temp_env :=
  PTree.set _n (Vlong (Int64.repr 8)) (le_w8_pos_5 bf bw x).
Definition le_w8_pos_7 (bf bw : block) (x : int) (w : int64) : temp_env :=
  PTree.set _t'6 (Vlong w) (le_w8_pos_6 bf bw x).
Definition le_w8_pos_8 (bf bw : block) (x : int) (w c : int64) : temp_env :=
  PTree.set _t'3 (Vlong c) (le_w8_pos_7 bf bw x w).
Definition le_w8_pos_9 (bf bw : block) (x : int) (w c k : int64) : temp_env :=
  PTree.set _t'4 (Vlong k) (le_w8_pos_8 bf bw x w c).
Definition le_w8_pos_final (bf bw : block) (x : int)
    (w c k : int64) : temp_env :=
  PTree.set _t'5 (Vlong (Int64.repr cursor)) (le_w8_pos_9 bf bw x w c k).

Ltac pos_scalar :=
  change (Int.signed (Int.repr 8)) with 8;
  change (Int.signed (Int.repr 1)) with 1;
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu
    Int64.modu Int64.ltu Int64.shl Int64.or];
  unfold sem_binarith, sem_cast;
  change Archi.ptr64 with true;
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu
    Int64.modu Int64.ltu Int64.shl Int64.or];
  repeat first [
    rewrite cursor_word_index by lia
  | rewrite cursor_word_shift by lia
  | rewrite cursor_no_cross by lia ];
  change (Int.signed (Int.repr 8)) with 8;
  try match goal with H : Int64.ltu _ Int64.iwordsize = true |- _ => rewrite H end;
  reflexivity.

Ltac eval_w8_pos :=
  first [ solve [apply eval_generated_uword_bits]
        | (eapply eval_frame_edge; [ simpl; reflexivity | eassumption ])
        | (eapply eval_frame_offset; [ simpl; reflexivity | eassumption ])
        | (eapply eval_word; [ simpl; reflexivity | eassumption ])
        | (eapply eval_Etempvar;
           cbn [le_w8_pos_final le_w8_pos_9 le_w8_pos_8 le_w8_pos_7
             le_w8_pos_6 le_w8_pos_5 le_w8_pos_4 le_w8_pos_3 le_w8_pos_2
             le_w8_pos_1 le_w8_pos_0 le_write8_x]; reflexivity)
        | (eapply eval_Ecast; [ eval_w8_pos | pos_scalar ])
        | (eapply eval_Eunop; [ eval_w8_pos | pos_scalar ])
        | (eapply eval_Ebinop;
           [ eval_w8_pos | eval_w8_pos | pos_scalar ])
        | apply eval_Econst_int
        | apply eval_Econst_long ].

Lemma write8_body_position : forall (m : mem) (bf bw : block) (x : int)
    (w c k q : int64) (m1 m2 : mem),
  Mem.load Mptr m bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr cursor)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong w) ->
  Mem.store Mint64 m bw 0 (Vlong q) = Some m1 ->
  Mem.load Mint64 m1 bf 8 = Some (Vlong (Int64.repr cursor)) ->
  Mem.store Mint64 m1 bf 8 (Vlong (Int64.repr (cursor - 8))) = Some m2 ->
  q = Int64.or c (Int64.shl k
        (Int64.sub (Int64.repr cursor) (Int64.repr 8))) ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBclear = Some 71%positive ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr 71%positive Ptrofs.zero) =
    Some (Internal f_LSBclear) ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBkeep = Some 72%positive ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr 72%positive Ptrofs.zero) =
    Some (Internal f_LSBkeep) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBclear)
    (Vlong w :: Vlong (Int64.repr cursor) :: nil) E0 m (Vlong c) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBkeep)
    (Vlong (Int64.repr (Int.unsigned x)) ::
     Vlong (Int64.repr 8) :: nil) E0 m (Vlong k) ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env (le_w8_pos_0 bf x) m
    (fn_body f_simplicity_write8) E0
    (le_w8_pos_final bf bw x w c k) m2 Out_normal.
Proof.
  intros m bf bw x w c k q m1 m2 H_edge H_offset H_word H_store_word
    H_offset1 H_store_offset Hq Hsym_clear Hfun_clear Hsym_keep Hfun_keep
    Hclear Hkeep.
  assert (Hshift : Int64.ltu
    (Int64.sub (Int64.repr cursor) (Int64.repr 8)) Int64.iwordsize = true).
  { rewrite cursor_sub by lia.
    unfold Int64.ltu. change Int64.iwordsize with (Int64.repr 64).
    rewrite !cursor_unsigned by lia. rewrite zlt_true by lia. reflexivity. }
  unfold f_simplicity_write8; cbn [fn_body].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + apply exec_set; eval_w8_pos.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_set; eval_w8_pos.
      * apply exec_set; eval_w8_pos.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_set; eval_w8_pos.
      * apply exec_set; eval_w8_pos.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_set; eval_w8_pos.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
           ++ eapply eval_Ebinop; [eval_w8_pos | eval_w8_pos |].
              pos_scalar.
           ++ reflexivity.
           ++ apply exec_Sskip.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
              ** eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
                 --- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
                     +++ apply exec_set; eval_w8_pos.
                     +++ eapply call_LSBclear_width.
                         *** cbn [le_w8_pos_7]; reflexivity.
                         *** cbn [le_w8_pos_6]; reflexivity.
                         *** exact Hsym_clear.
                         *** exact Hfun_clear.
                         *** exact Hclear.
              --- eapply call_LSBkeep8_x.
                  +++ cbn [le_w8_pos_8]; reflexivity.
                  +++ cbn [le_w8_pos_8]; reflexivity.
                  +++ exact Hsym_keep.
                  +++ exact Hfun_keep.
                  +++ exact Hkeep.
              ** eapply exec_Sassign_value.
                 --- apply eval_word_lvalue.
                     cbn [le_w8_pos_9]; reflexivity.
                 --- eapply eval_Ecast.
                     +++ eapply eval_Ebinop.
                         { eapply eval_Etempvar; cbn [le_w8_pos_9]; reflexivity. }
                         { eapply eval_Ebinop.
                           { eapply eval_Etempvar; cbn [le_w8_pos_9]; reflexivity. }
                           { eapply eval_Ebinop.
                             { eapply eval_Etempvar; cbn [le_w8_pos_9]; reflexivity. }
                             { eapply eval_Etempvar; cbn [le_w8_pos_9]; reflexivity. }
                             { pos_scalar. } }
                           { pos_scalar. } }
                         { pos_scalar. }
                     +++ pos_scalar.
                 --- pos_scalar.
                 --- apply assign_word with (le := le_w8_pos_9 bf bw x w c k).
                     +++ cbn [le_w8_pos_9 le_w8_pos_8 le_w8_pos_7 le_w8_pos_6
                           le_w8_pos_5 le_w8_pos_4 le_w8_pos_3 le_w8_pos_2
                           le_w8_pos_1 le_w8_pos_0 le_write8_x]; reflexivity.
                     +++ rewrite <- Hq; exact H_store_word.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
              ** apply exec_set.
                 eapply eval_frame_offset.
                 { cbn [le_w8_pos_8]; reflexivity. }
                 { exact H_offset1. }
              ** eapply exec_Sassign_value.
                 --- apply eval_frame_offset_lvalue.
                     cbn [le_w8_pos_final]; reflexivity.
                 --- eapply eval_Ebinop.
                     +++ eapply eval_Etempvar; cbn [le_w8_pos_final]; reflexivity.
                     +++ eapply eval_Etempvar; cbn [le_w8_pos_final]; reflexivity.
                     +++ pos_scalar.
                 --- pos_scalar.
                 --- apply assign_frame_offset with
                       (le := le_w8_pos_final bf bw x w c k).
                     +++ cbn [le_w8_pos_final]; reflexivity.
                     +++ rewrite cursor_sub by lia; exact H_store_offset.
Qed.

Lemma eval_write8_position_raw : forall (m : mem) (bf bw : block) (x : int)
    (w c k q : int64) (m1 m2 : mem),
  Mem.load Mptr m bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr cursor)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong w) ->
  Mem.store Mint64 m bw 0 (Vlong q) = Some m1 ->
  Mem.load Mint64 m1 bf 8 = Some (Vlong (Int64.repr cursor)) ->
  Mem.store Mint64 m1 bf 8 (Vlong (Int64.repr (cursor - 8))) = Some m2 ->
  q = Int64.or c
        (Int64.shl k
          (Int64.sub (Int64.repr cursor) (Int64.repr 8))) ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBclear = Some 71%positive ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr 71%positive Ptrofs.zero) =
    Some (Internal f_LSBclear) ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBkeep = Some 72%positive ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr 72%positive Ptrofs.zero) =
    Some (Internal f_LSBkeep) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBclear)
    (Vlong w :: Vlong (Int64.repr cursor) :: nil) E0 m (Vlong c) ->
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
         (le2 := le_w8_pos_final bf bw x w c k) (m2 := m2)
         (out := Out_normal) (vres := Vundef).
  - apply entry_write8_x.
  - eapply write8_body_position; eauto.
  - pos_scalar.
  - simpl; reflexivity.
Qed.

End Position.

(** No helper execution assumptions remain in this exported call rule. *)
Definition put_byte (cursor : Z) (old payload : int64) : int64 :=
  Int64.or (clear_low cursor old)
    (Int64.shl (Int64.zero_ext 8 payload) (Int64.repr (cursor - 8))).

Lemma eval_write8_position m mw mf bd bw cursor old x :
  8 <= cursor <= 64 ->
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr cursor)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong old) ->
  Mem.store Mint64 m bw 0
    (Vlong (put_byte cursor old (Int64.repr (Int.unsigned x)))) = Some mw ->
  Mem.store Mint64 mw bd 8 (Vlong (Int64.repr (cursor - 8))) = Some mf ->
  bd <> bw ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
    (Vptr bd Ptrofs.zero :: Vint x :: nil) E0 mf Vundef.
Proof.
  intros Hcursor HE HO HW SW SF Hneq.
  eapply eval_write8_position_raw with (w := old) (c := clear_low cursor old)
    (k := Int64.zero_ext 8 (Int64.repr (Int.unsigned x))) (m1 := mw).
  - exact Hcursor.
  - exact HE.
  - exact HO.
  - exact HW.
  - exact SW.
  - rewrite <- HO. eapply Mem.load_store_other; [exact SW | auto].
  - exact SF.
  - unfold put_byte. rewrite cursor_sub by lia. reflexivity.
  - apply symbol_LSBclear.
  - apply funct_LSBclear.
  - apply symbol_LSBkeep.
  - apply funct_LSBkeep.
  - apply eval_clear_width; lia.
  - rewrite Int64.zero_ext_and by lia. apply eval_LSBkeep8_value.
Qed.
