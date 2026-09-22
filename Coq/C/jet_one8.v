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

Definition e_one8 (bs : block) : env :=
  PTree.set _src (bs, Tstruct _frameItem noattr) empty_env.

Definition le_one8 (bd bs : block) (ofs : ptrofs) : temp_env :=
  PTree.set _dst (Vptr bd Ptrofs.zero)
    (PTree.set _src (Vptr bs ofs)
      (PTree.set _env Vundef (PTree.empty val))).

Lemma free_list_singleton : forall (m m' : mem) (b : block) (lo hi : Z),
    Mem.free_list m ((b, lo, hi) :: nil) = Some m' ->
    Mem.free m b lo hi = Some m'.
Proof.
  intros m m' b lo hi H.
  cbn in H.
  destruct (Mem.free m b lo hi) eqn:Hfree.
  - simpl in H.
    congruence.
  - discriminate.
Qed.

Lemma entry_one8_gen : forall (m m1 : mem) (bl bd bs : block)
    (ofs : ptrofs)
    (Halloc : Mem.alloc m 0 16 = (m1, bl)),
  function_entry2 ge0 f_simplicity_one_8
    (Vptr bd Ptrofs.zero :: Vptr bs ofs :: Vundef :: nil) m
    (e_one8 bl) (le_one8 bd bs ofs) m1.
Proof.
  intros m m1 bl bd bs ofs Halloc.
  constructor.
  - change (list_norepet (_src :: nil)).
    repeat constructor; simpl; tauto.
  - change (list_norepet (_dst :: _src :: _env :: nil)).
    unfold _dst, _src, _env.
    repeat constructor; simpl; intuition discriminate.
  - change (list_disjoint (_dst :: _src :: _env :: nil) nil).
    intros x y Hx Hy; contradiction.
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bl).
    + change (Mem.alloc m 0 16 = (m1, bl)). exact Halloc.
    + constructor.
  - simpl [le_one8]. reflexivity.
Qed.

Lemma exec_one8_copy : forall (m m' : mem) (bl bd bs : block)
    (ofs : ptrofs) (bytes : list memval),
    (access_mode (Tstruct _frameItem noattr) = By_copy) ->
    (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr) > 0 ->
      (alignof_blockcopy prog.(prog_comp_env) (Tstruct _frameItem noattr) |
        Ptrofs.unsigned ofs)) ->
    (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr) > 0 ->
      (alignof_blockcopy prog.(prog_comp_env) (Tstruct _frameItem noattr) |
        Ptrofs.unsigned Ptrofs.zero)) ->
    bl <> bs \/
      Ptrofs.unsigned ofs = Ptrofs.unsigned Ptrofs.zero \/
      Ptrofs.unsigned ofs + sizeof prog.(prog_comp_env)
        (Tstruct _frameItem noattr) <= Ptrofs.unsigned Ptrofs.zero \/
      Ptrofs.unsigned Ptrofs.zero + sizeof prog.(prog_comp_env)
        (Tstruct _frameItem noattr) <= Ptrofs.unsigned ofs ->
    Mem.loadbytes m bs (Ptrofs.unsigned ofs)
      (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr)) = Some bytes ->
    Mem.storebytes m bl 0 bytes = Some m' ->
    ClightBigstep.Clight2.exec_stmt ge0 (e_one8 bl)
      (le_one8 bd bs ofs) m
      (Sassign (Evar _src (Tstruct _frameItem noattr))
        (Etempvar _src (Tstruct _frameItem noattr)))
      E0 (le_one8 bd bs ofs) m' Out_normal.
Proof.
  intros m m' bl bd bs ofs bytes Hmode Hsrc_align Hdst_align Hdisjoint
    Hload Hstore.
  eapply exec_Sassign_copy.
  - eapply eval_Evar_local.
    simpl [e_one8]. reflexivity.
  - eapply eval_Etempvar.
    simpl [le_one8]. reflexivity.
  - cbn; reflexivity.
  - eapply assign_frameItem_copy; eauto.
Qed.

Lemma symbol_write8 :
  Genv.find_symbol (Clight.genv_genv ge0) _simplicity_write8 = Some block_write8.
Proof. vm_compute; reflexivity. Qed.

Lemma funct_write8 :
  Genv.find_funct (Clight.genv_genv ge0) (Vptr block_write8 Ptrofs.zero) =
    Some (Internal f_simplicity_write8).
Proof.
  change (Some (Internal f_simplicity_write8) = Some (Internal f_simplicity_write8)).
  reflexivity.
Qed.

Definition le_clear0 : temp_env :=
  PTree.set _n (Vlong (Int64.repr 8))
    (PTree.set _x (Vlong Int64.zero) (PTree.empty val)).

Lemma clear_entry : forall (m : mem),
  function_entry2 ge0 f_LSBclear
    (Vlong Int64.zero :: Vlong (Int64.repr 8) :: nil) m
    empty_env le_clear0 m.
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
  - intros id1 id2 H1 H2 Heq; simpl in H1, H2; tauto.
  - constructor.
  - reflexivity.
Qed.

Ltac pure_clear_eval :=
  first [ eapply eval_Ecast; [ pure_clear_eval | cbn; reflexivity ]
        | eapply eval_Eunop; [ pure_clear_eval | cbn; reflexivity ]
        | eapply eval_Ebinop;
            [ pure_clear_eval | pure_clear_eval | cbn; reflexivity ]
        | eapply eval_Etempvar; simpl [le_clear0]; reflexivity
        | constructor
        | (cbn; vm_compute; reflexivity) ].

Lemma eval_LSBclear_zero : forall (m : mem),
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBclear)
    (Vlong Int64.zero :: Vlong (Int64.repr 8) :: nil)
    E0 m (Vlong Int64.zero).
Proof.
  intros m.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_clear0) (m1 := m)
         (le2 := le_clear0) (m2 := m).
  - apply clear_entry.
  - simpl [f_LSBclear].
    apply ClightBigstep.exec_Sreturn_some.
    eapply eval_Ecast.
    pure_clear_eval.
    all: cbn; vm_compute; reflexivity.
  - cbn; split; [discriminate | reflexivity].
  - simpl; reflexivity.
Qed.

Lemma call_write8_one : forall (e : env) (le : temp_env) (m m' : mem) (bd b : block),
  e!_simplicity_write8 = None ->
  le!_dst = Some (Vptr bd Ptrofs.zero) ->
  Genv.find_symbol (Clight.genv_genv ge0) _simplicity_write8 = Some b ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr b Ptrofs.zero) =
    Some (Internal f_simplicity_write8) ->
  ClightBigstep.Clight2.eval_funcall ge0 m
    (Internal f_simplicity_write8)
    (Vptr bd Ptrofs.zero :: Vint (Int.repr 1) :: nil)
    E0 m' Vundef ->
  ClightBigstep.Clight2.exec_stmt ge0 e le m
    (Scall None
      (Evar _simplicity_write8
        (Tfunction (Tcons (tptr (Tstruct _frameItem noattr))
          (Tcons tuchar Tnil)) tvoid cc_default))
      ((Etempvar _dst (tptr (Tstruct _frameItem noattr))) ::
       (Econst_int (Int.repr 1) tint) :: nil))
    E0 le m' Out_normal.
Proof.
  intros e le m m' bd b Hen Hdst Hsym Hfun Heval.
  change (ClightBigstep.exec_stmt function_entry2 ge0 e le m
    (Scall None
      (Evar _simplicity_write8
        (Tfunction (Tcons (tptr (Tstruct _frameItem noattr))
          (Tcons tuchar Tnil)) tvoid cc_default))
      ((Etempvar _dst (tptr (Tstruct _frameItem noattr))) ::
       (Econst_int (Int.repr 1) tint) :: nil))
    E0 (set_opttemp None Vundef le) m' Out_normal).
  eapply ClightBigstep.exec_Scall
    with (vf := Vptr b Ptrofs.zero)
         (vargs := Vptr bd Ptrofs.zero :: Vint (Int.repr 1) :: nil)
         (f := Internal f_simplicity_write8) (vres := Vundef).
  - vm_compute; reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global.
      * exact Hen.
      * exact Hsym.
    + apply deref_loc_reference.
      change (access_mode
        (Tfunction (Tcons (tptr (Tstruct _frameItem noattr))
          (Tcons tuchar Tnil)) tvoid cc_default) = By_reference).
      reflexivity.
  - eapply eval_Econs.
    + eapply eval_Etempvar; exact Hdst.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Econst_int.
      * cbn; reflexivity.
      * apply eval_Enil.
  - exact Hfun.
  - vm_compute; reflexivity.
  - exact Heval.
Qed.

Lemma exec_one8_body : forall (m1 m2 m3 : mem) (bl bd bs : block)
    (ofs : ptrofs) (bytes : list memval),
    (access_mode (Tstruct _frameItem noattr) = By_copy) ->
    (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr) > 0 ->
      (alignof_blockcopy prog.(prog_comp_env) (Tstruct _frameItem noattr) |
        Ptrofs.unsigned ofs)) ->
    (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr) > 0 ->
      (alignof_blockcopy prog.(prog_comp_env) (Tstruct _frameItem noattr) |
        Ptrofs.unsigned Ptrofs.zero)) ->
    bl <> bs \/
      Ptrofs.unsigned ofs = Ptrofs.unsigned Ptrofs.zero \/
      Ptrofs.unsigned ofs + sizeof prog.(prog_comp_env)
        (Tstruct _frameItem noattr) <= Ptrofs.unsigned Ptrofs.zero \/
      Ptrofs.unsigned Ptrofs.zero + sizeof prog.(prog_comp_env)
        (Tstruct _frameItem noattr) <= Ptrofs.unsigned ofs ->
    Mem.loadbytes m1 bs (Ptrofs.unsigned ofs)
      (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr)) = Some bytes ->
    Mem.storebytes m1 bl 0 bytes = Some m2 ->
    ClightBigstep.Clight2.eval_funcall ge0 m2
      (Internal f_simplicity_write8)
      (Vptr bd Ptrofs.zero :: Vint (Int.repr 1) :: nil)
      E0 m3 Vundef ->
    ClightBigstep.Clight2.exec_stmt ge0 (e_one8 bl)
      (le_one8 bd bs ofs) m1 (fn_body f_simplicity_one_8)
      E0 (le_one8 bd bs ofs) m3
      (Out_return (Some (Vint (Int.repr 1), tint))).
Proof.
  intros m1 m2 m3 bl bd bs ofs bytes Hmode Hsrc_align Hdst_align
    Hdisjoint Hload Hstore Hwrite.
  unfold f_simplicity_one_8; cbn.
  eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - eapply exec_one8_copy; eauto.
  - eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply call_write8_one; eauto.
      simpl [le_one8]; reflexivity.
      apply symbol_write8.
      apply funct_write8.
    + apply ClightBigstep.exec_Sreturn_some.
      apply eval_Econst_int.
Qed.

Lemma eval_one8 : forall (m m1 m2 m3 m4 : mem)
    (bl bd bs : block) (ofs : ptrofs) (bytes : list memval),
    Mem.alloc m 0 16 = (m1, bl) ->
    (access_mode (Tstruct _frameItem noattr) = By_copy) ->
    (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr) > 0 ->
      (alignof_blockcopy prog.(prog_comp_env) (Tstruct _frameItem noattr) |
        Ptrofs.unsigned ofs)) ->
    (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr) > 0 ->
      (alignof_blockcopy prog.(prog_comp_env) (Tstruct _frameItem noattr) |
        Ptrofs.unsigned Ptrofs.zero)) ->
    bl <> bs \/
      Ptrofs.unsigned ofs = Ptrofs.unsigned Ptrofs.zero \/
      Ptrofs.unsigned ofs + sizeof prog.(prog_comp_env)
        (Tstruct _frameItem noattr) <= Ptrofs.unsigned Ptrofs.zero \/
      Ptrofs.unsigned Ptrofs.zero + sizeof prog.(prog_comp_env)
        (Tstruct _frameItem noattr) <= Ptrofs.unsigned ofs ->
    Mem.loadbytes m1 bs (Ptrofs.unsigned ofs)
      (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr)) = Some bytes ->
    Mem.storebytes m1 bl 0 bytes = Some m2 ->
    ClightBigstep.Clight2.eval_funcall ge0 m2
      (Internal f_simplicity_write8)
      (Vptr bd Ptrofs.zero :: Vint (Int.repr 1) :: nil)
      E0 m3 Vundef ->
    Mem.free_list m3 (blocks_of_env ge0 (e_one8 bl)) = Some m4 ->
    ClightBigstep.Clight2.eval_funcall ge0 m
      (Internal f_simplicity_one_8)
      (Vptr bd Ptrofs.zero :: Vptr bs ofs :: Vundef :: nil)
      E0 m4 (Vint (Int.repr 1)).
Proof.
  intros m m1 m2 m3 m4 bl bd bs ofs bytes Halloc Hmode Hsrc_align
    Hdst_align Hdisjoint Hload Hstore Hwrite Hfree.
  eapply ClightBigstep.eval_funcall_internal
    with (e := e_one8 bl) (le1 := le_one8 bd bs ofs) (m1 := m1)
         (le2 := le_one8 bd bs ofs) (m2 := m3)
         (out := Out_return (Some (Vint (Int.repr 1), tint)))
         (vres := Vint (Int.repr 1)) (m3 := m4).
  - apply entry_one8_gen; exact Halloc.
  - apply exec_one8_body with (m2 := m2) (bytes := bytes); assumption.
  - cbn; split; [discriminate | reflexivity].
  - exact Hfree.
Qed.

Lemma eval_one8_zero : forall (m m1 m2 mw m3 m4 : mem)
    (bl bd bw bs : block) (ofs : ptrofs) (bytes : list memval),
    Mem.alloc m 0 16 = (m1, bl) ->
    (access_mode (Tstruct _frameItem noattr) = By_copy) ->
    (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr) > 0 ->
      (alignof_blockcopy prog.(prog_comp_env) (Tstruct _frameItem noattr) |
        Ptrofs.unsigned ofs)) ->
    (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr) > 0 ->
      (alignof_blockcopy prog.(prog_comp_env) (Tstruct _frameItem noattr) |
        Ptrofs.unsigned Ptrofs.zero)) ->
    bl <> bs \/
      Ptrofs.unsigned ofs = Ptrofs.unsigned Ptrofs.zero \/
      Ptrofs.unsigned ofs + sizeof prog.(prog_comp_env)
        (Tstruct _frameItem noattr) <= Ptrofs.unsigned Ptrofs.zero \/
      Ptrofs.unsigned Ptrofs.zero + sizeof prog.(prog_comp_env)
        (Tstruct _frameItem noattr) <= Ptrofs.unsigned ofs ->
    Mem.loadbytes m1 bs (Ptrofs.unsigned ofs)
      (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr)) = Some bytes ->
    Mem.storebytes m1 bl 0 bytes = Some m2 ->
    Mem.load Mptr m2 bd 0 = Some (Vptr bw Ptrofs.zero) ->
    Mem.load Mint64 m2 bd 8 = Some (Vlong (Int64.repr 8)) ->
    Mem.load Mint64 m2 bw 0 = Some (Vlong Int64.zero) ->
    Mem.store Mint64 m2 bw 0 (Vlong (Int64.repr 1)) = Some mw ->
    Mem.store Mint64 mw bd 8 (Vlong (Int64.repr 0)) = Some m3 ->
    bd <> bw ->
    bl <> bd ->
    bl <> bw ->
    Mem.free_list m3 (blocks_of_env ge0 (e_one8 bl)) = Some m4 ->
    Mem.load Mint64 m4 bw 0 = Some (Vlong (Int64.repr 1)) /\
    Mem.load Mint64 m4 bd 8 = Some (Vlong (Int64.repr 0)) /\
    ClightBigstep.Clight2.eval_funcall ge0 m
      (Internal f_simplicity_one_8)
      (Vptr bd Ptrofs.zero :: Vptr bs ofs :: Vundef :: nil)
      E0 m4 (Vint (Int.repr 1)).
Proof.
  intros m m1 m2 mw m3 m4 bl bd bw bs ofs bytes Halloc Hmode Hsrc_align
    Hdst_align Hdisjoint Hload Hstore Hedge Hoffset Hword Hstore_word
    Hstore_offset Hbdw Hblbd Hblbw Hfree.
  assert (Hoffset_mw : Mem.load Mint64 mw bd 8 =
      Some (Vlong (Int64.repr 8))).
  { rewrite <- Hoffset.
    eapply Mem.load_store_other with (chunk := Mint64) (b := bw) (ofs := 0).
    - exact Hstore_word.
    - left; exact Hbdw.
  }
  assert (Hwrite : ClightBigstep.Clight2.eval_funcall ge0 m2
      (Internal f_simplicity_write8)
      (Vptr bd Ptrofs.zero :: Vint (Int.repr 1) :: nil)
      E0 m3 Vundef).
  { eapply eval_write8 with (m := m2) (bf := bd) (bw := bw)
      (w := Int64.zero) (c := Int64.zero) (q := Int64.repr 1)
      (m1 := mw) (m2 := m3).
    - exact Hedge.
    - exact Hoffset.
    - exact Hword.
    - exact Hstore_word.
    - exact Hoffset_mw.
    - exact Hstore_offset.
    - vm_compute; reflexivity.
    - apply eval_LSBclear_zero.
  }
  assert (Hcall : ClightBigstep.Clight2.eval_funcall ge0 m
      (Internal f_simplicity_one_8)
      (Vptr bd Ptrofs.zero :: Vptr bs ofs :: Vundef :: nil)
      E0 m4 (Vint (Int.repr 1))).
  { apply eval_one8 with (m1 := m1) (m2 := m2) (m3 := m3)
      (m4 := m4) (bl := bl) (bd := bd) (bs := bs) (ofs := ofs)
      (bytes := bytes); assumption. }
  assert (Hfree_direct : Mem.free m3 bl 0
      (sizeof (Clight.genv_cenv ge0) (Tstruct _frameItem noattr)) = Some m4).
  { apply free_list_singleton.
    change (Mem.free_list m3
      ((bl, 0, sizeof (Clight.genv_cenv ge0) (Tstruct _frameItem noattr)) :: nil) =
    Some m4).
    exact Hfree. }
  split.
  - assert (Hword_m3 : Mem.load Mint64 m3 bw 0 =
        Some (Vlong (Int64.repr 1))).
    { assert (Hword_mw : Mem.load Mint64 mw bw 0 =
          Some (Vlong (Int64.repr 1))).
      { eapply Mem.load_store_same with (chunk := Mint64) in Hstore_word.
        exact Hstore_word. }
      assert (Hpres : Mem.load Mint64 m3 bw 0 =
          Mem.load Mint64 mw bw 0).
      { eapply Mem.load_store_other with (chunk := Mint64)
          (b := bd) (ofs := 8).
        - exact Hstore_offset.
        - left; congruence. }
      rewrite Hword_mw in Hpres; exact Hpres.
    }
    assert (Hfree_word : Mem.load Mint64 m4 bw 0 =
        Mem.load Mint64 m3 bw 0).
    { eapply Mem.load_free with (m1 := m3) (bf := bl) (lo := 0)
        (hi := sizeof (Clight.genv_cenv ge0) (Tstruct _frameItem noattr))
        (m2 := m4).
      - exact Hfree_direct.
      - left; congruence. }
    rewrite Hword_m3 in Hfree_word; exact Hfree_word.
  - split.
    + assert (Hoffset_m3 : Mem.load Mint64 m3 bd 8 =
        Some (Vlong (Int64.repr 0))).
      { eapply Mem.load_store_same with (chunk := Mint64) in Hstore_offset.
        exact Hstore_offset. }
      assert (Hfree_offset : Mem.load Mint64 m4 bd 8 =
          Mem.load Mint64 m3 bd 8).
      { eapply Mem.load_free with (m1 := m3) (bf := bl) (lo := 0)
          (hi := sizeof (Clight.genv_cenv ge0) (Tstruct _frameItem noattr))
          (m2 := m4).
        - exact Hfree_direct.
        - left; congruence. }
      rewrite Hoffset_m3 in Hfree_offset; exact Hfree_offset.
    + exact Hcall.
Qed.
