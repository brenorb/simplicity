(** Function-boundary composition for the actual simplicity_copyBits wrapper.
    The nonzero theorem is INTERNAL: it takes copyBitsHelper execution and its
    surviving cursor load/store as premises. Those premises must be derived
    from initial frame contracts before any projection jet can count as proved.
    The zero-count theorem is a complete helper call and changes no memory. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_readBit_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition copy_frame_env f bd dofs bs sofs n :=
  PTree.set _n (Vlong (Int64.repr n))
    (PTree.set _src (Vptr bs sofs)
      (PTree.set _dst (Vptr bd dofs) (create_undef_temps f.(fn_temps)))).

Lemma copy_frame_entry f m bd dofs bs sofs n :
  f.(fn_vars) = [] ->
  f.(fn_params) = [(_dst, tptr (Tstruct _frameItem noattr));
    (_src, tptr (Tstruct _frameItem noattr)); (_n, tulong)] ->
  list_disjoint [_dst; _src; _n] (map fst f.(fn_temps)) ->
  function_entry2 ge0 f [Vptr bd dofs; Vptr bs sofs; Vlong (Int64.repr n)]
    m empty_env (copy_frame_env f bd dofs bs sofs n) m.
Proof.
  intros HV HP HT. constructor.
  - rewrite HV; constructor.
  - rewrite HP. cbn. unfold _dst, _src, _n.
    repeat constructor; simpl; intuition discriminate.
  - rewrite HP; exact HT.
  - rewrite HV; constructor.
  - unfold copy_frame_env; rewrite HP; reflexivity.
Qed.
Lemma copyBits_entry m bd dofs bs sofs n :
  function_entry2 ge0 f_simplicity_copyBits
    [Vptr bd dofs; Vptr bs sofs; Vlong (Int64.repr n)]
    m empty_env (copy_frame_env f_simplicity_copyBits bd dofs bs sofs n) m.
Proof.
  apply copy_frame_entry; [reflexivity|reflexivity|].
  change (list_disjoint [_dst; _src; _n] [_t'1]).
  intros i j HI HJ Heq; cbn in HI, HJ; subst j.
  repeat match goal with H : _ \/ _ |- _ => destruct H end;
    try contradiction; vm_compute in *; congruence.
Qed.

Lemma eval_copyBits_zero m bd dofs bs sofs :
  Clight2.eval_funcall ge0 m (Internal f_simplicity_copyBits)
    [Vptr bd dofs; Vptr bs sofs; Vlong Int64.zero] E0 m Vundef.
Proof.
  change (Clight2.eval_funcall ge0 m (Internal f_simplicity_copyBits)
    [Vptr bd dofs; Vptr bs sofs; Vlong (Int64.repr 0)] E0 m Vundef).
  eapply eval_funcall_internal with (e := empty_env)
    (le1 := copy_frame_env f_simplicity_copyBits bd dofs bs sofs 0)
    (le2 := copy_frame_env f_simplicity_copyBits bd dofs bs sofs 0)
    (m1 := m) (m2 := m) (out := Out_return None).
  - apply copyBits_entry.
  - apply exec_Sseq_2; [|discriminate].
    eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
    + eapply eval_Ebinop with (v1 := Vint Int.zero) (v2 := Vlong Int64.zero).
      * apply eval_Econst_int.
      * apply eval_Etempvar; reflexivity.
      * reflexivity.
    + reflexivity.
    + apply exec_Sreturn_none.
  - reflexivity.
  - reflexivity.
Qed.

Definition block_copyBitsHelper := jet_symbol_block _copyBitsHelper.
Lemma symbol_copyBitsHelper :
  Genv.find_symbol (Clight.genv_genv ge0) _copyBitsHelper = Some block_copyBitsHelper.
Proof. vm_compute; reflexivity. Qed.
Lemma funct_copyBitsHelper :
  Genv.find_funct (Clight.genv_genv ge0) (Vptr block_copyBitsHelper Ptrofs.zero) =
    Some (Internal f_copyBitsHelper).
Proof. vm_compute; reflexivity. Qed.

Lemma eval_copyBits_nonzero_composes m mi mf bd base bs sofs cursor n :
  frame_base_valid base -> 0 < n <= cursor -> cursor <= Int64.max_unsigned ->
  Clight2.eval_funcall ge0 m (Internal f_copyBitsHelper)
    [Vptr bd (Ptrofs.repr base); Vptr bs sofs; Vlong (Int64.repr n)] E0 mi Vundef ->
  Mem.load Mint64 mi bd (base + 8) = Some (Vlong (Int64.repr cursor)) ->
  Mem.store Mint64 mi bd (base + 8) (Vlong (Int64.repr (cursor - n))) = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_copyBits)
    [Vptr bd (Ptrofs.repr base); Vptr bs sofs; Vlong (Int64.repr n)] E0 mf Vundef.
Proof.
  intros HB HN HM HC HO SF.
  set (le := copy_frame_env f_simplicity_copyBits bd (Ptrofs.repr base) bs sofs n).
  assert (Hneq : Int64.eq Int64.zero (Int64.repr n) = Datatypes.false).
  { apply Int64.eq_false. intro HE. apply (f_equal Int64.unsigned) in HE.
    rewrite Int64.unsigned_repr in HE by lia. change (0 = n) in HE. lia. }
  assert (Hsub : Int64.sub (Int64.repr cursor) (Int64.repr n) = Int64.repr (cursor - n)).
  { unfold Int64.sub. rewrite !Int64.unsigned_repr by lia. reflexivity. }
  eapply eval_funcall_internal with (e := empty_env) (le1 := le)
    (le2 := PTree.set _t'1 (Vlong (Int64.repr cursor)) le)
    (m1 := m) (m2 := mf) (out := Out_normal).
  - apply copyBits_entry.
  - unfold f_simplicity_copyBits; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le).
    + eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
      * eapply eval_Ebinop with (v1 := Vint Int.zero) (v2 := Vlong (Int64.repr n)).
        -- apply eval_Econst_int.
        -- apply eval_Etempvar; reflexivity.
        -- change (Some (Val.of_bool (Int64.eq Int64.zero (Int64.repr n))) =
             Some (Vint Int.zero)). rewrite Hneq; reflexivity.
      * reflexivity.
      * apply exec_Sskip.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi) (le1 := le).
      * eapply exec_Scall with (vf := Vptr block_copyBitsHelper Ptrofs.zero)
          (vargs := [Vptr bd (Ptrofs.repr base); Vptr bs sofs; Vlong (Int64.repr n)])
          (f := Internal f_copyBitsHelper) (vres := Vundef).
        -- reflexivity.
        -- eapply eval_Elvalue.
           ++ eapply eval_Evar_global; [reflexivity|apply symbol_copyBitsHelper].
           ++ apply deref_loc_reference; reflexivity.
        -- eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
           eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
           eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|apply eval_Enil].
        -- apply funct_copyBitsHelper.
        -- reflexivity.
        -- exact HC.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi)
          (le1 := PTree.set _t'1 (Vlong (Int64.repr cursor)) le).
        -- apply exec_set. eapply eval_Elvalue.
           ++ eapply eval_Efield_struct.
              ** eapply eval_Elvalue.
                 --- eapply eval_Ederef; apply eval_Etempvar; reflexivity.
                 --- apply deref_loc_copy; reflexivity.
              ** reflexivity.
              ** reflexivity.
              ** reflexivity.
           ++ apply deref_loc_value with (chunk := Mint64); [reflexivity|].
              unfold Mem.loadv.
              change (Mem.load Mint64 mi bd
                (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 8))) =
                Some (Vlong (Int64.repr cursor))).
              rewrite frame_field_address by (assumption || lia). exact HO.
        -- eapply exec_Sassign_value with (v := Vlong (Int64.repr (cursor - n)))
            (v2 := Vlong (Int64.repr (cursor - n))).
           ++ eapply eval_Efield_struct.
              ** eapply eval_Elvalue.
                 --- eapply eval_Ederef; apply eval_Etempvar; reflexivity.
                 --- apply deref_loc_copy; reflexivity.
              ** reflexivity.
              ** reflexivity.
              ** reflexivity.
           ++ eapply eval_Ebinop with (v1 := Vlong (Int64.repr cursor))
                (v2 := Vlong (Int64.repr n)).
              ** apply eval_Etempvar; reflexivity.
              ** apply eval_Etempvar; reflexivity.
              ** change (Some (Vlong (Int64.sub (Int64.repr cursor) (Int64.repr n))) =
                   Some (Vlong (Int64.repr (cursor - n)))). rewrite Hsub; reflexivity.
           ++ reflexivity.
           ++ apply assign_frame_offset_at; assumption.
  - reflexivity.
  - reflexivity.
Qed.

(** Discharge the wrapper's cursor store from the state reached by the helper.
    This still does not prove copyBitsHelper or discharge its execution premise. *)
Theorem eval_copyBits_nonzero_advances m mi bd base bs sofs bw edge cursor n :
  frame_base_valid base -> 0 < n <= cursor -> cursor <= Int64.max_unsigned ->
  Clight2.eval_funcall ge0 m (Internal f_copyBitsHelper)
    [Vptr bd (Ptrofs.repr base); Vptr bs sofs; Vlong (Int64.repr n)] E0 mi Vundef ->
  frame_fields_at mi bd base bw edge cursor ->
  Mem.valid_access mi Mint64 bd (base + 8) Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_copyBits)
      [Vptr bd (Ptrofs.repr base); Vptr bs sofs; Vlong (Int64.repr n)] E0 mf Vundef /\
    frame_fields_at mf bd base bw edge (cursor - n) /\
    (forall chunk b ofs, b <> bd \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk mi b ofs) /\
    (forall b ofs kind p, Mem.perm mi b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block mi b -> Mem.valid_block mf b).
Proof.
  intros HB HN HM HC [HE HO] PW.
  destruct (Mem.valid_access_store mi Mint64 bd (base + 8)
    (Vlong (Int64.repr (cursor - n))) PW) as [mf SF].
  exists mf. split.
  - eapply eval_copyBits_nonzero_composes; eauto.
  - split.
    + split.
      * erewrite Mem.load_store_other; [exact HE|exact SF|].
        right; left; change (base + 8 <= base + 8); lia.
      * exact (Mem.load_store_same _ _ _ _ _ _ SF).
    + split.
      * intros chunk b ofs Hsep. eapply Mem.load_store_other; [exact SF|].
        change (b <> bd \/ ofs + size_chunk chunk <= base + 8 \/ base + 8 + 8 <= ofs). lia.
      * split.
        -- intros b ofs kind p HP. eapply Mem.perm_store_1; eauto.
        -- intros b HV. eapply Mem.store_valid_block_1; eauto.
Qed.
