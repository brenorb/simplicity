(** Actual legacy Elements helper bodies and a width-polymorphic helper/write
    composition. uint_fast16_t is a 64-bit carrier in this generated LP64 TU. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import C.jet_exec C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval.
Require Import C.jet_elements_call C.jet_elements_is_final_local C.jet_elements_tx_field_set.
Require Import C.jet_elements_wrapper C.jet_elements_transport C.jet_wide.
Require C.jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Definition legacy_lock_fn (field : ident) : function := {|
  fn_return := tulong; fn_callconv := cc_default;
  fn_params := [(_tx, tptr (Tstruct _elementsTransaction noattr))];
  fn_vars := []; fn_temps := [(_t'1, tulong); (_t'3, tulong); (_t'2, tulong)];
  fn_body := Ssequence
    (Ssequence
      (Sset _t'2 (Efield (Ederef (Etempvar _tx (tptr (Tstruct _elementsTransaction noattr)))
        (Tstruct _elementsTransaction noattr)) _version tulong))
      (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 2) tint) (Etempvar _t'2 tulong) tint)
        (Ssequence
          (Sset _t'3 (Efield (Ederef (Etempvar _tx (tptr (Tstruct _elementsTransaction noattr)))
            (Tstruct _elementsTransaction noattr)) field tulong))
          (Sset _t'1 (Ecast (Etempvar _t'3 tulong) tulong)))
        (Sset _t'1 (Ecast (Econst_int (Int.repr 0) tint) tulong))))
    (Sreturn (Some (Etempvar _t'1 tulong)))
|}.

Lemma legacy_distance_fn_shape : f_obsolete_lockDistance = legacy_lock_fn _obsolete_lockDistance.
Proof. reflexivity. Qed.
Lemma legacy_duration_fn_shape : f_obsolete_lockDuration = legacy_lock_fn _obsolete_lockDuration.
Proof. reflexivity. Qed.
Lemma legacy_version_at : elements_field_at _elementsTransaction _version 720.
Proof. vm_compute; reflexivity. Qed.
Lemma legacy_distance_at : elements_field_at _elementsTransaction _obsolete_lockDistance 736.
Proof. vm_compute; reflexivity. Qed.
Lemma legacy_duration_at : elements_field_at _elementsTransaction _obsolete_lockDuration 744.
Proof. vm_compute; reflexivity. Qed.

Definition legacy_lock_result (ver value : int64) : int64 :=
  if Int64.ltu ver (Int64.repr 2) then Int64.zero else value.

Lemma legacy_lock_entry field m bt base :
  function_entry2 elements_ge (legacy_lock_fn field) [Vptr bt (Ptrofs.repr base)]
    m empty_env
    (PTree.set _tx (Vptr bt (Ptrofs.repr base))
      (create_undef_temps (fn_temps (legacy_lock_fn field)))) m.
Proof.
  apply function_entry2_intro.
  - apply list_norepet_nil.
  - change (list_norepet [_tx]). constructor; [intro H; inversion H|constructor].
  - change (list_disjoint [_tx] [_t'1; _t'3; _t'2]).
    intros x y HX HY Hxy. cbn in HX, HY.
    destruct HX as [HX|[]]. destruct HY as [HY|[HY|[HY|[]]]];
      subst x y; vm_compute in Hxy; discriminate.
  - apply alloc_variables_nil.
  - reflexivity.
Qed.

Lemma eval_legacy_lock_fn field delta m bt base ver value :
  elements_field_at _elementsTransaction field delta -> 0 <= delta -> delta + 8 <= 760 ->
  0 <= base -> base + 760 <= Ptrofs.max_unsigned ->
  Mem.load Mint64 m bt (base + 720) = Some (Vlong ver) ->
  Mem.load Mint64 m bt (base + delta) = Some (Vlong value) ->
  Clight2.eval_funcall elements_ge m (Internal (legacy_lock_fn field))
    [Vptr bt (Ptrofs.repr base)] E0 m (Vlong (legacy_lock_result ver value)).
Proof.
  intros Hfield Hd HdM Hb HbM HV HL.
  assert (HF : forall le f d v,
    elements_field_at _elementsTransaction f d -> 0 <= d -> d + 8 <= 760 ->
    le!_tx = Some (Vptr bt (Ptrofs.repr base)) -> Mem.load Mint64 m bt (base + d) = Some v ->
    eval_expr elements_ge empty_env le m
      (Efield (Ederef (Etempvar _tx (tptr (Tstruct _elementsTransaction noattr)))
        (Tstruct _elementsTransaction noattr)) f tulong) v).
  { intros le f d v Hf Hd0 Hd1 Htx Hload.
    eapply eval_elements_field_value with (sid := _elementsTransaction) (delta := d) (chunk := Mint64);
      [reflexivity|exact Hf|reflexivity|apply eval_elements_deref_struct; exact Htx|].
    rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact Hload]. }
  unfold legacy_lock_result. destruct (Int64.ltu ver (Int64.repr 2)) eqn:HC.
  all: eapply eval_funcall_internal with (e := empty_env) (m1 := m) (m2 := m)
    (out := Out_return (Some (Vlong (if Int64.ltu ver (Int64.repr 2) then Int64.zero else value), tulong))).
  all: try solve [apply legacy_lock_entry].
  - rewrite HC. cbn [legacy_lock_fn fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m); [|apply exec_Sreturn_some; apply eval_Etempvar; apply PTree.gss].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
    + apply exec_set. apply (HF _ _ 720); [exact legacy_version_at|lia|lia|apply PTree.gss|exact HV].
    + eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
      * eapply eval_Ebinop; [constructor|apply eval_Etempvar; apply PTree.gss|].
        change (Some (Val.of_bool (negb (Int64.ltu ver (Int64.repr 2)))) = Some Vfalse).
        rewrite HC. reflexivity.
      * reflexivity.
      * apply exec_set. apply eval_Ecast with (v1 := Vint Int.zero); [constructor|reflexivity].
  - rewrite HC. cbn. split; [discriminate|reflexivity].
  - reflexivity.
  - rewrite HC. cbn [legacy_lock_fn fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m); [|apply exec_Sreturn_some; apply eval_Etempvar; apply PTree.gss].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
    + apply exec_set. apply (HF _ _ 720); [exact legacy_version_at|lia|lia|apply PTree.gss|exact HV].
    + eapply exec_Sifthenelse with (v1 := Vtrue) (b := true).
      * eapply eval_Ebinop; [constructor|apply eval_Etempvar; apply PTree.gss|].
        change (Some (Val.of_bool (negb (Int64.ltu ver (Int64.repr 2)))) = Some Vtrue).
        rewrite HC. reflexivity.
      * reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
        -- apply exec_set. apply (HF _ _ delta);
             [exact Hfield|exact Hd|exact HdM|rewrite PTree.gso by discriminate; apply PTree.gss|exact HL].
        -- apply exec_set. apply eval_Ecast with (v1 := Vlong value);
             [apply eval_Etempvar; apply PTree.gss|reflexivity].
  - rewrite HC. cbn. split; [discriminate|reflexivity].
  - reflexivity.
Qed.

Definition elements_helper_write_mid width (fid : ident) : statement :=
  Ssequence
    (Ssequence (elements_env_tx_set _t'2)
      (Scall (Some _t'1) (Evar fid (Tfunction
        (Tcons (tptr (Tstruct _elementsTransaction noattr)) Tnil) tulong cc_default))
        [Etempvar _t'2 (tptr (Tstruct _elementsTransaction noattr))]))
    (Scall None (Evar (wide_writer_id width) (Tfunction
      (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
      [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _t'1 tulong]).

Lemma exec_elements_helper_write_mid width fid f e le m me bd base be ebase bt tbase r :
  Genv.find_symbol (Clight.genv_genv elements_ge) fid = Some (elements_symbol_block fid) ->
  Genv.find_funct (Clight.genv_genv elements_ge) (Vptr (elements_symbol_block fid) Ptrofs.zero) = Some (Internal f) ->
  type_of_fundef (Internal f) = Tfunction (Tcons (tptr (Tstruct _elementsTransaction noattr)) Tnil) tulong cc_default ->
  e!fid = None -> e!(wide_writer_id width) = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr base)) ->
  0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Clight2.eval_funcall elements_ge m (Internal f) [Vptr bt (Ptrofs.repr tbase)] E0 m (Vlong r) ->
  Clight2.eval_funcall elements_ge m (Internal (wide_writer width))
    [Vptr bd (Ptrofs.repr base); Vlong r] E0 me Vundef ->
  Clight2.exec_stmt elements_ge e le m (elements_helper_write_mid width fid) E0
    (PTree.set _t'1 (Vlong r) (PTree.set _t'2 (Vptr bt (Ptrofs.repr tbase)) le)) me Out_normal.
Proof.
  intros HS HF HT HE HW HEnv HDst HB HM HL HCall HWrite.
  unfold elements_helper_write_mid.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
    (le1 := PTree.set _t'1 (Vlong r) (PTree.set _t'2 (Vptr bt (Ptrofs.repr tbase)) le)).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
    + eapply exec_elements_env_tx_set; eassumption.
    + change (PTree.set _t'1 (Vlong r) (PTree.set _t'2 (Vptr bt (Ptrofs.repr tbase)) le))
        with (set_opttemp (Some _t'1) (Vlong r) (PTree.set _t'2 (Vptr bt (Ptrofs.repr tbase)) le)).
      eapply exec_Scall with (vf := Vptr (elements_symbol_block fid) Ptrofs.zero)
        (vargs := [Vptr bt (Ptrofs.repr tbase)]) (f := Internal f).
      * reflexivity.
      * eapply eval_Elvalue; [apply eval_Evar_global; [exact HE|exact HS]|apply deref_loc_reference; reflexivity].
      * eapply eval_Econs; [apply eval_Etempvar; apply PTree.gss|reflexivity|apply eval_Enil].
      * exact HF.
      * exact HT.
      * exact HCall.
  - refine (exec_elements_helper_call _ _ _ None (wide_writer_id width) (wide_writer width)
      _ _ _ _ _ Vundef _ _ _ _ _ _).
    + destruct width; unfold elements_core_helpers, wide_writer, wide_writer_id; simpl; tauto.
    + exact HW.
    + eapply eval_Econs.
      * apply eval_Etempvar. repeat rewrite PTree.gso by discriminate. exact HDst.
      * reflexivity.
      * eapply eval_Econs; [apply eval_Etempvar; apply PTree.gss|reflexivity|apply eval_Enil].
    + destruct width; reflexivity.
    + exact HWrite.
Qed.
