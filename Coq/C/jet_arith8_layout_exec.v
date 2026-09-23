(** Shared entry/copy/call rules, without fixed destination addresses. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_increment8 C.jet_add8.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition le_arith8_layout f bd dofs bs sofs : temp_env :=
  PTree.set _env Vundef (PTree.set _src (Vptr bs sofs)
    (PTree.set _dst (Vptr bd dofs) (create_undef_temps f.(fn_temps)))).

Lemma entry_frame_jet f m ma bl bd dofs bs sofs :
  f.(fn_vars) = [(_src, Tstruct _frameItem noattr)] ->
  f.(fn_params) = [(_dst, tptr (Tstruct _frameItem noattr));
    (_src, Tstruct _frameItem noattr); (_env, tptr (Tstruct _txEnv noattr))] ->
  list_disjoint [_dst; _src; _env] (map fst f.(fn_temps)) ->
  Mem.alloc m 0 16 = (ma, bl) ->
  function_entry2 ge0 f [Vptr bd dofs; Vptr bs sofs; Vundef]
    m (e_one8 bl) (le_arith8_layout f bd dofs bs sofs) ma.
Proof.
  intros HV HP HT HA. constructor.
  - rewrite HV. cbn. repeat constructor; simpl; tauto.
  - rewrite HP. cbn. unfold _dst, _src, _env.
    repeat constructor; simpl; intuition discriminate.
  - rewrite HP. exact HT.
  - rewrite HV. eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma, bl)); exact HA.
    + constructor.
  - unfold le_arith8_layout. rewrite HP; reflexivity.
Qed.

Lemma exec_frame_jet_copy m mc bl bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  ClightBigstep.Clight2.exec_stmt ge0 (e_one8 bl) le m
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    E0 le mc Out_normal.
Proof.
  intros HB HS HD HL Hload Hstore.
  assert (HA : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr. unfold frame_base_valid in HB; lia. }
  eapply exec_Sassign_copy.
  - eapply eval_Evar_local; reflexivity.
  - eapply eval_Etempvar; exact HL.
  - reflexivity.
  - eapply assign_frameItem_copy.
    + reflexivity.
    + intros _. rewrite HA; exact HS.
    + intros _. exists 0; reflexivity.
    + left; exact HD.
    + rewrite HA; exact Hload.
    + exact Hstore.
Qed.

Definition frame_writer_call fid aty rty arg :=
  Scall None (Evar fid (Tfunction
    (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons aty Tnil)) rty cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr)); arg].

Lemma call_frame_writer_cast e le m mf bd dofs fid f b aty rty arg vraw v vret :
  e!fid = None -> le!_dst = Some (Vptr bd dofs) ->
  type_of_function f = Tfunction
    (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons aty Tnil)) rty cc_default ->
  Genv.find_symbol (Clight.genv_genv ge0) fid = Some b ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr b Ptrofs.zero) = Some (Internal f) ->
  eval_expr ge0 e le m arg vraw -> sem_cast vraw (typeof arg) aty m = Some v ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f) [Vptr bd dofs; v] E0 mf vret ->
  ClightBigstep.Clight2.exec_stmt ge0 e le m (frame_writer_call fid aty rty arg)
    E0 le mf Out_normal.
Proof.
  intros HE HD HT HS HF HV HC HW.
  eapply exec_Scall with (vf := Vptr b Ptrofs.zero) (vargs := [Vptr bd dofs; v])
    (f := Internal f) (vres := vret).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [exact HE|exact HS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + eapply eval_Etempvar; exact HD.
    + reflexivity.
    + eapply eval_Econs; [exact HV|exact HC|apply eval_Enil].
  - exact HF.
  - exact HT.
  - exact HW.
Qed.

Lemma call_frame_writer e le m mf bd dofs fid f b aty rty arg v vret :
  e!fid = None -> le!_dst = Some (Vptr bd dofs) ->
  type_of_function f = Tfunction
    (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons aty Tnil)) rty cc_default ->
  Genv.find_symbol (Clight.genv_genv ge0) fid = Some b ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr b Ptrofs.zero) = Some (Internal f) ->
  eval_expr ge0 e le m arg v -> sem_cast v (typeof arg) aty m = Some v ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f) [Vptr bd dofs; v] E0 mf vret ->
  ClightBigstep.Clight2.exec_stmt ge0 e le m (frame_writer_call fid aty rty arg)
    E0 le mf Out_normal.
Proof. intros. eapply call_frame_writer_cast; eauto. Qed.



Lemma eval_increment8_carry_env : forall (m : mem) (e : env) (le : temp_env) (r : int),
  le!_x = Some (Vint (increment8_u r)) ->
  eval_expr ge0 e le m
    increment8_carry_expr (Vint (increment8_carry_bit r)).
Proof.
  intros m e le r HX.
  unfold increment8_carry_expr, increment8_carry_bit.
  eapply eval_Ebinop.
  - eapply eval_Ebinop.
    + eapply eval_Ebinop.
      * apply eval_Econst_int.
      * apply eval_Econst_int.
      * cbn; vm_compute; reflexivity.
    + apply eval_Econst_int.
    + cbn; reflexivity.
  - eapply eval_Etempvar.
    exact HX.
  - change (Some (Val.of_bool
      (Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r))) =
      Some (Vint
        (if Int.ltu (Int.sub (Int.repr 255) (Int.repr 1))
            (increment8_u r)
        then Int.one else Int.zero))).
    destruct (Int.ltu (Int.sub (Int.repr 255) (Int.repr 1))
      (increment8_u r)); reflexivity.
Qed.

Lemma eval_increment8_sum_env : forall (m : mem) (e : env) (le : temp_env) (r : int),
  le!_x = Some (Vint (increment8_u r)) ->
  eval_expr ge0 e le m
    increment8_sum_expr (Vint (increment8_byte r)).
Proof.
  intros m e le r HX.
  unfold increment8_sum_expr, increment8_byte, increment8_sum_raw,
    increment8_u.
  eapply eval_Ecast.
  - eapply eval_Ebinop.
    + eapply eval_Ebinop.
      * apply eval_Econst_int.
      * eapply eval_Etempvar.
        exact HX.
      * cbn; reflexivity.
    + apply eval_Econst_int.
    + cbn; reflexivity.
  - cbn; reflexivity.
Qed.

Lemma eval_add8_carry_env : forall (m : mem) (e : env) (le : temp_env) (r s : int),
  le!_x = Some (Vint (add8_u r)) ->
  le!_y = Some (Vint (add8_u s)) ->
  eval_expr ge0 e le m
    add8_carry_expr (Vint (add8_carry_bit r s)).
Proof.
  intros m e le r s HX HY.
  unfold add8_carry_expr, add8_carry_bit.
  eapply eval_Ebinop.
  - eapply eval_Ebinop.
    + eapply eval_Ebinop.
      * apply eval_Econst_int.
      * apply eval_Econst_int.
      * cbn; vm_compute; reflexivity.
    + eapply eval_Etempvar. exact HY.
    + cbn; reflexivity.
  - eapply eval_Etempvar.
    exact HX.
  - change (Some (Val.of_bool
      (Int.ltu (Int.sub (Int.repr 255) (add8_u s)) (add8_u r))) =
      Some (Vint
        (if Int.ltu (Int.sub (Int.repr 255) (add8_u s))
            (add8_u r)
        then Int.one else Int.zero))).
    destruct (Int.ltu (Int.sub (Int.repr 255) (add8_u s))
      (add8_u r)); reflexivity.
Qed.

Lemma eval_add8_sum_env : forall (m : mem) (e : env) (le : temp_env) (r s : int),
  le!_x = Some (Vint (add8_u r)) ->
  le!_y = Some (Vint (add8_u s)) ->
  eval_expr ge0 e le m
    add8_sum_expr (Vint (add8_byte r s)).
Proof.
  intros m e le r s HX HY.
  unfold add8_sum_expr, add8_byte, add8_sum_raw,
    add8_u.
  eapply eval_Ecast.
  - eapply eval_Ebinop.
    + eapply eval_Ebinop.
      * apply eval_Econst_int.
      * eapply eval_Etempvar.
        exact HX.
      * cbn; reflexivity.
    + eapply eval_Etempvar. exact HY.
    + cbn; reflexivity.
  - cbn; reflexivity.
Qed.
