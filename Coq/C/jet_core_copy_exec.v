(** Execution of the actual statements [forwardBits(&src, k)] and
    [simplicity_copyBits(dst, &src, n)] of the core copy jets, inside the
    by-value source-copy lifecycle of [jet_core_wrapper]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_core_wrapper.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque ge0.
Set Default Timeout 30.

Definition block_copyBits : block := jet_symbol_block _simplicity_copyBits.
Definition block_forwardBits : block := jet_symbol_block _forwardBits.

Lemma symbol_copyBits :
  Genv.find_symbol (Clight.genv_genv ge0) _simplicity_copyBits = Some block_copyBits.
Proof. vm_compute; reflexivity. Qed.
Lemma funct_copyBits :
  Genv.find_funct (Clight.genv_genv ge0) (Vptr block_copyBits Ptrofs.zero) = Some (Internal f_simplicity_copyBits).
Proof. vm_compute; reflexivity. Qed.
Lemma symbol_forwardBits :
  Genv.find_symbol (Clight.genv_genv ge0) _forwardBits = Some block_forwardBits.
Proof. vm_compute; reflexivity. Qed.
Lemma funct_forwardBits :
  Genv.find_funct (Clight.genv_genv ge0) (Vptr block_forwardBits Ptrofs.zero) = Some (Internal f_forwardBits).
Proof. vm_compute; reflexivity. Qed.

Definition core_copy_call_e (arg : expr) : statement :=
  Scall None
    (Evar _simplicity_copyBits (Tfunction
      (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)))
      tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr));
     Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr));
     arg].

Definition core_copy_call (k : Z) : statement := core_copy_call_e (Econst_int (Int.repr k) tint).

Definition core_forward_call (n m : Z) : statement :=
  Scall None
    (Evar _forwardBits (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
    [Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr));
     Ebinop Osub (Econst_int (Int.repr n) tint) (Econst_int (Int.repr m) tint) tint].

Lemma exec_core_copy_call_e bl le m m' bd dbase arg k :
  0 <= k <= 1000 -> typeof arg = tint ->
  eval_expr ge0 (core_src_locals bl) le m arg (Vint (Int.repr k)) ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_copyBits)
    [Vptr bd (Ptrofs.repr dbase); Vptr bl Ptrofs.zero; Vlong (Int64.repr k)] E0 m' Vundef ->
  Clight2.exec_stmt ge0 (core_src_locals bl) le m (core_copy_call_e arg) E0 le m' Out_normal.
Proof.
  intros Hk Hty Harg HD Hcall.
  assert (Hr : forall z, 0 <= z <= 1000 -> Int.min_signed <= z <= Int.max_signed)
    by (intros z Hz; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
  change (Clight2.exec_stmt ge0 (core_src_locals bl) le m (core_copy_call_e arg) E0
    (set_opttemp None Vundef le) m' Out_normal).
  eapply exec_Scall with (vf := Vptr block_copyBits Ptrofs.zero) (f := Internal f_simplicity_copyBits)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bl Ptrofs.zero; Vlong (Int64.repr k)]) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + apply eval_Evar_global; [reflexivity|apply symbol_copyBits].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs with (v1 := Vptr bd (Ptrofs.repr dbase)).
    { apply eval_Etempvar; exact HD. }
    { reflexivity. }
    eapply eval_Econs.
    + apply eval_Eaddrof. apply eval_Evar_local. reflexivity.
    + reflexivity.
    + eapply eval_Econs with (v1 := Vint (Int.repr k)).
      * exact Harg.
      * rewrite Hty. simpl. unfold sem_cast. simpl. unfold cast_int_long. rewrite Int.signed_repr by (apply Hr; exact Hk). reflexivity.
      * apply eval_Enil.
  - apply funct_copyBits.
  - reflexivity.
  - exact Hcall.
Qed.

Lemma exec_core_copy_call bl le m m' bd dbase k :
  0 <= k <= 1000 -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_copyBits)
    [Vptr bd (Ptrofs.repr dbase); Vptr bl Ptrofs.zero; Vlong (Int64.repr k)] E0 m' Vundef ->
  Clight2.exec_stmt ge0 (core_src_locals bl) le m (core_copy_call k) E0 le m' Out_normal.
Proof.
  intros Hk HD Hcall. eapply exec_core_copy_call_e; try eassumption; [reflexivity|apply eval_Econst_int].
Qed.

Lemma exec_core_forward_call bl le m m' n mm :
  0 <= n - mm <= 1000 -> 0 <= n <= 1000 -> 0 <= mm <= 1000 ->
  Clight2.eval_funcall ge0 m (Internal f_forwardBits)
    [Vptr bl Ptrofs.zero; Vlong (Int64.repr (n - mm))] E0 m' Vundef ->
  Clight2.exec_stmt ge0 (core_src_locals bl) le m (core_forward_call n mm) E0 le m' Out_normal.
Proof.
  intros Hd Hn Hm Hcall.
  assert (Hr : forall z, -1000 <= z <= 1000 -> Int.min_signed <= z <= Int.max_signed)
    by (intros z Hz; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
  change (Clight2.exec_stmt ge0 (core_src_locals bl) le m (core_forward_call n mm) E0
    (set_opttemp None Vundef le) m' Out_normal).
  eapply exec_Scall with (vf := Vptr block_forwardBits Ptrofs.zero) (f := Internal f_forwardBits)
    (vargs := [Vptr bl Ptrofs.zero; Vlong (Int64.repr (n - mm))]) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + apply eval_Evar_global; [reflexivity|apply symbol_forwardBits].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof. apply eval_Evar_local. reflexivity.
    + reflexivity.
    + eapply eval_Econs with (v1 := Vint (Int.repr (n - mm))).
      * eapply eval_Ebinop with (v1 := Vint (Int.repr n)) (v2 := Vint (Int.repr mm));
          [apply eval_Econst_int|apply eval_Econst_int|].
        simpl. unfold sem_sub, sem_binarith. simpl.
        assert (HS : Int.sub (Int.repr n) (Int.repr mm) = Int.repr (n - mm)).
        { unfold Int.sub. rewrite !Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
          reflexivity. }
        rewrite HS. reflexivity.
      * simpl. unfold sem_cast. simpl. unfold cast_int_long.
        rewrite Int.signed_repr by (apply Hr; lia). reflexivity.
      * apply eval_Enil.
  - apply funct_forwardBits.
  - reflexivity.
  - exact Hcall.
Qed.
