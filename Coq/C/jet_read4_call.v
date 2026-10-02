(** Actual read4 call adapter using identifier-based generated symbols. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Ctypes Clight Maps ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8.
Import Values Ctypes ListNotations Clightdefs.
Set Default Timeout 10.
Definition nibble_read result := Scall (Some result)
  (Evar _simplicity_read4 (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil) tuchar cc_default))
  [Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))].
Lemma symbol_read4 : Genv.find_symbol (Clight.genv_genv ge0) _simplicity_read4 =
  Some (jet_symbol_block _simplicity_read4).
Proof. vm_compute; reflexivity. Qed.
Lemma funct_read4 : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _simplicity_read4) Ptrofs.zero) = Some (Internal f_simplicity_read4).
Proof. vm_compute; reflexivity. Qed.

Lemma call_nibble_read result le m mr bl r :
  Clight2.eval_funcall ge0 m (Internal f_simplicity_read4) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  Clight2.exec_stmt ge0 (e_one8 bl) le m (nibble_read result)
    E0 (PTree.set result (Vint r) le) mr Out_normal.
Proof.
  intros Hread. eapply exec_Scall with (vf := Vptr (jet_symbol_block _simplicity_read4) Ptrofs.zero)
    (vargs := [Vptr bl Ptrofs.zero]) (f := Internal f_simplicity_read4) (vres := Vint r).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|apply symbol_read4].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + eapply eval_Eaddrof. eapply eval_Evar_local; reflexivity.
    + reflexivity.
    + apply eval_Enil.
  - apply funct_read4.
  - reflexivity.
  - exact Hread.
Qed.

