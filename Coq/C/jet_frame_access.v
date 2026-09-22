(** Offset-aware word accesses and pure word-helper calls in the jet environment. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Cop Clight Maps ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jets.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Lemma eval_frame_word_at m le bw ofs w :
  le!_frame_ptr = Some (Vptr bw ofs) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned ofs) = Some (Vlong w) ->
  eval_expr ge0 empty_env le m
    (Ederef (Etempvar _frame_ptr (tptr tulong)) tulong) (Vlong w).
Proof.
  intros HP HW. eapply eval_Elvalue.
  - eapply eval_Ederef. eapply eval_Etempvar; exact HP.
  - eapply deref_loc_value; [reflexivity | exact HW].
Qed.

Lemma eval_frame_word_lvalue_at m le bw ofs :
  le!_frame_ptr = Some (Vptr bw ofs) ->
  eval_lvalue ge0 empty_env le m
    (Ederef (Etempvar _frame_ptr (tptr tulong)) tulong) bw ofs Full.
Proof. intros HP. eapply eval_Ederef. eapply eval_Etempvar; exact HP. Qed.

Lemma assign_frame_word_at m mf bw ofs w :
  Mem.store Mint64 m bw (Ptrofs.unsigned ofs) (Vlong w) = Some mf ->
  assign_loc (prog_comp_env prog) tulong m bw ofs Full (Vlong w) mf.
Proof. intros HS. eapply assign_loc_value; [reflexivity | exact HS]. Qed.

Lemma call_word_helper m le result fid f b a1 a2 w n v :
  type_of_function f = Tfunction (Tcons tulong (Tcons tulong Tnil)) tulong cc_default ->
  typeof a1 = tulong -> typeof a2 = tulong ->
  Genv.find_symbol (Clight.genv_genv ge0) fid = Some b ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr b Ptrofs.zero) = Some (Internal f) ->
  eval_expr ge0 empty_env le m a1 (Vlong w) ->
  eval_expr ge0 empty_env le m a2 (Vlong n) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f) [Vlong w; Vlong n] E0 m (Vlong v) ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env le m
    (Scall (Some result)
      (Evar fid (Tfunction (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) [a1; a2])
    E0 (PTree.set result (Vlong v) le) m Out_normal.
Proof.
  intros HT T1 T2 HS HF H1 H2 HC.
  eapply ClightBigstep.exec_Scall with (vf := Vptr b Ptrofs.zero)
    (vargs := [Vlong w; Vlong n]) (f := Internal f) (vres := Vlong v).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity | exact HS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [exact H1 | rewrite T1; reflexivity |].
    eapply eval_Econs; [exact H2 | rewrite T2; reflexivity | apply eval_Enil].
  - exact HF.
  - exact HT.
  - exact HC.
Qed.
