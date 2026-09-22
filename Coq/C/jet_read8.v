(** Direct Clight execution setup for [simplicity_read8] at a one-word,
    byte-aligned layout. *)

From Coq Require Import ZArith List PArith.BinPos.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.

Require Import C.jet_exec.
Require Import C.jet_write8.
Require Import jets.

Import Clightdefs Clightdefs.ClightNotations.
Import Values Mem Ctypes.
Import Events.

Local Open Scope Z_scope.
Local Open Scope clight_scope.

Definition le_read8 (bf : block) : temp_env :=
  PTree.set _frame (Vptr bf Ptrofs.zero)
    (create_undef_temps f_simplicity_read8.(fn_temps)).

Lemma entry_read8 : forall (m : mem) (bf : block),
  function_entry2 ge0 f_simplicity_read8
    (Vptr bf Ptrofs.zero :: nil) m empty_env (le_read8 bf) m.
Proof.
  intros m bf.
  constructor.
  - constructor.
  - constructor.
    + simpl; tauto.
    + constructor.
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

Lemma eval_frame_edge_ofs : forall (m : mem) (le : temp_env)
    (bf bs : block) (ofs : ptrofs),
  le!_frame = Some (Vptr bf Ptrofs.zero) ->
  Mem.load Mptr m bf 0 = Some (Vptr bs ofs) ->
  eval_expr ge0 empty_env le m
    (Efield (Ederef (Etempvar _frame (tptr (Tstruct _frameItem noattr)))
       (Tstruct _frameItem noattr)) _edge (tptr tulong))
    (Vptr bs ofs).
Proof.
  intros m le bf bs ofs Hle Hload.
  eapply eval_Elvalue.
  - eapply eval_Efield_struct.
    + eapply eval_Elvalue.
      * eapply eval_Ederef.
        eapply eval_Etempvar; exact Hle.
      * apply deref_loc_copy.
        change (access_mode (Tstruct _frameItem noattr) = By_copy).
        reflexivity.
    + reflexivity.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
  - apply deref_loc_value with (chunk := Mptr).
    + vm_compute; reflexivity.
    + simpl [Mem.loadv]. exact Hload.
Qed.

Definition read8_keep_stmt : statement :=
  Scall (Some _t'2)
    (Evar _LSBkeep
      (Tfunction (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
    ((Ecast
       (Ebinop Oshr (Etempvar _t'4 tulong)
         (Ebinop Osub (Etempvar _frame_shift tulong)
           (Etempvar _n tulong) tulong) tulong) tulong) ::
     (Etempvar _n tulong) :: nil).

Lemma call_read8_keep : forall (le : temp_env) (m : mem)
    (w k : int64) (b : block),
  le!_t'4 = Some (Vlong w) ->
  le!_frame_shift = Some (Vlong (Int64.repr 8)) ->
  le!_n = Some (Vlong (Int64.repr 8)) ->
  Genv.find_symbol (Clight.genv_genv ge0) _LSBkeep = Some b ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr b Ptrofs.zero) =
    Some (Internal f_LSBkeep) ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBkeep)
    (Vlong w :: Vlong (Int64.repr 8) :: nil) E0 m (Vlong k) ->
  ClightBigstep.Clight2.exec_stmt ge0 empty_env le m read8_keep_stmt
    E0 (PTree.set _t'2 (Vlong k) le) m Out_normal.
Proof.
  intros le m w k b Hword Hshift Hn Hsym Hfun Heval.
  change (ClightBigstep.exec_stmt function_entry2 ge0 empty_env le m
    read8_keep_stmt E0 (set_opttemp (Some _t'2) (Vlong k) le) m
    Out_normal).
  eapply ClightBigstep.exec_Scall
    with (vf := Vptr b Ptrofs.zero)
         (vargs := Vlong w :: Vlong (Int64.repr 8) :: nil)
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
    + eapply eval_Ecast with (v1 := Vlong w).
      * eapply eval_Ebinop with (v1 := Vlong w)
          (v2 := Vlong Int64.zero).
        -- apply eval_Etempvar; exact Hword.
        -- eapply eval_Ebinop with (v1 := Vlong (Int64.repr 8))
             (v2 := Vlong (Int64.repr 8)).
           ++ apply eval_Etempvar; exact Hshift.
           ++ apply eval_Etempvar; exact Hn.
           ++ reflexivity.
        -- change (Some (Vlong (Int64.shru w Int64.zero)) =
             Some (Vlong w)).
           rewrite Int64.shru_zero; reflexivity.
      * reflexivity.
    + reflexivity.
    + eapply eval_Econs.
      * eapply eval_Etempvar; exact Hn.
      * reflexivity.
      * apply eval_Enil.
  - exact Hfun.
  - vm_compute; reflexivity.
  - exact Heval.
Qed.
