(** Conditional Clight execution infrastructure for [simplicity_increment_8].

    This file deliberately keeps the read/write helper calls explicit.  The
    resulting body theorem is composition infrastructure; the public
    equivalence theorem must still prove those helper executions from a
    concrete frame layout. *)

From Coq Require Import ZArith List PArith.BinPos.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.

Require Import C.jet_exec.
Require Import C.jet_one8.
Require Import C.jet_write8.
Require Import jets.

Import Clightdefs Clightdefs.ClightNotations.
Import Values Mem Ctypes.
Import Events.

Local Open Scope Z_scope.
Local Open Scope clight_scope.

Definition e_increment8 (bl : block) : env :=
  PTree.set _src (bl, Tstruct _frameItem noattr) empty_env.

Definition le_increment8 (bd bs : block) (ofs : ptrofs) : temp_env :=
  PTree.set _dst (Vptr bd Ptrofs.zero)
    (PTree.set _src (Vptr bs ofs)
      (PTree.set _env Vundef
        (create_undef_temps f_simplicity_increment_8.(fn_temps)))).

Lemma entry_increment8 : forall (m m1 : mem) (bl bd bs : block)
    (ofs : ptrofs),
    Mem.alloc m 0 16 = (m1, bl) ->
  function_entry2 ge0 f_simplicity_increment_8
    (Vptr bd Ptrofs.zero :: Vptr bs ofs :: Vundef :: nil) m
    (e_increment8 bl) (le_increment8 bd bs ofs) m1.
Proof.
  intros m m1 bl bd bs ofs Halloc.
  constructor.
  - change (list_norepet (_src :: nil)).
    repeat constructor; simpl; tauto.
  - change (list_norepet (_dst :: _src :: _env :: nil)).
    unfold _dst, _src, _env.
    repeat constructor; simpl; intuition discriminate.
  - change (list_disjoint (_dst :: _src :: _env :: nil)
      (_x :: _t'1 :: nil)).
    intros id1 id2 H1 H2 Heq.
    simpl in H1, H2.
    subst id2.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H
    end.
    all: vm_compute in *; congruence.
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bl).
    + change (Mem.alloc m 0 16 = (m1, bl)). exact Halloc.
    + constructor.
  - simpl [le_increment8]. reflexivity.
Qed.
