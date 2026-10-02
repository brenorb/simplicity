(** Actual write_buffer8 entry/assertions/initial shift/loop/return for len=0,
    n=5. The initial-only layout consumer must still derive its loop calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_umul128_layout.
Require Import C.jet_write_buffer8_empty_exec C.jet_write_buffer8_empty_run.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition buffer8_first_assert := match f_simplicity_write_buffer8.(fn_body) with
  | Ssequence s _ => s | _ => Sskip end.
Definition buffer8_second_assert := match f_simplicity_write_buffer8.(fn_body) with
  | Ssequence _ (Ssequence s _) => s | _ => Sskip end.
Definition buffer8_empty_temps bf base buf := PTree.set _n (Vint (Int.repr 5))
  (PTree.set _len (Vlong Int64.zero) (PTree.set _buf buf
    (PTree.set _dst (Vptr bf (Ptrofs.repr base)) (create_undef_temps f_simplicity_write_buffer8.(fn_temps))))).

Lemma buffer8_body_prefix : f_simplicity_write_buffer8.(fn_body) =
  Ssequence buffer8_first_assert (Ssequence buffer8_second_assert
    (Ssequence (Sset _i (Ebinop Oshl (Ecast (Econst_int Int.one tint) tulong) (Etempvar _n tint) tulong))
      buffer8_actual_loop)).
Proof. reflexivity. Qed.

Theorem eval_write_buffer8_empty_composes m mf bf base buf :
  buffer8_empty_calls bf base buffer63_empty_counts m mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_write_buffer8)
    [Vptr bf (Ptrofs.repr base); buf; Vlong Int64.zero; Vint (Int.repr 5)] E0 mf Vundef.
Proof.
  intros Hcalls. set (le0 := buffer8_empty_temps bf base buf).
  set (le1 := PTree.set _i (Vlong (Int64.repr 32)) le0).
  destruct (exec_buffer8_empty_calls buffer63_empty_counts le1 m mf bf base buffer63_empty_counts_chain
    ltac:(unfold le1, le0, buffer8_empty_temps; umul128_lookup)
    ltac:(unfold le1, le0, buffer8_empty_temps; umul128_lookup)
    ltac:(unfold le1, buffer63_empty_counts, buffer8_empty_index; rewrite PTree.gss; reflexivity) Hcalls)
    as (lef & Hloop).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le0) (le2 := lef)
    (m1 := m) (m2 := mf) (out := Out_normal).
  - constructor.
    + constructor.
    + change (list_norepet [_dst; _buf; _len; _n]). vm_compute.
      repeat (apply list_norepet_cons; [simpl; intuition discriminate|]). constructor.
    + change (list_disjoint [_dst; _buf; _len; _n] [_i; _t'2; _t'1]); vm_compute; intuition congruence.
    + constructor.
    + reflexivity.
  - rewrite buffer8_body_prefix.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m).
    + apply exec_buffer8_disabled_assert.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m).
      * apply exec_buffer8_disabled_assert.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
        -- apply exec_set. unfold le0, buffer8_empty_temps. umul128_scalar.
        -- exact Hloop.
  - reflexivity.
  - reflexivity.
Qed.
