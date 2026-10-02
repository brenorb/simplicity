(** Actual Buffer63 reader entry, production assertion, initial length store,
    initial shift and normal return. The loop consumer is a separate obligation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_umul128_layout.
Require Import C.jet_write_buffer8_empty_exec C.jet_read_buffer8_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition buffer8_read_assert := match f_simplicity_read_buffer8.(fn_body) with
  | Ssequence s _ => s | _ => Sskip end.
Definition buffer8_read_temps bf base bo output bl slot := PTree.set _n (Vint (Int.repr 5))
  (PTree.set _src (Vptr bf (Ptrofs.repr base)) (PTree.set _len (Vptr bl (Ptrofs.repr slot))
    (PTree.set _buf (Vptr bo (Ptrofs.repr output)) (create_undef_temps f_simplicity_read_buffer8.(fn_temps))))).
Lemma buffer8_read_body_prefix : f_simplicity_read_buffer8.(fn_body) =
  Ssequence buffer8_read_assert (Ssequence
    (Sassign (Ederef (Etempvar _len (tptr tulong)) tulong) (Econst_int Int.zero tint))
    (Ssequence (Sset _i (Ebinop Oshl (Ecast (Econst_int Int.one tint) tulong) (Etempvar _n tint) tulong))
      buffer8_read_loop)).
Proof. reflexivity. Qed.

Theorem eval_read_buffer8_from_loop m mz mf lef bf base bo output bl slot :
  0 <= slot <= Ptrofs.max_unsigned ->
  Mem.store Mint64 m bl slot (Vlong Int64.zero) = Some mz ->
  Clight2.exec_stmt ge0 empty_env
    (PTree.set _i (Vlong (Int64.repr 32)) (buffer8_read_temps bf base bo output bl slot))
    mz buffer8_read_loop E0 lef mf Out_normal ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_read_buffer8)
    [Vptr bo (Ptrofs.repr output); Vptr bl (Ptrofs.repr slot); Vptr bf (Ptrofs.repr base); Vint (Int.repr 5)]
    E0 mf Vundef.
Proof.
  intros Hslot HS Hloop. set (le0 := buffer8_read_temps bf base bo output bl slot).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le0) (le2 := lef)
    (m1 := m) (m2 := mf) (out := Out_normal).
  - constructor.
    + constructor.
    + change (list_norepet [_buf; _len; _src; _n]). vm_compute.
      repeat (apply list_norepet_cons; [simpl; intuition discriminate|]). constructor.
    + change (list_disjoint [_buf; _len; _src; _n] [_i; _t'2; _t'1; _t'3]); vm_compute; intuition congruence.
    + constructor.
    + reflexivity.
  - rewrite buffer8_read_body_prefix.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m).
    + apply exec_buffer8_disabled_assert.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := mz).
      * eapply exec_Sassign_value with (v := Vlong Int64.zero) (v2 := Vint Int.zero)
          (b := bl) (ofs := Ptrofs.repr slot).
        -- eapply eval_Ederef. apply eval_Etempvar. unfold le0, buffer8_read_temps; umul128_lookup.
        -- apply eval_Econst_int.
        -- reflexivity.
        -- apply assign_loc_value with (chunk := Mint64); [reflexivity|].
           unfold Mem.storev. rewrite Ptrofs.unsigned_repr by exact Hslot. exact HS.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
          (le1 := PTree.set _i (Vlong (Int64.repr 32)) le0) (m1 := mz).
        -- apply exec_set. unfold le0, buffer8_read_temps; umul128_scalar.
        -- exact Hloop.
  - reflexivity.
  - reflexivity.
Qed.
