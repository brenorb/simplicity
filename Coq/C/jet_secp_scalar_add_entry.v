(** Actual three-local allocation entry and cleanup shape of scalar addition. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events.
Require Import C.jet_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_public_copy C.jet_secp_public_body C.jet_secp_scalar_add_body.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_add_temps (v_env : val) bd dbase bs sbase : temp_env :=
  PTree.set jets_secp._env v_env
    (PTree.set jets_secp._src (Vptr bs (Ptrofs.repr sbase))
      (PTree.set jets_secp._dst (Vptr bd (Ptrofs.repr dbase))
        (create_undef_temps (fn_temps f_simplicity_scalar_add)))).
Lemma scalar_add_public_entry v_env m ml ma mb bl ba bb bd dbase bs sbase :
  Mem.alloc m 0 16 = (ml, bl) -> Mem.alloc ml 0 32 = (ma, ba) ->
  Mem.alloc ma 0 32 = (mb, bb) ->
  function_entry2 secp_ge f_simplicity_scalar_add
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] m
    (scalar_add_public_env bl ba bb) (scalar_add_temps v_env bd dbase bs sbase) mb.
Proof.
  intros HL HA HB; constructor.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy; cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in Hxy; discriminate|congruence].
  - eapply alloc_variables_cons with (m1 := ml) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ml, bl)); exact HL.
    + eapply alloc_variables_cons with (m1 := ma) (b1 := ba).
      * change (Mem.alloc ml 0 32 = (ma, ba)); exact HA.
      * eapply alloc_variables_cons with (m1 := mb) (b1 := bb).
        -- change (Mem.alloc ma 0 32 = (mb, bb)); exact HB.
        -- constructor.
  - reflexivity.
Qed.

Lemma scalar_add_public_blocks bl ba bb :
  blocks_of_env secp_ge (scalar_add_public_env bl ba bb) = [(bl,0,16);(ba,0,32);(bb,0,32)].
Proof. reflexivity. Qed.

Lemma scalar_add_free_locals m bl ba bb :
  ba <> bl -> bb <> bl -> ba <> bb ->
  Mem.range_perm m bl 0 16 Cur Freeable ->
  Mem.range_perm m ba 0 32 Cur Freeable -> Mem.range_perm m bb 0 32 Cur Freeable ->
  exists mf, Mem.free_list m (blocks_of_env secp_ge (scalar_add_public_env bl ba bb)) = Some mf /\
    lframe (fun bx _ => bx <> ba /\ bx <> bb /\ bx <> bl) m mf.
Proof.
  intros HAL HBL HAB HL HA HB.
  destruct (free_list_exists [(bl,0,16);(ba,0,32);(bb,0,32)] m) as [mf [HFree HUnchanged]].
  - cbn; repeat constructor; cbn; intuition congruence.
  - intros bx lo hi [H|[H|[H|H]]];
      [inversion H; subst; exact HL|inversion H; subst; exact HA|
       inversion H; subst; exact HB|contradiction].
  - exists mf; split; [rewrite scalar_add_public_blocks; exact HFree|].
    eapply lframe_implies; [apply lframe_unchanged; exact HUnchanged|].
    intros bx pos [HA' [HB' HL']] HValid; cbn; intuition congruence.
Qed.
Print Assumptions scalar_add_public_entry.
Print Assumptions scalar_add_public_blocks.
Print Assumptions scalar_add_free_locals.

