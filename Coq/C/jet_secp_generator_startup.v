(** The actual zero auxiliary scalar and both read-only generator tables.
    Establish and transport readiness; do not assume it after a caller. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Ctypes Clight ClightBigstep Memory Values Globalenvs.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_clight_forward
  C.jet_clight_readonly C.jet_clight_readonly_frame C.jet_clight_internal_preserve
  C.jet_secp_generator_zero_global C.jet_secp_generator_globals
  C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_add_reader_support.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge generator_zero_block generator_table_block.

Definition generator_startup m := generator_zero_global_state m /\ forall h,generator_table_state h m.

Theorem generator_startup_initializes m : Genv.init_mem jets_secp.prog=Some m -> generator_startup m.
Proof.
  intro Init;split;[apply generator_zero_global_initializes|intro h;apply generator_table_initializes];exact Init.
Qed.

Theorem generator_startup_exists : exists m,Genv.init_mem jets_secp.prog=Some m /\ generator_startup m.
Proof.
  destruct generator_tables_initialized_memory_exists as (m & Init & _).
  exists m;split;[exact Init|apply generator_startup_initializes;exact Init].
Qed.

Lemma generator_startup_separate m b size : generator_startup m -> 0<size ->
  Mem.range_perm m b 0 size Cur Freeable ->
  b<>generator_zero_block /\ forall h,b<>generator_table_block h.
Proof.
  intros [Zero Tables] Size Owned;split.
  - apply (generator_zero_global_separate m b Zero);apply Owned;clear -Size;lia.
  - intros h Same;destruct (Tables h) as [Table Bounds];rewrite <-Same in Bounds.
    destruct (proj1 (Bounds 0 Cur Freeable) (Owned 0 ltac:(clear -Size;lia))) as [_ Order];inversion Order.
Qed.

Lemma generator_startup_lframe m mf P : generator_startup m ->
  mem_forward m mf -> lframe P m mf ->
  (forall pos,P generator_zero_block pos) ->
  (forall h pos,P (generator_table_block h) pos) -> generator_startup mf.
Proof.
  intros [Zero Tables] Forward Frame OutsideZero OutsideTables.
  pose proof (generator_zero_global_valid m Zero) as ZeroValid.
  destruct Zero as [Storage Bounds].
  assert (StorageF:scalar_at mf generator_zero_block 0
    [Integers.Int64.zero;Integers.Int64.zero;Integers.Int64.zero;Integers.Int64.zero]).
  { eapply scalar_at_lframe;[exact Storage|exact Frame|exact OutsideZero]. }
  split.
  - split;[exact StorageF|].
    eapply readonly_bounds_transport;[exact ZeroValid|exact Bounds|exact Forward|].
    destruct StorageF as (_ & _ & _ & _ & Read & _);exact Read.
  - intro h;destruct (Tables h) as [Table TableBounds].
    pose proof (generator_table_rep_lframe h m mf P Table Frame (OutsideTables h)) as TableF.
    split;[exact TableF|];eapply readonly_bounds_transport;
      [exact (proj1 Table)|exact TableBounds|exact Forward|exact (proj1 (proj2 TableF))].
Qed.

Lemma generator_startup_readonly m mf : generator_startup m ->
  readonly_preserved m mf -> generator_startup mf.
Proof.
  intros [Zero Tables] [_ Unchanged];split.
  - apply (generator_zero_global_unchanged m mf Zero).
    eapply Mem.unchanged_on_implies;[exact Unchanged|].
    intros b pos At Valid;subst b;split;[exact Valid|].
    exact (readonly_bounds_not_writable _ _ _ _ (proj2 Zero) pos).
  - intro h;apply (generator_table_state_unchanged h m mf);[|apply Tables].
    eapply Mem.unchanged_on_implies;[exact Unchanged|].
    intros b pos At Valid;subst b;split;[exact Valid|].
    exact (readonly_bounds_not_writable _ _ _ _ (proj2 (Tables h)) pos).
Qed.

Lemma generator_startup_call m mf fd args trace result P :
  generator_startup m -> Clight2.eval_funcall secp_ge m fd args trace mf result ->
  lframe P m mf -> (forall pos,P generator_zero_block pos) ->
  (forall h pos,P (generator_table_block h) pos) -> generator_startup mf.
Proof.
  intros Ready Call Frame Zero Tables;eapply generator_startup_lframe;
    [exact Ready| |exact Frame|exact Zero|exact Tables].
  exact (proj1 (proj2 (clight_exec_readonly_readback secp_ge) _ _ _ _ _ _ Call)).
Qed.
