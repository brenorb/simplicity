(** Application-jet local contract with an explicit environment footprint.
    The jets that read the environment after writing part of their output
    (every multi-word getter) need the environment bytes they read to be
    disjoint from the bytes the call may modify.  [application_jet_local_spec_sep]
    states this as a premise: the footprint of the abstract environment's
    physical representation avoids the written output words and the
    destination frame's cursor field.  The environment representation predicate
    reports its own footprint as a list of byte intervals; otherwise the
    contract is that of [jet_application_contract.v]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Translate.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition out_low (edge cursor count : Z) : Z := edge + 8 * ((cursor - count) / 64).
Definition out_high (edge cursor : Z) : Z := write_word_address edge cursor + 8.

(** A byte interval [lo, hi) of block [b] is disjoint from everything a call
    writing [count] cells at [cursor] can modify. *)
Definition out_sep (bf : block) (base : Z) (bw : block) (edge cursor count : Z)
    (b : block) (lo hi : Z) : Prop :=
  (b <> bf \/ hi <= base + 8 \/ base + 16 <= lo) /\
  (b <> bw \/ hi <= out_low edge cursor count \/ out_high edge cursor <= lo).

Definition application_jet_local_spec_sep (f : function) (ge : Clight.genv) (E : Set)
    (A B : Ty) (env_rep : mem -> val -> E -> list (block * Z * Z) -> Prop)
    (spec : A -> E -> option B) : Prop :=
  forall logical_env env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A) fp,
    env_rep m env logical_env fp ->
    Forall (fun '(b, lo, hi) => out_sep bd dbase bw outedge cursor (Z.of_nat (bitSize B)) b lo hi) fp ->
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    exists mf value,
      spec a logical_env = Some value /\
      Clight2.eval_funcall ge m (Internal f)
        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
        E0 mf (Vint Int.one) /\
      frame_output_cells_at mf bw outedge cursor (encode value) /\
      write_prefix_at m mf bw outedge cursor /\
      frame_fields_at mf bd dbase bw outedge (cursor - Z.of_nat (bitSize B)) /\
      (forall chunk b ofs, Mem.valid_block m b ->
        (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
        (b <> bw \/
          ofs + size_chunk chunk <= outedge + 8 * ((cursor - Z.of_nat (bitSize B)) / 64) \/
          write_word_address outedge cursor + 8 <= ofs) ->
        Mem.load chunk mf b ofs = Mem.load chunk m b ofs).

(** A sub-write (fewer cells, lower cursor) of a larger write inherits the
    separation of the larger footprint. *)
Lemma out_sep_sub bf base bw edge cursor count cursor' count' b lo hi :
  0 < count' -> count' <= cursor' -> cursor' <= cursor -> cursor - count <= cursor' - count' ->
  out_sep bf base bw edge cursor count b lo hi ->
  out_sep bf base bw edge cursor' count' b lo hi.
Proof.
  intros HC HC' HCur HLow [Hf Hw]. split; [exact Hf|].
  unfold out_low, out_high, write_word_address in *.
  destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw| |].
  - right; left.
    pose proof (Z.div_le_mono (cursor - count) (cursor' - count') 64 ltac:(lia) HLow). lia.
  - right; right.
    pose proof (Z.div_le_mono (cursor' - 1) (cursor - 1) 64 ltac:(lia) ltac:(lia)). lia.
Qed.
