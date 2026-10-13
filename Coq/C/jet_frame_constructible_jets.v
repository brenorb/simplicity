(** Every frame-only jet contract is executable on every input.

    Combining [jet_frames_constructible] with the shared contracts: for any
    function proved against [jet_local_spec] or [jet_separated_local_spec],
    any input [a : A], any environment argument and any starting memory,
    frames can be set up in fresh blocks so that the actual C function runs
    to completion with result 1 and leaves [encode (spec a)] in the output
    frame, without changing any load from a block that existed before the
    setup.  The size bounds are the contracts' own representability bounds. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Import Simplicity.Ty Simplicity.BitMachine Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_partial C.jet_context_separated C.jet_frame_constructible.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Definition jet_runs_on_fresh_frames (f : function) (A B : Ty) (spec : A -> B) : Prop :=
  forall (a : A) (env : val) (m0 : mem),
  exists m bd bs bw mf,
    (forall b chunk ofs, Mem.valid_block m0 b ->
      Mem.load chunk m b ofs = Mem.load chunk m0 b ofs) /\
    Clight2.eval_funcall ge0 m (Internal f)
      [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw 0 (Z.of_nat (bitSize B)) (encode (spec a)) /\
    (forall b chunk ofs, Mem.valid_block m0 b ->
      Mem.load chunk mf b ofs = Mem.load chunk m0 b ofs).

Theorem jet_separated_local_spec_executable f A B spec :
  jet_separated_local_spec f A B spec ->
  Z.of_nat (bitSize A) <= Int64.max_unsigned ->
  Z.of_nat (bitSize B) <= Int64.max_unsigned ->
  jet_runs_on_fresh_frames f A B spec.
Proof.
  intros HSpec HA HB a env m0.
  destruct (jet_frames_constructible m0 (encode a) (Z.of_nat (bitSize B)))
    as (m & bd & bs & bi & bw & edge & HBase & HAlign & HFields & HInput & HOutput &
        (Ndbi & Ndbw & Ndbs & Nbibw & Nsbi & Nsbw) & HOld).
  { rewrite encode_length. exact HA. }
  { lia. }
  destruct (HSpec env m bd 0 bs 0 bi bw edge 0 (Z.of_nat (bitSize B)) 0 a
    HBase HAlign HFields ltac:(lia) ltac:(lia) HInput HOutput
    (conj Ndbi (or_introl Nbibw)))
    as (mf & HCall & HOut & _ & _ & HLoads).
  exists m, bd, bs, bw, mf.
  split; [intros b chunk ofs Hb; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (HOld b Hb)))))) chunk ofs)|].
  split; [exact HCall|]. split; [exact HOut|].
  intros b chunk ofs Hb.
  destruct (HOld b Hb) as (Hvalid & Nd & _ & _ & Nw & HL & _).
  rewrite HLoads; [exact (HL chunk ofs)|exact Hvalid|left; exact Nd|left; exact Nw].
Qed.

Theorem jet_local_spec_executable f A B spec :
  jet_local_spec f A B spec ->
  Z.of_nat (bitSize A) <= Int64.max_unsigned ->
  Z.of_nat (bitSize B) <= Int64.max_unsigned ->
  jet_runs_on_fresh_frames f A B spec.
Proof.
  intros HSpec. apply jet_separated_local_spec_executable.
  apply jet_local_spec_to_separated. exact HSpec.
Qed.

(** Assertion jets: the call returns the assertion's verdict; on success the
    output frame holds the encoded result. *)
Definition jet_partial_runs_on_fresh_frames (f : function) (A B : Ty)
    (spec : A -> option B) : Prop :=
  forall (a : A) (env : val) (m0 : mem),
  exists m bd bs bw mf,
    (forall b chunk ofs, Mem.valid_block m0 b ->
      Mem.load chunk m b ofs = Mem.load chunk m0 b ofs) /\
    Clight2.eval_funcall ge0 m (Internal f)
      [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf
      (jet_partial_return (spec a)) /\
    (match spec a with
     | Some b => frame_output_cells_at mf bw 0 (Z.of_nat (bitSize B)) (encode b)
     | None => True
     end) /\
    (forall b chunk ofs, Mem.valid_block m0 b ->
      Mem.load chunk mf b ofs = Mem.load chunk m0 b ofs).

Theorem jet_partial_local_spec_executable f A B spec :
  jet_partial_local_spec f A B spec ->
  Z.of_nat (bitSize A) <= Int64.max_unsigned ->
  Z.of_nat (bitSize B) <= Int64.max_unsigned ->
  jet_partial_runs_on_fresh_frames f A B spec.
Proof.
  intros HSpec HA HB a env m0.
  destruct (jet_frames_constructible m0 (encode a) (Z.of_nat (bitSize B)))
    as (m & bd & bs & bi & bw & edge & HBase & HAlign & HFields & HInput & HOutput & _ & HOld).
  { rewrite encode_length. exact HA. }
  { lia. }
  destruct (HSpec env m bd 0 bs 0 bi bw edge 0 (Z.of_nat (bitSize B)) 0 a
    HBase HAlign HFields ltac:(lia) ltac:(lia) HInput HOutput)
    as (mf & HCall & HResult & HLoads).
  exists m, bd, bs, bw, mf.
  split; [intros b chunk ofs Hb; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (HOld b Hb)))))) chunk ofs)|].
  split; [exact HCall|]. split.
  { destruct (spec a) as [b|]; [exact (proj1 HResult)|exact I]. }
  intros b chunk ofs Hb.
  destruct (HOld b Hb) as (Hvalid & Nd & _ & _ & Nw & HL & _).
  rewrite HLoads; [exact (HL chunk ofs)|exact Hvalid|left; exact Nd|left; exact Nw].
Qed.
