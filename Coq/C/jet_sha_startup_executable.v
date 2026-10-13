(** SHA-unit jets run on freshly constructed frames in any memory satisfying
    the startup invariant, for every input.

    [jet_frames_constructible] builds the frames in fresh blocks; the setup
    is forward and leaves the five state objects untouched, so the invariant
    still holds when the jet is called, and the per-jet contract
    re-establishes it afterwards.  Starting from the initial memory of the
    SHA translation unit no assumption about C global objects, frames or
    inputs remains: the caller-side premises of these contracts are all
    established here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Globalenvs Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.BitMachine Simplicity.Translate.
Require Import C.jet_partial C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_write_layout C.jet_encoding.
Require Import C.jet_frame_constructible.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local.
Require Import C.jet_sha_uchars_exec C.jet_sha_add_n_exec.
Require Import C.jet_clight_forward C.jet_sha_initial_globals.
Require Import C.jet_sha_startup_globals C.jet_sha_startup_state.
Require Import C.jet_sha_startup_setup.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

(** The frame construction preserves the invariant. *)
Theorem sha_startup_frames_constructible (m0 : mem) (cells : list Cell) (count : Z) :
  sha_startup_state m0 ->
  Z.of_nat (length cells) <= Int64.max_unsigned ->
  0 <= count <= Int64.max_unsigned ->
  exists m bd bs bi bw edge,
    sha_startup_state m /\
    frame_base_valid 0 /\ (8 | 0) /\
    frame_fields_at m bs 0 bi edge 0 /\
    frame_input_cells_at m bi edge 0 cells /\
    write_frame_at m bd 0 bw 0 count count /\
    (forall b, Mem.valid_block m0 b ->
      Mem.valid_block m b /\ b <> bd /\ b <> bw /\
      forall chunk ofs, Mem.load chunk m b ofs = Mem.load chunk m0 b ofs).
Proof.
  intros HState HCells HCount.
  destruct (jet_frames_constructible m0 cells count HCells HCount)
    as (m & bd & bs & bi & bw & edge & HBase & HAlign & HFields & HInput & HOutput & _ & HOld).
  exists m, bd, bs, bi, bw, edge.
  split.
  { eapply sha_startup_state_preserved; [exact HState| |].
    - intros b Hb. destruct (HOld b Hb) as (Hv & _ & _ & _ & _ & _ & HPerm).
      split; [exact Hv|]. intros ofs p HP. exact (HPerm ofs Max p HP).
    - intros chunk b ofs HIn.
      destruct (HOld b (sha_state_blocks_valid m0 b HState HIn)) as (_ & _ & _ & _ & _ & HL & _).
      exact (HL chunk ofs). }
  repeat (split; [assumption|]).
  intros b Hb. destruct (HOld b Hb) as (Hv & Nd & _ & _ & Nw & HL & _).
  repeat (split; [assumption|]). exact HL.
Qed.

Definition sha_total_runs_on_fresh_frames (f : function) (A B : Ty) (spec : A -> B) : Prop :=
  forall (a : A) (env : val) (m0 : mem),
  sha_startup_state m0 ->
  exists m bd bs bw mf,
    Clight2.eval_funcall sha_ge m (Internal f)
      [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw 0 (Z.of_nat (bitSize B)) (encode (spec a)) /\
    sha_startup_state mf /\
    (forall b chunk ofs, Mem.valid_block m0 b ->
      Mem.load chunk mf b ofs = Mem.load chunk m0 b ofs).

Theorem sha_startup_total_executable f A B spec :
  sha_startup_total_spec f A B spec ->
  Z.of_nat (bitSize A) <= Int64.max_unsigned ->
  Z.of_nat (bitSize B) <= Int64.max_unsigned ->
  sha_total_runs_on_fresh_frames f A B spec.
Proof.
  intros HSpec HA HB a env m0 HState.
  destruct (sha_startup_frames_constructible m0 (encode a) (Z.of_nat (bitSize B)) HState)
    as (m & bd & bs & bi & bw & edge & HState' & HBase & HAlign & HFields & HInput & HOutput & HOld).
  { rewrite encode_length. exact HA. }
  { lia. }
  destruct (HSpec env m bd 0 bs 0 bi bw edge 0 (Z.of_nat (bitSize B)) 0 a
    HState' HBase HAlign HFields ltac:(lia) ltac:(lia) HInput HOutput)
    as (mf & HCall & HOut & _ & _ & HLoads & HFinal).
  exists m, bd, bs, bw, mf.
  split; [exact HCall|]. split; [exact HOut|]. split; [exact HFinal|].
  intros b chunk ofs Hb. destruct (HOld b Hb) as (Hv & Nd & Nw & HL).
  rewrite HLoads; [exact (HL chunk ofs)|exact Hv|left; exact Nd|left; exact Nw].
Qed.

(** Assertion jets: the call returns the assertion's verdict; on success the
    output frame holds the encoded result. *)
Definition sha_partial_runs_on_fresh_frames (f : function) (A B : Ty)
    (spec : A -> option B) : Prop :=
  forall (a : A) (env : val) (m0 : mem),
  sha_startup_state m0 ->
  exists m bd bs bw mf,
    Clight2.eval_funcall sha_ge m (Internal f)
      [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf
      (jet_partial_return (spec a)) /\
    (match spec a with
     | Some b => frame_output_cells_at mf bw 0 (Z.of_nat (bitSize B)) (encode b)
     | None => True
     end) /\
    sha_startup_state mf /\
    (forall b chunk ofs, Mem.valid_block m0 b ->
      Mem.load chunk mf b ofs = Mem.load chunk m0 b ofs).

Theorem sha_startup_partial_executable f A B spec :
  sha_startup_partial_spec f A B spec ->
  Z.of_nat (bitSize A) <= Int64.max_unsigned ->
  Z.of_nat (bitSize B) <= Int64.max_unsigned ->
  sha_partial_runs_on_fresh_frames f A B spec.
Proof.
  intros HSpec HA HB a env m0 HState.
  destruct (sha_startup_frames_constructible m0 (encode a) (Z.of_nat (bitSize B)) HState)
    as (m & bd & bs & bi & bw & edge & HState' & HBase & HAlign & HFields & HInput & HOutput & HOld).
  { rewrite encode_length. exact HA. }
  { lia. }
  destruct (HSpec env m bd 0 bs 0 bi bw edge 0 (Z.of_nat (bitSize B)) 0 a
    HState' HBase HAlign HFields ltac:(lia) ltac:(lia) HInput HOutput)
    as (mf & HCall & HResult & HLoads & HFinal).
  exists m, bd, bs, bw, mf.
  split; [exact HCall|]. split.
  { destruct (spec a) as [b|]; [exact (proj1 HResult)|exact I]. }
  split; [exact HFinal|].
  intros b chunk ofs Hb. destruct (HOld b Hb) as (Hv & Nd & Nw & HL).
  rewrite HLoads; [exact (HL chunk ofs)|exact Hv|left; exact Nd|left; exact Nw].
Qed.
