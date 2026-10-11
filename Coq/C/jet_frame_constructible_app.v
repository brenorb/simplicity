(** Executability of environment-reading jets on fresh frames.

    An application contract additionally takes a relation between C memory
    and a logical environment.  Building the two frames in fresh blocks
    extends the memory without changing any load or adding any permission on
    existing blocks ([memory_extension]).  If the environment relation is
    stable under such extensions (it is for relations that only observe loads
    of the environment's own blocks), then from any memory representing a
    logical environment the jet runs on fresh frames for every input and
    yields exactly the canonical result for that environment.  For relations
    with a separation footprint the blocks of the footprint must exist in the
    starting memory (a stored pointer does not by itself make its target
    block valid).  The relation itself is the caller's input and is not
    constructed here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Import Simplicity.Ty Simplicity.BitMachine Simplicity.Translate.
Require Import C.jet_partial C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_encoding.
Require Import C.jet_application_contract C.jet_application_sep C.jet_application_partial.
Require Import C.jet_frame_constructible.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Definition memory_extension (m m' : mem) : Prop :=
  forall b, Mem.valid_block m b ->
    Mem.valid_block m' b /\
    (forall chunk ofs, Mem.load chunk m' b ofs = Mem.load chunk m b ofs) /\
    (forall ofs k p, Mem.perm m' b ofs k p -> Mem.perm m b ofs k p).

(** A load that succeeds keeps its value in any extension. *)
Lemma memory_extension_load m m' chunk b ofs v :
  memory_extension m m' -> Mem.load chunk m b ofs = Some v -> Mem.load chunk m' b ofs = Some v.
Proof.
  intros HExt HL.
  assert (HV : Mem.valid_block m b).
  { eapply Mem.perm_valid_block with (ofs := ofs) (k := Cur) (p := Readable).
    apply (Mem.load_valid_access _ _ _ _ _ HL). destruct chunk; cbn; lia. }
  rewrite (proj1 (proj2 (HExt b HV))). exact HL.
Qed.

Definition env_rep_stable {E : Set} (rep : mem -> val -> E -> Prop) : Prop :=
  forall m m' env e, memory_extension m m' -> rep m env e -> rep m' env e.

Definition env_rep_sep_stable {E : Set}
    (rep : mem -> val -> E -> list (block * Z * Z) -> Prop) : Prop :=
  forall m m' env e fp, memory_extension m m' -> rep m env e fp -> rep m' env e fp.

Lemma frames_extension (m0 : mem) (cells : list Cell) (count : Z) :
  Z.of_nat (length cells) <= Int64.max_unsigned ->
  0 <= count <= Int64.max_unsigned ->
  exists m bd bs bi bw edge,
    memory_extension m0 m /\
    frame_base_valid 0 /\ (8 | 0) /\
    frame_fields_at m bs 0 bi edge 0 /\
    frame_input_cells_at m bi edge 0 cells /\
    write_frame_at m bd 0 bw 0 count count /\
    (forall b, Mem.valid_block m0 b -> b <> bd /\ b <> bw).
Proof.
  intros HCells HCount.
  destruct (jet_frames_constructible m0 cells count HCells HCount)
    as (m & bd & bs & bi & bw & edge & HBase & HAlign & HFields & HInput & HOutput & _ & HOld).
  exists m, bd, bs, bi, bw, edge.
  split.
  { intros b Hb. destruct (HOld b Hb) as (Hv & _ & _ & _ & _ & HL & HP).
    split; [exact Hv|]. split; [exact HL|exact HP]. }
  repeat (split; [assumption|]).
  intros b Hb. destruct (HOld b Hb) as (_ & Nd & _ & _ & Nw & _). split; assumption.
Qed.

Definition application_runs_on_fresh_frames (f : function) (ge : Clight.genv) (E : Set)
    (A B : Ty) (env_rep : mem -> val -> E -> Prop) (spec : A -> E -> option B) : Prop :=
  forall (a : A) (logical_env : E) (env : val) (m0 : mem),
  env_rep m0 env logical_env ->
  exists m bd bs bw mf value,
    spec a logical_env = Some value /\
    Clight2.eval_funcall ge m (Internal f)
      [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw 0 (Z.of_nat (bitSize B)) (encode value).

Definition application_sep_runs_on_fresh_frames (f : function) (ge : Clight.genv) (E : Set)
    (A B : Ty) (env_rep : mem -> val -> E -> list (block * Z * Z) -> Prop)
    (spec : A -> E -> option B) : Prop :=
  forall (a : A) (logical_env : E) (env : val) (m0 : mem) fp,
  env_rep m0 env logical_env fp ->
  Forall (fun '(b, _, _) => Mem.valid_block m0 b) fp ->
  exists m bd bs bw mf value,
    spec a logical_env = Some value /\
    Clight2.eval_funcall ge m (Internal f)
      [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw 0 (Z.of_nat (bitSize B)) (encode value).

Definition application_partial_runs_on_fresh_frames (f : function) (ge : Clight.genv)
    (E : Set) (A B : Ty) (env_rep : mem -> val -> E -> Prop)
    (spec : A -> E -> option B) : Prop :=
  forall (a : A) (logical_env : E) (env : val) (m0 : mem),
  env_rep m0 env logical_env ->
  exists m bd bs bw mf,
    Clight2.eval_funcall ge m (Internal f)
      [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf
      (jet_partial_return (spec a logical_env)) /\
    match spec a logical_env with
    | Some b => frame_output_cells_at mf bw 0 (Z.of_nat (bitSize B)) (encode b)
    | None => True
    end.

Section Application.
Variables (f : function) (ge : Clight.genv) (E : Set) (A B : Ty).
Hypothesis HA : Z.of_nat (bitSize A) <= Int64.max_unsigned.
Hypothesis HB : Z.of_nat (bitSize B) <= Int64.max_unsigned.

Theorem application_jet_local_spec_executable
    (env_rep : mem -> val -> E -> Prop) (spec : A -> E -> option B) :
  application_jet_local_spec f ge E A B env_rep spec ->
  env_rep_stable env_rep ->
  application_runs_on_fresh_frames f ge E A B env_rep spec.
Proof.
  intros HSpec HStable a e env m0 HRep.
  destruct (frames_extension m0 (encode a) (Z.of_nat (bitSize B)))
    as (m & bd & bs & bi & bw & edge & HExt & HBase & HAlign & HFields & HInput & HOutput & _).
  { rewrite encode_length. exact HA. }
  { lia. }
  destruct (HSpec e env m bd 0 bs 0 bi bw edge 0 (Z.of_nat (bitSize B)) 0 a
    (HStable _ _ _ _ HExt HRep) HBase HAlign HFields ltac:(lia) ltac:(lia) HInput HOutput)
    as (mf & value & HValue & HCall & HOut & _).
  exists m, bd, bs, bw, mf, value. repeat split; assumption.
Qed.

Theorem application_jet_local_spec_sep_executable
    (env_rep : mem -> val -> E -> list (block * Z * Z) -> Prop) (spec : A -> E -> option B) :
  application_jet_local_spec_sep f ge E A B env_rep spec ->
  env_rep_sep_stable env_rep ->
  application_sep_runs_on_fresh_frames f ge E A B env_rep spec.
Proof.
  intros HSpec HStable a e env m0 fp HRep HValid.
  destruct (frames_extension m0 (encode a) (Z.of_nat (bitSize B)))
    as (m & bd & bs & bi & bw & edge & HExt & HBase & HAlign & HFields & HInput & HOutput & HFresh).
  { rewrite encode_length. exact HA. }
  { lia. }
  pose proof (HStable _ _ _ _ _ HExt HRep) as HRep'.
  assert (HSep : Forall (fun '(b, lo, hi) =>
      out_sep bd 0 bw 0 (Z.of_nat (bitSize B)) (Z.of_nat (bitSize B)) b lo hi) fp).
  { eapply Forall_impl; [|exact HValid]. intros [[b lo] hi] Hb.
    destruct (HFresh b Hb) as [Nd Nw]. split; left; assumption. }
  destruct (HSpec e env m bd 0 bs 0 bi bw edge 0 (Z.of_nat (bitSize B)) 0 a fp
    HRep' HSep HBase HAlign HFields ltac:(lia) ltac:(lia) HInput HOutput)
    as (mf & value & HValue & HCall & HOut & _).
  exists m, bd, bs, bw, mf, value. repeat split; assumption.
Qed.

Theorem application_jet_partial_spec_executable
    (env_rep : mem -> val -> E -> Prop) (spec : A -> E -> option B) :
  application_jet_partial_spec f ge E A B env_rep spec ->
  env_rep_stable env_rep ->
  application_partial_runs_on_fresh_frames f ge E A B env_rep spec.
Proof.
  intros HSpec HStable a e env m0 HRep.
  destruct (frames_extension m0 (encode a) (Z.of_nat (bitSize B)))
    as (m & bd & bs & bi & bw & edge & HExt & HBase & HAlign & HFields & HInput & HOutput & _).
  { rewrite encode_length. exact HA. }
  { lia. }
  destruct (HSpec e env m bd 0 bs 0 bi bw edge 0 (Z.of_nat (bitSize B)) 0 a
    (HStable _ _ _ _ HExt HRep) HBase HAlign HFields ltac:(lia) ltac:(lia) HInput HOutput)
    as (mf & HCall & HResult & _).
  exists m, bd, bs, bw, mf. split; [exact HCall|].
  destruct (spec a e) as [b|]; [exact (proj1 HResult)|exact I].
Qed.
End Application.
