(** The startup invariant along whole caller lifecycles.

    A lifecycle starts in the initial memory of the SHA translation unit and
    interleaves, in any order and number,

    - caller memory operations on blocks the caller allocated
      (allocation, stores, byte stores, frees), and
    - *any* terminating Clight execution of a SHA-unit jet called on frames
      satisfying the jet's frame premises (for the environment-reading jets,
      also its environment relation).

    The jet steps are stated for an arbitrary big-step execution of the call,
    not for the particular final memory produced by the contract: determinism
    of Clight ([jet_clight_determinism.eval_funcall_unique], which rests on
    CompCert's external-call determinism) identifies the two.  The theorem is
    that the invariant holds at every point of every lifecycle, so the state
    premise of each jet is discharged at each call, however the jets are
    sequenced by the caller. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Globalenvs Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_partial C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_write_layout C.jet_encoding C.jet_application_sep.
Require Import C.jet_clight_determinism.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local.
Require Import C.jet_sha_uchars_exec C.jet_sha_add_n_exec.
Require Import C.jet_clight_forward C.jet_sha_initial_globals.
Require Import C.jet_sha_startup_globals C.jet_sha_startup_state.
Require Import C.jet_sha_startup_setup.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Definition jet_call_args (bd : block) (dbase : Z) (bs : block) (sbase : Z) (env : val) : list val :=
  [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env].

(** Every execution of a call covered by a contract over the invariant ends
    in a memory satisfying the invariant. *)
Theorem sha_total_call_preserves f A B spec :
  sha_startup_total_spec f A B spec ->
  forall env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A) t mf v,
    sha_startup_state m ->
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    Clight2.eval_funcall sha_ge m (Internal f) (jet_call_args bd dbase bs sbase env) t mf v ->
    t = E0 /\ v = Vint Int.one /\ sha_startup_state mf /\
    frame_output_cells_at mf bw outedge cursor (encode (spec a)).
Proof.
  intros HSpec env m bd dbase bs sbase bi bw edge outedge cursor rc a t mf v
    HState HBase HAlign HFields HCursor HMax HInput HOutput HExec.
  destruct (HSpec env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HState HBase HAlign HFields HCursor HMax HInput HOutput)
    as (mf0 & HCall & HOut & _ & _ & _ & HFinal).
  destruct (eval_funcall_unique jets_sha.prog _ _ _ _ _ _ _ _ HCall HExec) as (-> & -> & ->).
  split; [reflexivity|split; [reflexivity|split; assumption]].
Qed.

Theorem sha_partial_call_preserves f A B spec :
  sha_startup_partial_spec f A B spec ->
  forall env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A) t mf v,
    sha_startup_state m ->
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    Clight2.eval_funcall sha_ge m (Internal f) (jet_call_args bd dbase bs sbase env) t mf v ->
    t = E0 /\ v = jet_partial_return (spec a) /\ sha_startup_state mf.
Proof.
  intros HSpec env m bd dbase bs sbase bi bw edge outedge cursor rc a t mf v
    HState HBase HAlign HFields HCursor HMax HInput HOutput HExec.
  destruct (HSpec env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HState HBase HAlign HFields HCursor HMax HInput HOutput)
    as (mf0 & HCall & _ & _ & HFinal).
  destruct (eval_funcall_unique jets_sha.prog _ _ _ _ _ _ _ _ HCall HExec) as (-> & -> & ->).
  split; [reflexivity|split; [reflexivity|exact HFinal]].
Qed.

Theorem sha_application_call_preserves f (E : Set) A B env_rep spec :
  sha_startup_application_spec f E A B env_rep spec ->
  forall logical_env env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A) fp t mf v,
    sha_startup_state m ->
    env_rep m env logical_env fp ->
    Forall (fun '(b, lo, hi) => out_sep bd dbase bw outedge cursor (Z.of_nat (bitSize B)) b lo hi) fp ->
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    Clight2.eval_funcall sha_ge m (Internal f) (jet_call_args bd dbase bs sbase env) t mf v ->
    t = E0 /\ v = Vint Int.one /\ sha_startup_state mf.
Proof.
  intros HSpec logical_env env m bd dbase bs sbase bi bw edge outedge cursor rc a fp t mf v
    HState HRep HSep HBase HAlign HFields HCursor HMax HInput HOutput HExec.
  destruct (HSpec logical_env env m bd dbase bs sbase bi bw edge outedge cursor rc a fp
    HState HRep HSep HBase HAlign HFields HCursor HMax HInput HOutput)
    as (mf0 & value & _ & HCall & _ & _ & _ & _ & HFinal).
  destruct (eval_funcall_unique jets_sha.prog _ _ _ _ _ _ _ _ HCall HExec) as (-> & -> & ->).
  split; [reflexivity|split; [reflexivity|exact HFinal]].
Qed.

(** ** Lifecycles *)

Inductive sha_lifecycle : mem -> list block -> Prop :=
| life_initial : forall m,
    Genv.init_mem jets_sha.prog = Some m -> sha_lifecycle m []
| life_alloc : forall m owned lo hi mf fresh,
    sha_lifecycle m owned -> Mem.alloc m lo hi = (mf, fresh) ->
    sha_lifecycle mf (fresh :: owned)
| life_store : forall m owned chunk b ofs value mf,
    sha_lifecycle m owned -> In b owned ->
    Mem.store chunk m b ofs value = Some mf -> sha_lifecycle mf owned
| life_storebytes : forall m owned b ofs bytes mf,
    sha_lifecycle m owned -> In b owned ->
    Mem.storebytes m b ofs bytes = Some mf -> sha_lifecycle mf owned
| life_free : forall m owned b lo hi mf,
    sha_lifecycle m owned -> In b owned ->
    Mem.free m b lo hi = Some mf -> sha_lifecycle mf owned
| life_total_jet : forall m owned f (A B : Ty) spec env bd dbase bs sbase bi bw edge outedge cursor
      read_cursor (a : A) t mf v,
    sha_lifecycle m owned ->
    sha_startup_total_spec f A B spec ->
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    Clight2.eval_funcall sha_ge m (Internal f) (jet_call_args bd dbase bs sbase env) t mf v ->
    sha_lifecycle mf owned
| life_partial_jet : forall m owned f (A B : Ty) spec env bd dbase bs sbase bi bw edge outedge cursor
      read_cursor (a : A) t mf v,
    sha_lifecycle m owned ->
    sha_startup_partial_spec f A B spec ->
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    Clight2.eval_funcall sha_ge m (Internal f) (jet_call_args bd dbase bs sbase env) t mf v ->
    sha_lifecycle mf owned
| life_application_jet : forall m owned f (E : Set) (A B : Ty) env_rep spec (logical_env : E) env
      bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A) fp t mf v,
    sha_lifecycle m owned ->
    sha_startup_application_spec f E A B env_rep spec ->
    env_rep m env logical_env fp ->
    Forall (fun '(b, lo, hi) => out_sep bd dbase bw outedge cursor (Z.of_nat (bitSize B)) b lo hi) fp ->
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    Clight2.eval_funcall sha_ge m (Internal f) (jet_call_args bd dbase bs sbase env) t mf v ->
    sha_lifecycle mf owned.

Theorem sha_lifecycle_state m owned :
  sha_lifecycle m owned ->
  sha_startup_state m /\ (forall b, In b owned -> ~ In b sha_state_blocks).
Proof.
  intros HLife. induction HLife as
    [m HInit
    |m owned lo hi mf fresh _ IH HA
    |m owned chunk b ofs value mf _ IH HOwned HS
    |m owned b ofs bytes mf _ IH HOwned HS
    |m owned b lo hi mf _ IH HOwned HF
    |m owned f A B spec env bd dbase bs sbase bi bw edge outedge cursor rc a t mf v _ IH
       HSpec HBase HAlign HFields HCursor HMax HInput HOutput HExec
    |m owned f A B spec env bd dbase bs sbase bi bw edge outedge cursor rc a t mf v _ IH
       HSpec HBase HAlign HFields HCursor HMax HInput HOutput HExec
    |m owned f E A B env_rep spec logical_env env bd dbase bs sbase bi bw edge outedge cursor
       rc a fp t mf v _ IH HSpec HRep HSep HBase HAlign HFields HCursor HMax HInput HOutput HExec].
  - split; [exact (sha_startup_state_initialized m HInit)|intros b []].
  - destruct IH as [HState HOwners].
    destruct (sha_startup_state_alloc m mf lo hi fresh HState HA) as [HFinal HFresh].
    split; [exact HFinal|].
    intros b [<-|HB]; [exact HFresh|exact (HOwners b HB)].
  - destruct IH as [HState HOwners]. split; [|exact HOwners].
    eapply sha_startup_state_store; [exact HState|exact (HOwners b HOwned)|exact HS].
  - destruct IH as [HState HOwners]. split; [|exact HOwners].
    eapply sha_startup_state_storebytes; [exact HState|exact (HOwners b HOwned)|exact HS].
  - destruct IH as [HState HOwners]. split; [|exact HOwners].
    eapply sha_startup_state_free; [exact HState|exact (HOwners b HOwned)|exact HF].
  - destruct IH as [HState HOwners]. split; [|exact HOwners].
    exact (proj1 (proj2 (proj2 (sha_total_call_preserves f A B spec HSpec env m bd dbase bs sbase
      bi bw edge outedge cursor rc a t mf v HState HBase HAlign HFields HCursor HMax HInput
      HOutput HExec)))).
  - destruct IH as [HState HOwners]. split; [|exact HOwners].
    exact (proj2 (proj2 (sha_partial_call_preserves f A B spec HSpec env m bd dbase bs sbase
      bi bw edge outedge cursor rc a t mf v HState HBase HAlign HFields HCursor HMax HInput
      HOutput HExec))).
  - destruct IH as [HState HOwners]. split; [|exact HOwners].
    exact (proj2 (proj2 (sha_application_call_preserves f E A B env_rep spec HSpec logical_env
      env m bd dbase bs sbase bi bw edge outedge cursor rc a fp t mf v HState HRep HSep HBase
      HAlign HFields HCursor HMax HInput HOutput HExec))).
Qed.
