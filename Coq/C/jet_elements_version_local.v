(** Direct canonical public version-jet contract. The environment projection
    requires only the initial physical fields this primitive actually reads. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Memory.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Import C.jet_elements_prim.
Require Import C.jet_application_contract C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_version_canonical.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_version_env_rep (m : mem) (env : val) (environment : Elements.env) : Prop :=
  exists be ebase bt txbase version,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase <= Ptrofs.max_unsigned /\ 0 <= txbase /\ txbase + 760 <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) /\
    Mem.load Mint64 m bt (txbase + 720) = Some (Vlong version) /\
    Int64.unsigned version = Int.unsigned (sigTxVersion (Elements.envTx environment)).

Theorem elements_version_local_spec :
  application_jet_local_spec f_simplicity_version elements_ge Elements.env Ty.Unit Word32
    elements_version_env_rep
    (fun a environment => @elements_transaction_version_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor []
    (be & ebase & bt & txbase & version & HEnvVal & HE & HT & HM & HEnv & HVersion & HR)
    HB HA [HSedge HSoff] _ _ _ HFrame.
  subst env.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  change (write_frame_at m bd dbase bw outedge cursor 32) in HFrame.
  destruct (elements_transaction_version_canonical_spec environment m bd dbase bs sbase bw outedge cursor
      be ebase bt txbase version bytes HB HA HBytes HE HT HM HEnv HVersion HR HFrame)
    as (mf & value & HSpec & HCall & HOutput & HPrefix & HFields & HMemory).
  exists mf, value. split; [exact HSpec|]. split; [exact HCall|].
  split; [exact HOutput|]. split; [exact HPrefix|]. split; [exact HFields|].
  intros chunk b ofs HV Hd Hw. apply HMemory; [exact HV|exact Hd|].
  destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw|right; left|right; right; exact Hw].
  assert (HC : 32 <= cursor) by (destruct HFrame as (_ & _ & _ & HC & _); lia).
  pose proof (slice_write_low_bound 32 outedge cursor ltac:(lia) HC) as HBound.
  change (ofs + size_chunk chunk <= outedge + 8 * ((cursor - 32) / 64)) in Hw.
  lia.
Qed.
