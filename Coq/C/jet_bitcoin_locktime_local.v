(** Actual Bitcoin lock_time jet against literal canonical primitive LockTime.
    Reuses the shared initial-memory getter execution, not a version-jet
    execution assumption or a replacement mathematical specification. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Memory.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.Util.Option.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_contract C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_getter32_exec C.jet_bitcoin_getter32_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition bitcoin_transaction_locktime_spec {alg : Primitive.Algebra} : alg Ty.Unit Word32 :=
  Primitive.Combinators.prim Bitcoin.LockTime.

Lemma bitcoin_transaction_locktime_spec_parametric :
  Primitive.Parametric (@bitcoin_transaction_locktime_spec).
Proof. intros alg1 alg2 R. apply prim_Parametric. Qed.

Lemma bitcoin_transaction_locktime_spec_sem (environment : Bitcoin.env) :
  @bitcoin_transaction_locktime_spec (PrimitivePrimSem option_Monad_Zero) tt environment =
    Bitcoin.sem Bitcoin.LockTime tt environment.
Proof. reflexivity. Qed.

Lemma bitcoin_locktime_carrier_matches_primitive r (environment : Bitcoin.env) :
  Int64.unsigned r = Int.unsigned (sigTxLock (Bitcoin.envTx environment)) ->
  Some (decode_wide W32 (Int64.zero_ext 32 r)) = Bitcoin.sem Bitcoin.LockTime tt environment.
Proof.
  intro Hr.
  change (Some (@fromZ (WordToZ 5) (Int64.unsigned (Int64.zero_ext 32 r))) =
    Some (@fromZ (WordToZ 5) (Int.unsigned (sigTxLock (Bitcoin.envTx environment))))).
  rewrite Int64.zero_ext_mod by (change (0 <= 32 < 64); lia).
  change (Some (@fromZ (WordToZ 5) (Int64.unsigned r mod 4294967296)) =
    Some (@fromZ (WordToZ 5) (Int.unsigned (sigTxLock (Bitcoin.envTx environment))))).
  rewrite Hr, Z.mod_small by (pose proof (Int.unsigned_range (sigTxLock (Bitcoin.envTx environment))); exact H).
  reflexivity.
Qed.

Definition bitcoin_locktime_env_rep (m : mem) (env : val) (environment : Bitcoin.env) : Prop :=
  exists be ebase bt txbase value,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase <= Ptrofs.max_unsigned /\ 0 <= txbase /\ txbase + 488 <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) /\
    Mem.load Mint64 m bt (txbase + 472) = Some (Vlong value) /\
    Int64.unsigned value = Int.unsigned (sigTxLock (Bitcoin.envTx environment)).

Theorem bitcoin_locktime_local_spec :
  application_jet_local_spec f_simplicity_bitcoin_lock_time bitcoin_ge Bitcoin.env Ty.Unit Word32
    bitcoin_locktime_env_rep
    (fun a environment => @bitcoin_transaction_locktime_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor []
    (be & ebase & bt & txbase & value & HEnvVal & HE & HT & HM & HEnv & HValue & HR)
    HB HA [HSedge HSoff] _ _ _ HFrame.
  subst env.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  change (write_frame_at m bd dbase bw outedge cursor 32) in HFrame.
  destruct (eval_bitcoin_getter32_layout f_simplicity_bitcoin_lock_time _lockTime 472
      m bd dbase bs sbase bw outedge cursor be ebase bt txbase value bytes
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
      bitcoin_locktime_getter32_body bitcoin_tx_locktime_field HB HA HBytes HE HT ltac:(lia) ltac:(lia)
      HEnv HValue HFrame)
    as (mf & HCall & HOutput & HPrefix & HFields & HMemory).
  exists mf, (decode_wide W32 (Int64.zero_ext 32 value)). split.
  - rewrite bitcoin_transaction_locktime_spec_sem. symmetry.
    apply bitcoin_locktime_carrier_matches_primitive; exact HR.
  - split; [exact HCall|]. split.
    + apply (wide_output_at_encode W32); [|exact HOutput].
      destruct HFrame as (_ & _ & _ & HC & _). change (32 <= cursor); lia.
    + split; [exact HPrefix|]. split; [exact HFields|].
      intros chunk b ofs HV Hd Hw. apply HMemory; [exact HV|exact Hd|].
      destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw|right; left|right; right; exact Hw].
      assert (HC : 32 <= cursor) by (destruct HFrame as (_ & _ & _ & HC & _); lia).
      pose proof (slice_write_low_bound 32 outedge cursor ltac:(lia) HC) as HBound.
      change (ofs + size_chunk chunk <= outedge + 8 * ((cursor - 32) / 64)) in Hw.
      lia.
Qed.
