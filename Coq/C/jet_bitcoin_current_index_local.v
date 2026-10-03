(** Actual CurrentIndex jet against its literal canonical Simplicity primitive. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Memory.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.Util.Option.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_contract C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_word_repr.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_current_index_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition bitcoin_transaction_current_index_spec {alg : Primitive.Algebra} : alg Ty.Unit Word32 :=
  Primitive.Combinators.prim Bitcoin.CurrentIndex.

Lemma bitcoin_transaction_current_index_spec_parametric :
  Primitive.Parametric (@bitcoin_transaction_current_index_spec).
Proof. intros alg1 alg2 R. apply prim_Parametric. Qed.

Lemma bitcoin_transaction_current_index_spec_sem (environment : Bitcoin.env) :
  @bitcoin_transaction_current_index_spec (PrimitivePrimSem option_Monad_Zero) tt environment =
    Bitcoin.sem Bitcoin.CurrentIndex tt environment.
Proof. reflexivity. Qed.

Lemma bitcoin_current_index_carrier_matches_primitive r (environment : Bitcoin.env) :
  Int64.unsigned r = Z.of_nat (Bitcoin.envIx environment) ->
  Some (decode_wide W32 (Int64.zero_ext 32 r)) = Bitcoin.sem Bitcoin.CurrentIndex tt environment.
Proof.
  intro Hr.
  change (Some (@fromZ (WordToZ 5) (Int64.unsigned (Int64.zero_ext 32 r))) =
    Some (@fromZ (WordToZ 5) (Z.of_nat (Bitcoin.envIx environment)))).
  rewrite Int64.zero_ext_mod by (change (0 <= 32 < 64); lia).
  rewrite Hr.
  change (Some (@fromZ (WordToZ 5) (Z.of_nat (Bitcoin.envIx environment) mod 4294967296)) =
    Some (@fromZ (WordToZ 5) (Z.of_nat (Bitcoin.envIx environment)))).
  f_equal. exact (word_fromZ_mod 5 (Z.of_nat (Bitcoin.envIx environment))).
Qed.

Definition bitcoin_current_index_env_rep (m : mem) (env : val) (environment : Bitcoin.env) : Prop :=
  exists be ebase index,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    Mem.load Mint64 m be (ebase + 48) = Some (Vlong index) /\
    Int64.unsigned index = Z.of_nat (Bitcoin.envIx environment).

Theorem bitcoin_current_index_local_spec :
  application_jet_local_spec f_simplicity_bitcoin_current_index bitcoin_ge Bitcoin.env Ty.Unit Word32
    bitcoin_current_index_env_rep
    (fun a environment => @bitcoin_transaction_current_index_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor []
    (be & ebase & index & HEnvVal & HE & HM & HIndex & HR)
    HB HA [HSedge HSoff] _ _ _ HFrame.
  subst env.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  change (write_frame_at m bd dbase bw outedge cursor 32) in HFrame.
  destruct (eval_bitcoin_current_index_layout m bd dbase bs sbase bw outedge cursor be ebase index bytes
      HB HA HBytes HE HM HIndex HFrame)
    as (mf & HCall & HOutput & HPrefix & HFields & HMemory).
  exists mf, (decode_wide W32 (Int64.zero_ext 32 index)). split.
  - rewrite bitcoin_transaction_current_index_spec_sem. symmetry.
    apply bitcoin_current_index_carrier_matches_primitive; exact HR.
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
