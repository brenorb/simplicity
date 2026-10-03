(** Actual Bitcoin count getters against literal canonical firstFail programs.
    Reads, source copy, writer, cleanup and encoding follow from initial memory.
    The physical projection observes only the fields these C getters read. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Memory Maps Errors.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.Util.Option.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_contract C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_word_repr.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_getter32_exec C.jet_bitcoin_getter32_layout.
Require Import C.jet_bitcoin_count_canonical C.jet_bitcoin_count_bridge.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma bitcoin_num_inputs_getter32_body :
  f_simplicity_bitcoin_num_inputs.(fn_body) = bitcoin_getter32_body _numInputs.
Proof. reflexivity. Qed.
Lemma bitcoin_num_outputs_getter32_body :
  f_simplicity_bitcoin_num_outputs.(fn_body) = bitcoin_getter32_body _numOutputs.
Proof. reflexivity. Qed.
Lemma bitcoin_tx_num_inputs_field :
  match (Clight.genv_cenv bitcoin_ge)!_bitcoinTransaction with
  | Some co => field_offset (Clight.genv_cenv bitcoin_ge) _numInputs (co_members co) = OK (448, Full)
  | None => False end.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_tx_num_outputs_field :
  match (Clight.genv_cenv bitcoin_ge)!_bitcoinTransaction with
  | Some co => field_offset (Clight.genv_cenv bitcoin_ge) _numOutputs (co_members co) = OK (456, Full)
  | None => False end.
Proof. vm_compute; reflexivity. Qed.

Lemma bitcoin_count_carrier_encoding r count :
  Int64.unsigned r = count ->
  decode_wide W32 (Int64.zero_ext 32 r) = @fromZ (WordToZ 5) count.
Proof.
  intro HR.
  change (@fromZ (WordToZ 5) (Int64.unsigned (Int64.zero_ext 32 r)) = @fromZ (WordToZ 5) count).
  rewrite Int64.zero_ext_mod by (change (0 <= 32 < 64); lia).
  rewrite HR. exact (word_fromZ_mod 5 count).
Qed.

Definition bitcoin_count_env_rep delta (count : Bitcoin.env -> Z)
    (m : mem) (env : val) (environment : Bitcoin.env) : Prop :=
  exists be ebase bt txbase value,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase <= Ptrofs.max_unsigned /\ 0 <= txbase /\ txbase + 488 <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) /\
    Mem.load Mint64 m bt (txbase + delta) = Some (Vlong value) /\
    Int64.unsigned value = count environment.

Lemma bitcoin_count_getter_local_spec f field delta count
    (spec : tySem Ty.Unit -> Bitcoin.env -> option (tySem Word32)) :
  0 <= delta <= 488 ->
  f.(fn_vars) = f_simplicity_bitcoin_version.(fn_vars) ->
  f.(fn_params) = f_simplicity_bitcoin_version.(fn_params) ->
  f.(fn_temps) = f_simplicity_bitcoin_version.(fn_temps) ->
  f.(fn_return) = tbool -> f.(fn_body) = bitcoin_getter32_body field ->
  (match (Clight.genv_cenv bitcoin_ge)!_bitcoinTransaction with
   | Some co => field_offset (Clight.genv_cenv bitcoin_ge) field (co_members co) = OK (delta, Full)
   | None => False end) ->
  (forall environment, spec tt environment = Some (@fromZ (WordToZ 5) (count environment))) ->
  application_jet_local_spec f bitcoin_ge Bitcoin.env Ty.Unit Word32
    (bitcoin_count_env_rep delta count) spec.
Proof.
  intros HD HVars HParams HTemps HRet HBody HField HSpec
    environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor []
    (be & ebase & bt & txbase & value & HEnvVal & HE & HT & HM & HEnv & HValue & HR)
    HB HA [HSedge HSoff] _ _ _ HFrame.
  subst env.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  change (write_frame_at m bd dbase bw outedge cursor 32) in HFrame.
  destruct (eval_bitcoin_getter32_layout f field delta
      m bd dbase bs sbase bw outedge cursor be ebase bt txbase value bytes
      HVars HParams HTemps HRet HBody HField HB HA HBytes HE HT ltac:(lia) ltac:(lia)
      HEnv HValue HFrame)
    as (mf & HCall & HOutput & HPrefix & HFields & HMemory).
  exists mf, (decode_wide W32 (Int64.zero_ext 32 value)). split.
  - rewrite HSpec, (bitcoin_count_carrier_encoding value (count environment) HR). reflexivity.
  - split; [exact HCall | ]. split.
    + apply (wide_output_at_encode W32); [ | exact HOutput].
      destruct HFrame as (_ & _ & _ & HC & _). change (32 <= cursor); lia.
    + split; [exact HPrefix | ]. split; [exact HFields | ].
      intros chunk b ofs HV Hd Hw. apply HMemory; [exact HV | exact Hd | ].
      destruct Hw as [Hw | [Hw | Hw]]; [left; exact Hw | right; left | right; right; exact Hw].
      assert (HC : 32 <= cursor) by (destruct HFrame as (_ & _ & _ & HC & _); lia).
      pose proof (slice_write_low_bound 32 outedge cursor ltac:(lia) HC) as HBound.
      change (ofs + size_chunk chunk <= outedge + 8 * ((cursor - 32) / 64)) in Hw. lia.
Qed.

Definition bitcoin_num_inputs_env_rep := bitcoin_count_env_rep 448
  (fun environment => Z.of_nat (length (sigTxIn (Bitcoin.envTx environment)))).
Definition bitcoin_num_outputs_env_rep := bitcoin_count_env_rep 456
  (fun environment => Z.of_nat (length (sigTxOut (Bitcoin.envTx environment)))).

Theorem bitcoin_num_inputs_local_spec :
  application_jet_local_spec f_simplicity_bitcoin_num_inputs bitcoin_ge Bitcoin.env Ty.Unit Word32
    bitcoin_num_inputs_env_rep
    (fun a environment => @bitcoin_transaction_num_inputs_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply bitcoin_count_getter_local_spec;
    [lia | reflexivity | reflexivity | reflexivity | reflexivity |
     exact bitcoin_num_inputs_getter32_body | exact bitcoin_tx_num_inputs_field | ].
  apply bitcoin_transaction_num_inputs_spec_length.
Qed.

Theorem bitcoin_num_outputs_local_spec :
  application_jet_local_spec f_simplicity_bitcoin_num_outputs bitcoin_ge Bitcoin.env Ty.Unit Word32
    bitcoin_num_outputs_env_rep
    (fun a environment => @bitcoin_transaction_num_outputs_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply bitcoin_count_getter_local_spec;
    [lia | reflexivity | reflexivity | reflexivity | reflexivity |
     exact bitcoin_num_outputs_getter32_body | exact bitcoin_tx_num_outputs_field | ].
  apply bitcoin_transaction_num_outputs_spec_length.
Qed.
