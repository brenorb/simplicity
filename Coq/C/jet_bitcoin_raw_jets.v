(** Lift the checked execution/memory contracts through the raw-data semantics.
    Every cached hash in these premises is computed from the logical raw input;
    no premise assumes jet execution or the result written by the jet. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Values Memory Clight.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Import C.jet_application_sep C.jet_bitcoin_ext_prim C.jet_bitcoin_raw_env.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_indexed_ptr.
Require Import C.jet_bitcoin_hash_getter_local C.jet_bitcoin_ext_ptr_jets.
Require Import C.jet_bitcoin_transaction_id_local C.jet_bitcoin_internal_key_local.
Require Import C.jet_bitcoin_tapleaf_version_local C.jet_bitcoin_tappath_local.
Require Import C.jet_bitcoin_ext_current_spec C.jet_bitcoin_ext_current_jets.
Require Import C.jet_bitcoin_current_ptr_jets.
Local Open Scope Z_scope.
Set Default Timeout 30.

Definition raw_env_rep
    (rep : Mem.mem -> val -> ext_environment -> list (block * Z * Z) -> Prop)
    (m : Mem.mem) (env : val) (logical : raw_bitcoin_environment)
    (fp : list (block * Z * Z)) : Prop :=
  exists Hpath : (length (raw_tap_path logical) <= 128)%nat,
    rep m env (project_raw_environment logical Hpath) fp.

Lemma application_raw_local_spec_sep f ge A B rep spec raw_spec :
  (forall a logical Hpath,
    spec a (project_raw_environment logical Hpath) = raw_spec a logical) ->
  application_jet_local_spec_sep f ge ext_environment A B rep spec ->
  application_jet_local_spec_sep f ge raw_bitcoin_environment A B (raw_env_rep rep) raw_spec.
Proof.
  intros HS HC logical env m bd dbase bs sbase bi bw edge outedge cursor read_cursor a fp
    [Hpath HR] HSep HB HA HF HI0 HImax HIn HOut.
  destruct (HC (project_raw_environment logical Hpath) env m bd dbase bs sbase bi bw
    edge outedge cursor read_cursor a fp HR HSep HB HA HF HI0 HImax HIn HOut)
    as (mf & value & HV & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, value. rewrite HS in HV.
  exact (conj HV (conj HCall (conj HCells (conj HPrefix (conj HFields HMem))))).
Qed.

Lemma application_raw_primitive_local_spec_sep f ge A B (p : BitcoinExt.t A B) rep :
  application_jet_local_spec_sep f ge ext_environment A B rep (BitcoinExt.sem p) ->
  application_jet_local_spec_sep f ge raw_bitcoin_environment A B
    (raw_env_rep rep) (raw_ext_sem p).
Proof.
  apply application_raw_local_spec_sep.
  intros. apply bitcoin_ext_raw_projection.
Qed.

Theorem bitcoin_transaction_id_raw_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_transaction_id bitcoin_ge
    raw_bitcoin_environment Ty.Unit Word256
    (raw_env_rep (hash_getter_rep extTxid 0 400 432))
    (raw_ext_sem BitcoinExt.TransactionId).
Proof.
  apply application_raw_primitive_local_spec_sep.
  exact bitcoin_transaction_id_local_spec.
Qed.

Theorem bitcoin_internal_key_raw_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_internal_key bitcoin_ge
    raw_bitcoin_environment Ty.Unit Word256
    (raw_env_rep (hash_getter_rep extInternalKey 8 104 176))
    (raw_ext_sem BitcoinExt.InternalKey).
Proof.
  apply application_raw_primitive_local_spec_sep.
  exact bitcoin_internal_key_local_spec.
Qed.

Theorem bitcoin_tapleaf_version_raw_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tapleaf_version bitcoin_ge
    raw_bitcoin_environment Ty.Unit Word8 (raw_env_rep bitcoin_tapleaf_version_env_rep)
    (raw_ext_sem BitcoinExt.TapleafVersion).
Proof.
  apply application_raw_primitive_local_spec_sep.
  exact bitcoin_tapleaf_version_local_spec.
Qed.

Theorem bitcoin_input_script_hash_raw_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_script_hash bitcoin_ge
    raw_bitcoin_environment Word32 (Ty.Sum Ty.Unit Word256)
    (raw_env_rep (indexed_ptr_rep extInScriptHash hash_elem_rep 160 112 0 448))
    (raw_ext_sem BitcoinExt.InputScriptHash).
Proof.
  apply application_raw_primitive_local_spec_sep.
  exact bitcoin_input_script_hash_local_spec.
Qed.

Theorem bitcoin_input_script_sig_hash_raw_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_script_sig_hash bitcoin_ge
    raw_bitcoin_environment Word32 (Ty.Sum Ty.Unit Word256)
    (raw_env_rep (indexed_ptr_rep extInScriptSigHash hash_elem_rep 160 32 0 448))
    (raw_ext_sem BitcoinExt.InputScriptSigHash).
Proof.
  apply application_raw_primitive_local_spec_sep.
  exact bitcoin_input_script_sig_hash_local_spec.
Qed.

Theorem bitcoin_tappath_raw_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tappath bitcoin_ge
    raw_bitcoin_environment Word8 (Ty.Sum Ty.Unit Word256)
    (raw_env_rep bitcoin_tappath_env_rep) (raw_ext_sem BitcoinExt.Tappath).
Proof.
  apply application_raw_primitive_local_spec_sep.
  exact bitcoin_tappath_local_spec.
Qed.

(** Option interpretation of the literal CurrentIndex >>> assert (InputX)
    program.  The bridge below preserves that composition and its failure. *)
Definition raw_current_hash_sem (p : BitcoinExt.t Word32 (Ty.Sum Ty.Unit Word256))
    (a : Ty.tySem Ty.Unit) (logical : raw_bitcoin_environment) : option (Ty.tySem Word256) :=
  match raw_ext_sem BitcoinExt.CurrentIndex a logical with
  | Some ix => match raw_ext_sem p ix logical with Some (inr h) => Some h | _ => None end
  | None => None
  end.

Lemma ext_primitive_option_sem {A B} (p : BitcoinExt.t A B) a e :
  @PrimitiveBitcoinExt.Primitive.Combinators.prim A B
    (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero) p a e =
  BitcoinExt.sem p a e.
Proof.
  cbv -[BitcoinExt.sem]. destruct (BitcoinExt.sem p a e); reflexivity.
Qed.

Lemma raw_current_composition p a logical Hpath :
  @ext_comp (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero)
    Ty.Unit Word32 Word256
    (PrimitiveBitcoinExt.Primitive.Combinators.prim BitcoinExt.CurrentIndex)
    (ext_assert_spec (PrimitiveBitcoinExt.Primitive.Combinators.prim p))
    a (project_raw_environment logical Hpath) = raw_current_hash_sem p a logical.
Proof.
  rewrite ext_comp_sem.
  change (match BitcoinExt.sem BitcoinExt.CurrentIndex a (project_raw_environment logical Hpath) with
    | Some ix => @ext_assert_spec
        (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero)
        Word32 Word256 (PrimitiveBitcoinExt.Primitive.Combinators.prim p)
        ix (project_raw_environment logical Hpath)
    | None => None end = raw_current_hash_sem p a logical).
  rewrite bitcoin_ext_raw_projection. unfold raw_current_hash_sem.
  destruct (raw_ext_sem BitcoinExt.CurrentIndex a logical) as [ix|]; [|reflexivity].
  rewrite ext_assert_sem.
  rewrite ext_primitive_option_sem, bitcoin_ext_raw_projection. reflexivity.
Qed.

Theorem bitcoin_current_script_hash_raw_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_current_script_hash bitcoin_ge
    raw_bitcoin_environment Ty.Unit Word256
    (raw_env_rep (current_ptr_rep extInScriptHash ext_ix hash_elem_rep 160 112 0 448))
    (raw_current_hash_sem BitcoinExt.InputScriptHash).
Proof.
  eapply application_raw_local_spec_sep.
  - intros. unfold bitcoin_current_script_hash_spec. apply raw_current_composition.
  - exact bitcoin_current_script_hash_local_spec.
Qed.

Theorem bitcoin_current_script_sig_hash_raw_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_current_script_sig_hash bitcoin_ge
    raw_bitcoin_environment Ty.Unit Word256
    (raw_env_rep (current_ptr_rep extInScriptSigHash ext_ix hash_elem_rep 160 32 0 448))
    (raw_current_hash_sem BitcoinExt.InputScriptSigHash).
Proof.
  eapply application_raw_local_spec_sep.
  - intros. unfold bitcoin_current_script_sig_hash_spec. apply raw_current_composition.
  - exact bitcoin_current_script_sig_hash_local_spec.
Qed.
