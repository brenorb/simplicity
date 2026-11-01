(** The original C [simplicity_total_fee] compared with the canonical
    [totalFee] program on every represented environment.

    Environment relation: the transaction's stored fee table is uniquely
    sorted, and looking up the 256-bit key read by the jet returns, modulo
    2^64, the sum of the explicit amounts of the outputs that the C builder
    classifies as fees ([isFee]: empty script, explicit asset and amount) with
    that explicit asset.  This is the meaning of the cache that
    [elements/env.c] builds (sorted [feeOutputs], [sumFees]); like every other
    cached Elements field, the builder itself is not verified here.

    The canonical program classifies by the script's SHA-256 digest instead.
    The two totals agree on every environment iff no nonempty supported script
    has the empty-string digest; neither that SHA-256 property nor its negation
    is proved or assumed.  See [JET_ELEMENTS_FEE_MISMATCHES.md]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Values Events.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Digest Simplicity.Bit.
Require Import Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jet_equality_spec C.jet_application_sep C.jet_toZ.
Require Import C.jet_elements_asset_jets C.jet_elements_amount_jets.
Require Import C.jets_elements C.jet_elements_linkage C.jet_memcmp_model C.jet_word32_chunks.
Require Import C.jet_wide C.jet_encoding.
Require Import C.jet_elements_fee_lookup_table C.jet_elements_fee_lookup_sorted.
Require Import C.jet_elements_total_fee_read C.jet_elements_total_fee_suffix C.jet_elements_total_fee_jet.
Require Import C.jet_forWhile_seq C.jet_bitcoin_totals_spec C.jet_word_repr.
Require Import C.jet_elements_fee_flag_exec C.jet_elements_fee_flag_caller C.jet_elements_output_is_fee_spec.
Require Import C.jet_elements_output_is_fee_compare C.jet_elements_total_fee_spec C.jet_elements_sequence_literal.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope semantic_scope.
Set Default Timeout 60.

Local Notation ConfTy a := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) a).

(** * The C builder's fee total *)

(** Contribution of one output under the builder's [isFee] classification. *)
Definition processed_fee_contrib (a : Ty.tySem Word256) (o : txOutput) : Z :=
  if processed_fee_bit o then
    if Bit.toBool (|[ equality_spec (ConfTy Word256) ]| (encode_asset (clearPrf (txoAsset o)), inr a))
    then match clearPrf (txoAmount o) with Explicit v => Int64.unsigned v | Confidential _ _ => 0 end
    else 0
  else 0.

Definition processed_total_fee (a : Ty.tySem Word256) (environment : Elements.env) : Z :=
  fold_right Z.add 0 (map (processed_fee_contrib a) (sigTxOut (Elements.envTx environment))).

Definition total_fee_env_rep (m : mem) (envv : val) (environment : Elements.env)
    (fp : list (block * Z * Z)) : Prop :=
  fp = [] /\
  exists be ebase bt txbase tableval entries,
    envv = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 8 <= Ptrofs.max_unsigned /\ 0 <= txbase /\ txbase + 720 <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) /\
    Mem.load Mptr m bt (txbase + 16) = Some tableval /\
    Mem.load Mint64 m bt (txbase + 712) = Some (Vlong (Int64.repr (Z.of_nat (length entries)))) /\
    tableval <> Vundef /\ total_fee_table_storage m tableval entries /\ fee_lookup_sorted entries /\
    (forall a : Ty.tySem Word256,
      fee_lookup_value (total_fee_input_key (word32_chunks 3 a)) entries =
        Int64.repr (processed_total_fee a environment)).

Lemma fromZ64_unsigned_repr z :
  @fromZ (WordToZ 6) (Int64.unsigned (Int64.repr z)) = fw6 z.
Proof. rewrite Int64.unsigned_repr_eq. exact (word_fromZ_mod 6 z). Qed.

(** The complete original C call computes the builder's fee total. *)
Theorem elements_total_fee_c_contract (Model : memcmp_model) :
  application_jet_local_spec_sep f_simplicity_total_fee elements_ge Elements.env Word256 Word64
    total_fee_env_rep (fun a environment => Some (fw6 (processed_total_fee a environment))).
Proof.
  intros environment envv m bd dbase bs sbase bi bw edge outedge cursor rc a fp
    (-> & be & ebase & bt & txbase & tableval & entries & -> & EB & EM & TB & TM & EnvTx & Table
      & Count & Defined & Storage & Sorted & Lookup)
    _ SrcBase SrcAlign Src RC RCMax Input Out.
  destruct (eval_total_fee_stored_table Model m be ebase bt txbase tableval entries bd dbase bs sbase bi bw
    edge outedge cursor rc a SrcBase SrcAlign Src RC RCMax Input Out EB EM TB TM EnvTx Table Count
    Defined Storage Sorted) as (mf & Call & Cells & Prefix & Fields & Frame).
  exists mf, (fw6 (processed_total_fee a environment)). split; [reflexivity|].
  split; [exact Call|]. split; [|split; [exact Prefix|split; [exact Fields|exact Frame]]].
  unfold total_fee_cells in Cells. rewrite Lookup in Cells.
  change 64 with (wide_bits W64) in Cells at 1.
  rewrite decode_wide64_unsigned', fromZ64_unsigned_repr in Cells. exact Cells.
Qed.

(** * Comparison with the canonical program *)

Lemma fee_contrib_agree a o : ~ fee_digest_collision o ->
  processed_fee_contrib a o = canonical_fee_contrib a o.
Proof.
  intro HN. unfold processed_fee_contrib, canonical_fee_contrib.
  rewrite (proj2 (fee_bits_agree_iff o) HN). reflexivity.
Qed.

Theorem total_fee_results_agree_everywhere_iff :
  (forall a environment, Some (fw6 (processed_total_fee a environment)) =
     @elements_total_fee_spec (PrimitivePrimSem option_Monad_Zero) a environment) <->
  empty_script_digest_unique.
Proof.
  split.
  - intros HAll s Hs HH. destruct s as [|b s]; [reflexivity|exfalso].
    set (h0 := byteStringHash []).
    specialize (HAll (from_hash256 h0) (fee_witness_env (b :: s) Hs)).
    rewrite elements_total_fee_sem in HAll. apply some_inj in HAll.
    assert (HE : Bit.toBool (|[ equality_spec (ConfTy Word256) ]|
        (inr (from_hash256 h0), inr (from_hash256 h0))) = Datatypes.true)
      by (apply equality_spec_true; reflexivity).
    assert (HB : canonical_fee_bit (fee_witness_output (b :: s) Hs) = Datatypes.true).
    { unfold canonical_fee_bit, fee_witness_output. cbn [txoAsset txoAmount txoScript clearPrf
        encode_asset encode_amount fee_explicit andb].
      apply canonical_digest_bit_iff. exact HH. }
    unfold processed_total_fee, canonical_total_fee, fee_witness_env, fee_witness_tx in HAll.
    cbn [Elements.envTx sigTxOut map fold_right] in HAll.
    unfold processed_fee_contrib, canonical_fee_contrib in HAll.
    rewrite HB in HAll. unfold processed_fee_bit, processed_fee_empty, fee_witness_output in HAll.
    cbn [txoAsset txoAmount txoScript clearPrf fee_classifier andb] in HAll.
    cbn [encode_asset] in HAll. fold h0 in HAll.
    match type of HAll with context [if Bit.toBool ?e then _ else _] =>
      replace (Bit.toBool e) with Datatypes.true in HAll by (symmetry; exact HE) end.
    vm_compute in HAll. discriminate HAll.
  - intros HU a environment. rewrite elements_total_fee_sem. f_equal. f_equal.
    unfold processed_total_fee, canonical_total_fee. f_equal. apply map_ext_in.
    intros o _. apply fee_contrib_agree. intros (_ & _ & HN & HH).
    apply HN. apply HU; [apply txoScript_bound|exact HH].
Qed.

(** The complete original C call, its builder-classified result, and the
    exact condition for agreement with the canonical program. *)
Theorem elements_total_fee_canonical_comparison (Model : memcmp_model) :
  application_jet_local_spec_sep f_simplicity_total_fee elements_ge Elements.env Word256 Word64
    total_fee_env_rep (fun a environment => Some (fw6 (processed_total_fee a environment))) /\
  ((forall a environment, Some (fw6 (processed_total_fee a environment)) =
     @elements_total_fee_spec (PrimitivePrimSem option_Monad_Zero) a environment) <->
   empty_script_digest_unique).
Proof. split; [exact (elements_total_fee_c_contract Model)|exact total_fee_results_agree_everywhere_iff]. Qed.

(** Equivalence with the canonical specification, conditional on the open
    SHA-256 property (a hypothesis, not an axiom) and the existing explicit
    [memcmp_model]. *)
Theorem elements_total_fee_local_spec_if_digest_unique (Model : memcmp_model) :
  empty_script_digest_unique ->
  application_jet_local_spec_sep f_simplicity_total_fee elements_ge Elements.env Word256 Word64
    total_fee_env_rep
    (fun a environment => @elements_total_fee_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intro HU. eapply application_jet_local_spec_sep_pointwise;
    [|exact (elements_total_fee_c_contract Model)].
  exact (proj2 total_fee_results_agree_everywhere_iff HU).
Qed.
