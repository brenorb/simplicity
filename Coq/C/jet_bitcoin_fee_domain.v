(** Corrected ordinary-transaction fee domain and strong nonvacuity.
    Synthetic memory construction, not execution of the production builder. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Import Simplicity.Translate Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Primitive.Bitcoin.
Require Import Simplicity.Util.List Simplicity.Util.Option.
Require Import C.jet_forWhile_seq C.jet_bitcoin_totals_spec.
Require Import C.jet_bitcoin_fee_spec C.jet_bitcoin_fee_local C.jet_bitcoin_linkage C.jets_bitcoin.
Require Import C.jet_bitcoin_raw_env C.jet_bitcoin_ext_prim C.jet_word_repr.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout C.jet_encoding.
Require Import C.jet_env_constructible C.jet_frame_constructible_app C.jet_application_sep.
Import ListNotations Ctypes.
Local Open Scope Z_scope.
Local Notation moneyRange x := (-1 < x < Z.succ MAX_MONEY).
Local Transparent Archi.ptr64.
Set Default Timeout 30.
Set Implicit Arguments.

(** The upper fee bound follows from the existing total bounds; the lower
    bound expresses the ordinary non-creating transaction domain. *)
Lemma bitcoin_fee_admissible ti to_ :
  moneyRange ti -> moneyRange to_ -> to_ <= ti -> moneyRange (ti - to_).
Proof. unfold MAX_MONEY; lia. Qed.

Definition bitcoin_tx_from_lists ver ins outs lock
    (HI : 0 < Zlength ins < Int.modulus)
    (HO : 0 < Zlength outs < Int.modulus)
    (HTI : moneyRange (Z_sum (map (fun i => Int64.signed (sigTxiValue i)) ins)))
    (HTO : moneyRange (Z_sum (map (fun o => Int64.signed (txoValue o)) outs)))
    (Hbalance : Z_sum (map (fun o => Int64.signed (txoValue o)) outs) <=
                Z_sum (map (fun i => Int64.signed (sigTxiValue i)) ins)) : sigTx :=
  {| sigTxVersion := ver; sigTxIn := ins; sigTxOut := outs; sigTxLock := lock;
     sigTxInBounds := HI; sigTxOutBounds := HO;
     sigTxTotalInValue_bound := HTI; sigTxTotalOutValue_bound := HTO;
     sigTxFee_bound := bitcoin_fee_admissible HTI HTO Hbalance |}.

Lemma bitcoin_fee_exact tx :
  0 <= sigTxFee tx <= MAX_MONEY /\
  sigTxFee tx = sigTxTotalInValue tx - sigTxTotalOutValue tx.
Proof. pose proof (sigTxFee_bound tx) as H.
  change (moneyRange (sigTxFee tx)) in H. split; [lia|reflexivity]. Qed.

Lemma bitcoin_fee_word_exact e :
  wz 6 (fw6 (sigTxFee (Bitcoin.envTx e))) = sigTxFee (Bitcoin.envTx e).
Proof.
  rewrite fw6_toZ. apply Z.mod_small.
  pose proof (bitcoin_fee_exact (Bitcoin.envTx e)) as [H _].
  change (wsize 6) with 18446744073709551616. unfold MAX_MONEY in H. lia.
Qed.

Lemma bitcoin_fee_spec_record e :
  @bitcoin_fee_spec (PrimitivePrimSem option_Monad_Zero) tt e =
    Some (fw6 (sigTxFee (Bitcoin.envTx e))).
Proof. apply bitcoin_fee_spec_value. Qed.

Definition fee_domain_hash : hash256 := Hash256 (repeat Int.zero 8) eq_refl.
Definition fee_domain_input n (H : moneyRange n) : sigTxInput.
Proof.
  refine {| sigTxiPreviousOutpoint := {| opHash := fee_domain_hash; opIndex := Int.zero |};
            sigTxiValue := Int64.repr n; sigTxiSequence := Int.zero |}.
  rewrite Int64.signed_repr; [exact H|].
  change (-9223372036854775808 <= n <= 9223372036854775807).
  unfold MAX_MONEY in H. lia.
Defined.
Definition fee_domain_output n (H : moneyRange n) : txOutput.
Proof.
  refine {| txoValue := Int64.repr n; txoScript := [] |}.
  - rewrite Int64.signed_repr; [exact H|].
    change (-9223372036854775808 <= n <= 9223372036854775807).
    unfold MAX_MONEY in H. lia.
  - change (0 < 4294967296). lia.
Defined.
Definition fee_domain_tx ti to_ (HI : moneyRange ti) (HO : moneyRange to_)
    (HB : to_ <= ti) : sigTx.
Proof.
  refine (bitcoin_tx_from_lists Int.one [fee_domain_input HI]
    [fee_domain_output HO] Int.zero _ _ _ _ _).
  - change (0 < 1 < 4294967296). lia.
  - change (0 < 1 < 4294967296). lia.
  - cbn [map Z_sum fee_domain_input sigTxiValue]. rewrite Int64.signed_repr; [unfold Z_sum; cbn; unfold MAX_MONEY in *; lia|].
    change (-9223372036854775808 <= ti <= 9223372036854775807). unfold MAX_MONEY in HI. lia.
  - cbn [map Z_sum fee_domain_output txoValue]. rewrite Int64.signed_repr; [unfold Z_sum; cbn; unfold MAX_MONEY in *; lia|].
    change (-9223372036854775808 <= to_ <= 9223372036854775807). unfold MAX_MONEY in HO. lia.
  - cbn [map Z_sum fee_domain_input fee_domain_output sigTxiValue txoValue].
    rewrite !Int64.signed_repr; try (unfold Z_sum; cbn; unfold MAX_MONEY in *; lia);
      change (-9223372036854775808 <= _ <= 9223372036854775807); unfold MAX_MONEY in *; lia.
Defined.
Definition fee_domain_env (ti to_ : Z) (HI : moneyRange ti) (HO : moneyRange to_)
    (HB : to_ <= ti) : Bitcoin.env.
Proof.
  refine {| Bitcoin.envTx := @fee_domain_tx ti to_ HI HO HB;
            Bitcoin.envIx := 0; Bitcoin.envScriptCMR := fee_domain_hash |}.
  cbn. lia.
Defined.
Definition positive_fee_env := @fee_domain_env 10 9 ltac:(unfold MAX_MONEY; lia)
  ltac:(unfold MAX_MONEY; lia) ltac:(lia).
Definition zero_fee_env := @fee_domain_env 10 10 ltac:(unfold MAX_MONEY; lia)
  ltac:(unfold MAX_MONEY; lia) ltac:(lia).

Example positive_fee_totals :
  sigTxTotalInValue (Bitcoin.envTx positive_fee_env) = 10 /\
  sigTxTotalOutValue (Bitcoin.envTx positive_fee_env) = 9 /\
  sigTxFee (Bitcoin.envTx positive_fee_env) = 1.
Proof. vm_compute; auto. Qed.
Example zero_fee_total : sigTxFee (Bitcoin.envTx zero_fee_env) = 0.
Proof. reflexivity. Qed.

(** Raw and extended transaction hashing retain the very same base transaction.
    No independently chosen cache is substituted for its transaction id. *)
Definition fee_domain_raw (e : Bitcoin.env) : raw_bitcoin_environment.
Proof.
  refine {| raw_base := e;
    raw_inputs := repeat {| raw_redeemed_script := []; raw_annex := None; raw_script_sig := [] |}
      (length (sigTxIn (Bitcoin.envTx e)));
    raw_leaf_version := Byte.repr 190; raw_tap_path := [];
    raw_internal_key := fee_domain_hash |}.
  apply repeat_length.
Defined.
Lemma fee_domain_raw_projection e :
  extBase (project_raw_environment (fee_domain_raw e) (Nat.le_0_l 128)) = e /\
  extTxid (project_raw_environment (fee_domain_raw e) (Nat.le_0_l 128)) =
    raw_transaction_id (fee_domain_raw e).
Proof. split; reflexivity. Qed.

(** Full physical precondition of the registered fee theorem, for every
    logical environment, including strictly positive fees. *)
Lemma bitcoin_fee_rep_constructible e :
  exists m env fp, bitcoin_fee_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  destruct (three_blocks Mem.empty 56 488 0)
    as (m & be & bt & bin & N & _ & _ & Ve & Vt & _ & Pe & Pt & _).
  destruct (built_store_ptr m be 0 bt (Ptrofs.repr 0) 0 8 eq_refl)
    as (m1 & B1 & L1); [intros o H; apply Pe; lia|apply Z.divide_0_r|lia|lia|].
  destruct (built_store_int64 m1 bt 432 (Int64.repr (sigTxTotalInValue (Bitcoin.envTx e))) 432 440)
    as (m2 & B2 & L2).
  { eapply built_range_perm; [exact B1|]. intros o H. apply Pt. lia. }
  { exists 54; reflexivity. } { lia. } { lia. }
  destruct (built_store_int64 m2 bt 440 (Int64.repr (sigTxTotalOutValue (Bitcoin.envTx e))) 440 448)
    as (m3 & B3 & L3).
  { eapply built_range_perm; [exact B2|]. eapply built_range_perm; [exact B1|]. intros o H. apply Pt. lia. }
  { exists 55; reflexivity. } { lia. } { lia. }
  exists m3, (Vptr be (Ptrofs.repr 0)), [(be, 0, 8); (bt, 432, 448)]. split.
  - exists be, 0, bt, 0,
      (Int64.repr (sigTxTotalInValue (Bitcoin.envTx e))),
      (Int64.repr (sigTxTotalOutValue (Bitcoin.envTx e))).
    repeat split; try reflexivity; try (change (0 <= 0); lia);
      try (change (56 <= 18446744073709551615); lia);
      try (change (488 <= 18446744073709551615); lia).
    + rewrite (proj1 B3), (proj1 B2); try (left; exact N). exact L1.
    + rewrite (proj1 B3); [exact L2|right; left; cbn; lia].
    + exact L3.
    + apply Int64.unsigned_repr. pose proof (sigTxTotalInValue_bound (Bitcoin.envTx e)) as H.
      change (0 <= sigTxTotalInValue (Bitcoin.envTx e) <= 18446744073709551615).
      change (moneyRange (sigTxTotalInValue (Bitcoin.envTx e))) in H. unfold MAX_MONEY in H. lia.
    + apply Int64.unsigned_repr. pose proof (sigTxTotalOutValue_bound (Bitcoin.envTx e)) as H.
      change (0 <= sigTxTotalOutValue (Bitcoin.envTx e) <= 18446744073709551615).
      change (moneyRange (sigTxTotalOutValue (Bitcoin.envTx e))) in H. unfold MAX_MONEY in H. lia.
  - constructor; [exact (proj1 (proj2 (proj2 B3)) _ (proj1 (proj2 (proj2 B2)) _ (proj1 (proj2 (proj2 B1)) _ Ve)))|].
    constructor; [exact (proj1 (proj2 (proj2 B3)) _ (proj1 (proj2 (proj2 B2)) _ (proj1 (proj2 (proj2 B1)) _ Vt)))|constructor].
Qed.

Lemma bitcoin_fee_rep_stable : env_rep_sep_stable bitcoin_fee_env_rep.
Proof.
  intros m m' env e fp HE (be & eb & bt & tb & vi & vo & HV & H0 & H1 & H2 & H3 & L & LI & LO & RI & RO & HF).
  exists be, eb, bt, tb, vi, vo. repeat split; try assumption;
    eapply memory_extension_load; eauto.
Qed.

(** Keep all preconditions and all conclusions of the local theorem visible
    in the witness, including input encoding, footprint, framing and exact
    non-modular fee. The memory at the actual C call represents this e. *)
Definition bitcoin_fee_checked_execution (e : Bitcoin.env) : Prop :=
  exists m env fp bd bs bi bw edge mf,
    bitcoin_fee_env_rep m env e fp /\
    Forall (fun '(b, lo, hi) => out_sep bd 0 bw 0 64 64 b lo hi) fp /\
    frame_base_valid 0 /\ (8 | 0) /\
    frame_fields_at m bs 0 bi edge 0 /\
    frame_input_cells_at m bi edge 0 (encode (X := Ty.Unit) tt) /\
    write_frame_at m bd 0 bw 0 64 64 /\
    @bitcoin_fee_spec (PrimitivePrimSem option_Monad_Zero) tt e = Some (fw6 (sigTxFee (Bitcoin.envTx e))) /\
    wz 6 (fw6 (sigTxFee (Bitcoin.envTx e))) = sigTxTotalInValue (Bitcoin.envTx e) - sigTxTotalOutValue (Bitcoin.envTx e) /\
    Clight2.eval_funcall bitcoin_ge m (Internal f_simplicity_bitcoin_fee)
      [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw 0 64 (encode (fw6 (sigTxFee (Bitcoin.envTx e)))) /\
    write_prefix_at m mf bw 0 64 /\
    frame_fields_at mf bd 0 bw 0 0 /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= 8 \/ 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= 0 \/ 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).

Theorem bitcoin_fee_every_environment_checked e : bitcoin_fee_checked_execution e.
Proof.
  destruct (bitcoin_fee_rep_constructible e) as (m0 & env & fp & HR & HV).
  destruct (frames_extension m0 (encode (X := Ty.Unit) tt) 64)
    as (m & bd & bs & bi & bw & edge & HE & HB & HA & HF & HI & HO & HFresh).
  { cbn. change (0 <= 18446744073709551615). lia. }
  { change (0 <= 64 <= 18446744073709551615). lia. }
  pose proof (bitcoin_fee_rep_stable HE HR) as HR'.
  assert (HS : Forall (fun '(b, lo, hi) => out_sep bd 0 bw 0 64 64 b lo hi) fp).
  { eapply Forall_impl; [|exact HV]. intros [[b lo] hi] H.
    destruct (HFresh b H). split; left; assumption. }
  destruct (bitcoin_fee_local_spec e env m bd 0 bs 0 bi bw edge 0 64 0 tt fp
    HR' HS HB HA HF ltac:(lia) ltac:(change (0 <= 18446744073709551615); lia) HI HO)
    as (mf & value & HVl & HC & HOut & HP & HFields & HM).
  rewrite bitcoin_fee_spec_record in HVl. injection HVl as HVl. subst value.
  exists m, env, fp, bd, bs, bi, bw, edge, mf.
  exact (conj HR' (conj HS (conj HB (conj HA (conj HF (conj HI (conj HO
    (conj (bitcoin_fee_spec_record e) (conj (bitcoin_fee_word_exact e)
      (conj HC (conj HOut (conj HP (conj HFields HM))))))))))))).
Qed.

Example positive_fee_checked : bitcoin_fee_checked_execution positive_fee_env.
Proof. apply bitcoin_fee_every_environment_checked. Qed.
Example zero_fee_checked : bitcoin_fee_checked_execution zero_fee_env.
Proof. apply bitcoin_fee_every_environment_checked. Qed.
