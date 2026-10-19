(** Every logical Bitcoin environment has a representing C memory for the
    record-only environment relations, and the thirteen registered jets over
    those relations run and return the canonical result for every
    environment and input, with no memory, frame or environment premise.

    One memory holds the environment record (transaction pointer, current
    index) and the transaction record (totals, counts, version, lock time,
    finality flag); each relation reads part of it. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Import Simplicity.Ty Simplicity.BitMachine Simplicity.Translate Simplicity.Primitive.Bitcoin.
Require Import C.jet_partial C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_application_contract C.jet_application_sep C.jet_application_partial.
Require Import C.jet_frame_constructible_app C.jet_env_constructible C.jet_bitcoin_linkage.
Require Import C.jet_bitcoin_version_local C.jet_bitcoin_locktime_local C.jet_bitcoin_current_index_local.
Require Import C.jet_bitcoin_count_local C.jet_bitcoin_totals_local C.jet_bitcoin_fee_local.
Require Import C.jet_bitcoin_is_final_spec C.jet_bitcoin_is_final_local C.jet_bitcoin_lock_local.
Require Import C.jet_bitcoin_check_lock C.jet_app_executable_registry.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Lemma ptrofs_max : Ptrofs.max_unsigned = 18446744073709551615.
Proof. reflexivity. Qed.
Lemma int64_max : Int64.max_unsigned = 18446744073709551615.
Proof. reflexivity. Qed.

Ltac keep B :=
  rewrite (proj1 B) by
    (first [left; assumption | left; apply not_eq_sym; assumption
           | right; left; cbn; lia | right; right; cbn; lia]).

(** The record memory. *)
Lemma bitcoin_record_built (m0 : mem) (ix vi vo nI nO ver lt : int64) (final : bool) :
  exists m be bt,
    Mem.valid_block m be /\ Mem.valid_block m bt /\
    Mem.load Mptr m be 0 = Some (Vptr bt (Ptrofs.repr 0)) /\
    Mem.load Mint64 m be 48 = Some (Vlong ix) /\
    Mem.load Mint64 m bt 432 = Some (Vlong vi) /\
    Mem.load Mint64 m bt 440 = Some (Vlong vo) /\
    Mem.load Mint64 m bt 448 = Some (Vlong nI) /\
    Mem.load Mint64 m bt 456 = Some (Vlong nO) /\
    Mem.load Mint64 m bt 464 = Some (Vlong ver) /\
    Mem.load Mint64 m bt 472 = Some (Vlong lt) /\
    Mem.load Mint8unsigned m bt 480 = Some (Vint (if final then Int.one else Int.zero)).
Proof.
  destruct (three_blocks m0 56 488 0)
    as (m & be & bt & bin & Net & _ & _ & Ve & Vt & _ & Pe & Pt & _).
  assert (Nte : bt <> be) by (apply not_eq_sym; exact Net).
  destruct (built_store_ptr m be 0 bt (Ptrofs.repr 0) 0 8 eq_refl) as (m1 & B1 & L1);
    [intros o Ho; apply Pe; lia|apply Z.divide_0_r|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ be 0 56 Cur Writable B1 Pe) as Pe1.
  pose proof (built_range_perm _ _ _ _ _ bt 0 488 Cur Writable B1 Pt) as Pt1.
  destruct (built_store_int64 m1 be 48 ix 48 56) as (m2 & B2 & L2);
    [intros o Ho; apply Pe1; lia|exists 6; reflexivity|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 488 Cur Writable B2 Pt1) as Pt2.
  destruct (built_store_int64 m2 bt 432 vi 432 440) as (m3 & B3 & L3);
    [intros o Ho; apply Pt2; lia|exists 54; reflexivity|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 488 Cur Writable B3 Pt2) as Pt3.
  destruct (built_store_int64 m3 bt 440 vo 440 448) as (m4 & B4 & L4);
    [intros o Ho; apply Pt3; lia|exists 55; reflexivity|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 488 Cur Writable B4 Pt3) as Pt4.
  destruct (built_store_int64 m4 bt 448 nI 448 456) as (m5 & B5 & L5);
    [intros o Ho; apply Pt4; lia|exists 56; reflexivity|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 488 Cur Writable B5 Pt4) as Pt5.
  destruct (built_store_int64 m5 bt 456 nO 456 464) as (m6 & B6 & L6);
    [intros o Ho; apply Pt5; lia|exists 57; reflexivity|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 488 Cur Writable B6 Pt5) as Pt6.
  destruct (built_store_int64 m6 bt 464 ver 464 472) as (m7 & B7 & L7);
    [intros o Ho; apply Pt6; lia|exists 58; reflexivity|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 488 Cur Writable B7 Pt6) as Pt7.
  destruct (built_store_int64 m7 bt 472 lt 472 480) as (m8 & B8 & L8);
    [intros o Ho; apply Pt7; lia|exists 59; reflexivity|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 488 Cur Writable B8 Pt7) as Pt8.
  destruct (built_store_bool m8 bt 480 final 480 481) as (m9 & B9 & L9);
    [intros o Ho; apply Pt8; lia|lia|lia|].
  exists m9, be, bt.
  split; [repeat match goal with B : built _ _ _ _ _ |- _ => apply (proj1 (proj2 (proj2 B))) end; exact Ve|].
  split; [repeat match goal with B : built _ _ _ _ _ |- _ => apply (proj1 (proj2 (proj2 B))) end; exact Vt|].
  split; [keep B9; keep B8; keep B7; keep B6; keep B5; keep B4; keep B3; keep B2; exact L1|].
  split; [keep B9; keep B8; keep B7; keep B6; keep B5; keep B4; keep B3; exact L2|].
  split; [keep B9; keep B8; keep B7; keep B6; keep B5; keep B4; exact L3|].
  split; [keep B9; keep B8; keep B7; keep B6; keep B5; exact L4|].
  split; [keep B9; keep B8; keep B7; keep B6; exact L5|].
  split; [keep B9; keep B8; keep B7; exact L6|].
  split; [keep B9; keep B8; exact L7|].
  split; [keep B9; exact L8|exact L9].
Qed.

Lemma repr_small z : 0 <= z < 4294967296 -> Int64.unsigned (Int64.repr z) = z.
Proof. intros H. apply Int64.unsigned_repr. rewrite int64_max. lia. Qed.

Lemma int_small (x : int) : 0 <= Int.unsigned x < 4294967296.
Proof. exact (Int.unsigned_range x). Qed.

(** The memory of a logical environment and what it holds. *)
Lemma bitcoin_env_record (e : Bitcoin.env) :
  exists m be bt,
    Mem.valid_block m be /\ Mem.valid_block m bt /\
    Mem.load Mptr m be 0 = Some (Vptr bt (Ptrofs.repr 0)) /\
    (exists ix, Mem.load Mint64 m be 48 = Some (Vlong ix) /\
       Int64.unsigned ix = Z.of_nat (Bitcoin.envIx e)) /\
    (exists vi, Mem.load Mint64 m bt 432 = Some (Vlong vi) /\
       Int64.unsigned vi = sigTxTotalInValue (Bitcoin.envTx e) mod Int64.modulus) /\
    (exists vo, Mem.load Mint64 m bt 440 = Some (Vlong vo) /\
       Int64.unsigned vo = sigTxTotalOutValue (Bitcoin.envTx e) mod Int64.modulus) /\
    (exists nI, Mem.load Mint64 m bt 448 = Some (Vlong nI) /\
       Int64.unsigned nI = Z.of_nat (length (sigTxIn (Bitcoin.envTx e)))) /\
    (exists nO, Mem.load Mint64 m bt 456 = Some (Vlong nO) /\
       Int64.unsigned nO = Z.of_nat (length (sigTxOut (Bitcoin.envTx e)))) /\
    (exists ver, Mem.load Mint64 m bt 464 = Some (Vlong ver) /\
       Int64.unsigned ver = Int.unsigned (sigTxVersion (Bitcoin.envTx e))) /\
    (exists lt, Mem.load Mint64 m bt 472 = Some (Vlong lt) /\
       Int64.unsigned lt = Int.unsigned (sigTxLock (Bitcoin.envTx e))) /\
    Mem.load Mint8unsigned m bt 480 =
      Some (Vint (bool_int (forallb sequence_final (sigTxIn (Bitcoin.envTx e))))).
Proof.
  pose proof (sigTxInBounds (Bitcoin.envTx e)) as HbI. rewrite Zlength_correct in HbI.
  pose proof (sigTxOutBounds (Bitcoin.envTx e)) as HbO. rewrite Zlength_correct in HbO.
  change Int.modulus with 4294967296 in HbI, HbO.
  pose proof (Bitcoin.envIxBounded e) as Hix.
  destruct (bitcoin_record_built Mem.empty
    (Int64.repr (Z.of_nat (Bitcoin.envIx e)))
    (Int64.repr (sigTxTotalInValue (Bitcoin.envTx e)))
    (Int64.repr (sigTxTotalOutValue (Bitcoin.envTx e)))
    (Int64.repr (Z.of_nat (length (sigTxIn (Bitcoin.envTx e)))))
    (Int64.repr (Z.of_nat (length (sigTxOut (Bitcoin.envTx e)))))
    (Int64.repr (Int.unsigned (sigTxVersion (Bitcoin.envTx e))))
    (Int64.repr (Int.unsigned (sigTxLock (Bitcoin.envTx e))))
    (forallb sequence_final (sigTxIn (Bitcoin.envTx e))))
    as (m & be & bt & Ve & Vt & L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
  exists m, be, bt. split; [exact Ve|]. split; [exact Vt|]. split; [exact L0|].
  split; [eexists; split; [exact L1|apply repr_small; lia]|].
  split; [eexists; split; [exact L2|apply Int64.unsigned_repr_eq]|].
  split; [eexists; split; [exact L3|apply Int64.unsigned_repr_eq]|].
  split; [eexists; split; [exact L4|apply repr_small; lia]|].
  split; [eexists; split; [exact L5|apply repr_small; lia]|].
  split; [eexists; split; [exact L6|apply repr_small; apply int_small]|].
  split; [eexists; split; [exact L7|apply repr_small; apply int_small]|exact L8].
Qed.

Ltac rec_env e :=
  destruct (bitcoin_env_record e)
    as (m & be & bt & Ve & Vt & L0 & (ix & Lix & Hix) & (vi & Lvi & Hvi) & (vo & Lvo & Hvo) &
        (nI & LnI & HnI) & (nO & LnO & HnO) & (ver & Lver & Hver) & (lt & Llt & Hlt) & Lfin).

Ltac fin :=
  cbv beta; rewrite ?ptrofs_max; repeat split; cbv beta;
  first [reflexivity | lia | assumption].

Lemma bitcoin_version_env_rep_constructible e : exists m env, bitcoin_version_env_rep m env e.
Proof. rec_env e. exists m, (Vptr be (Ptrofs.repr 0)), be, 0, bt, 0, ver. fin. Qed.

Lemma bitcoin_locktime_env_rep_constructible e : exists m env, bitcoin_locktime_env_rep m env e.
Proof. rec_env e. exists m, (Vptr be (Ptrofs.repr 0)), be, 0, bt, 0, lt. fin. Qed.

Lemma bitcoin_current_index_env_rep_constructible e :
  exists m env, bitcoin_current_index_env_rep m env e.
Proof. rec_env e. exists m, (Vptr be (Ptrofs.repr 0)), be, 0, ix. fin. Qed.

Lemma bitcoin_num_inputs_env_rep_constructible e : exists m env, bitcoin_num_inputs_env_rep m env e.
Proof.
  rec_env e. unfold bitcoin_num_inputs_env_rep, bitcoin_count_env_rep.
  exists m, (Vptr be (Ptrofs.repr 0)), be, 0, bt, 0, nI. fin.
Qed.

Lemma bitcoin_num_outputs_env_rep_constructible e : exists m env, bitcoin_num_outputs_env_rep m env e.
Proof.
  rec_env e. unfold bitcoin_num_outputs_env_rep, bitcoin_count_env_rep.
  exists m, (Vptr be (Ptrofs.repr 0)), be, 0, bt, 0, nO. fin.
Qed.

Ltac valid_fp := repeat constructor; assumption.

Lemma bitcoin_total_input_value_env_rep_constructible e :
  exists m env fp, bitcoin_total_input_value_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  rec_env e. exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  {
    unfold bitcoin_total_input_value_env_rep, bitcoin_tx64_env_rep.
    exists be, 0, bt, 0, vi. fin.
  }
  valid_fp.
Qed.

Lemma bitcoin_total_output_value_env_rep_constructible e :
  exists m env fp, bitcoin_total_output_value_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  rec_env e. exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  {
    unfold bitcoin_total_output_value_env_rep, bitcoin_tx64_env_rep.
    exists be, 0, bt, 0, vo. fin.
  }
  valid_fp.
Qed.

Lemma bitcoin_fee_env_rep_constructible e :
  exists m env fp, bitcoin_fee_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  rec_env e. exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  {
    exists be, 0, bt, 0, vi, vo. fin.
  }
  valid_fp.
Qed.

Lemma bitcoin_tx_is_final_env_rep_constructible e :
  exists m env fp, bitcoin_tx_is_final_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  rec_env e. exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  {
    exists be, 0, bt, 0. fin.
  }
  valid_fp.
Qed.

Lemma bitcoin_lock_env_rep_constructible e :
  exists m env fp, bitcoin_lock_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  rec_env e. exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  {
    exists be, 0, bt, 0, lt. fin.
  }
  valid_fp.
Qed.

Lemma bitcoin_check_lock_env_rep_constructible e : exists m env, bitcoin_check_lock_env_rep m env e.
Proof.
  destruct (bitcoin_lock_env_rep_constructible e) as (m & env & fp & H & _).
  exists m, env, fp. exact H.
Qed.

(** * No-premise statements *)

Definition bitcoin_runs_everywhere (f : function) (A B : Ty)
    (spec : A -> Bitcoin.env -> option B) : Prop :=
  forall (a : A) (e : Bitcoin.env),
  exists m bd bs bw env mf value,
    spec a e = Some value /\
    Clight2.eval_funcall bitcoin_ge m (Internal f)
      [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw 0 (Z.of_nat (bitSize B)) (encode value).

(** For assertion jets: the C verdict is the canonical one, and on success
    the canonical result is left. *)
Definition bitcoin_partial_runs_everywhere (f : function) (A B : Ty)
    (spec : A -> Bitcoin.env -> option B) : Prop :=
  forall (a : A) (e : Bitcoin.env),
  exists m bd bs bw env mf,
    Clight2.eval_funcall bitcoin_ge m (Internal f)
      [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf
      (jet_partial_return (spec a e)) /\
    match spec a e with
    | Some b => frame_output_cells_at mf bw 0 (Z.of_nat (bitSize B)) (encode b)
    | None => True
    end.

Lemma plain_runs_everywhere f A B rep spec :
  application_runs_on_fresh_frames f bitcoin_ge Bitcoin.env A B rep spec ->
  (forall e, exists m env, rep m env e) -> bitcoin_runs_everywhere f A B spec.
Proof.
  intros HRun HRep a e. destruct (HRep e) as (m0 & env & Hr).
  destruct (HRun a e env m0 Hr) as (m & bd & bs & bw & mf & value & H1 & H2 & H3).
  exists m, bd, bs, bw, env, mf, value. repeat split; assumption.
Qed.

Lemma sep_runs_everywhere f A B rep spec :
  application_sep_runs_on_fresh_frames f bitcoin_ge Bitcoin.env A B rep spec ->
  (forall e, exists m env fp, rep m env e fp /\ Forall (fun '(b, _, _) => Mem.valid_block m b) fp) ->
  bitcoin_runs_everywhere f A B spec.
Proof.
  intros HRun HRep a e. destruct (HRep e) as (m0 & env & fp & Hr & Hv).
  destruct (HRun a e env m0 fp Hr Hv) as (m & bd & bs & bw & mf & value & H1 & H2 & H3).
  exists m, bd, bs, bw, env, mf, value. repeat split; assumption.
Qed.

Lemma partial_runs_everywhere f A B rep spec :
  application_partial_runs_on_fresh_frames f bitcoin_ge Bitcoin.env A B rep spec ->
  (forall e, exists m env, rep m env e) -> bitcoin_partial_runs_everywhere f A B spec.
Proof.
  intros HRun HRep a e. destruct (HRep e) as (m0 & env & Hr).
  destruct (HRun a e env m0 Hr) as (m & bd & bs & bw & mf & H1 & H2).
  exists m, bd, bs, bw, env, mf. split; assumption.
Qed.

Ltac statement H :=
  lazymatch type of H with
  | application_runs_on_fresh_frames ?f _ _ ?A ?B _ ?s => exact (bitcoin_runs_everywhere f A B s)
  | application_sep_runs_on_fresh_frames ?f _ _ ?A ?B _ ?s => exact (bitcoin_runs_everywhere f A B s)
  | application_partial_runs_on_fresh_frames ?f _ _ ?A ?B _ ?s =>
      exact (bitcoin_partial_runs_everywhere f A B s)
  end.

Theorem bitcoin_version_runs_everywhere : ltac:(statement bitcoin_version_local_spec_executable).
Proof. exact (plain_runs_everywhere _ _ _ _ _ bitcoin_version_local_spec_executable bitcoin_version_env_rep_constructible). Qed.

Theorem bitcoin_locktime_runs_everywhere : ltac:(statement bitcoin_locktime_local_spec_executable).
Proof. exact (plain_runs_everywhere _ _ _ _ _ bitcoin_locktime_local_spec_executable bitcoin_locktime_env_rep_constructible). Qed.

Theorem bitcoin_current_index_runs_everywhere : ltac:(statement bitcoin_current_index_local_spec_executable).
Proof. exact (plain_runs_everywhere _ _ _ _ _ bitcoin_current_index_local_spec_executable bitcoin_current_index_env_rep_constructible). Qed.

Theorem bitcoin_num_inputs_runs_everywhere : ltac:(statement bitcoin_num_inputs_local_spec_executable).
Proof. exact (plain_runs_everywhere _ _ _ _ _ bitcoin_num_inputs_local_spec_executable bitcoin_num_inputs_env_rep_constructible). Qed.

Theorem bitcoin_num_outputs_runs_everywhere : ltac:(statement bitcoin_num_outputs_local_spec_executable).
Proof. exact (plain_runs_everywhere _ _ _ _ _ bitcoin_num_outputs_local_spec_executable bitcoin_num_outputs_env_rep_constructible). Qed.

Theorem bitcoin_total_input_value_runs_everywhere :
  ltac:(statement bitcoin_total_input_value_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ bitcoin_total_input_value_local_spec_executable bitcoin_total_input_value_env_rep_constructible). Qed.

Theorem bitcoin_total_output_value_runs_everywhere :
  ltac:(statement bitcoin_total_output_value_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ bitcoin_total_output_value_local_spec_executable bitcoin_total_output_value_env_rep_constructible). Qed.

Theorem bitcoin_fee_runs_everywhere : ltac:(statement bitcoin_fee_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ bitcoin_fee_local_spec_executable bitcoin_fee_env_rep_constructible). Qed.

Theorem bitcoin_tx_is_final_runs_everywhere : ltac:(statement bitcoin_tx_is_final_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ bitcoin_tx_is_final_local_spec_executable bitcoin_tx_is_final_env_rep_constructible). Qed.

Theorem bitcoin_tx_lock_height_runs_everywhere : ltac:(statement bitcoin_tx_lock_height_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ bitcoin_tx_lock_height_local_spec_executable bitcoin_lock_env_rep_constructible). Qed.

Theorem bitcoin_tx_lock_time_runs_everywhere : ltac:(statement bitcoin_tx_lock_time_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ bitcoin_tx_lock_time_local_spec_executable bitcoin_lock_env_rep_constructible). Qed.

Theorem bitcoin_check_lock_height_runs_everywhere :
  ltac:(statement bitcoin_check_lock_height_local_spec_executable).
Proof. exact (partial_runs_everywhere _ _ _ _ _ bitcoin_check_lock_height_local_spec_executable bitcoin_check_lock_env_rep_constructible). Qed.

Theorem bitcoin_check_lock_time_runs_everywhere :
  ltac:(statement bitcoin_check_lock_time_local_spec_executable).
Proof. exact (partial_runs_everywhere _ _ _ _ _ bitcoin_check_lock_time_local_spec_executable bitcoin_check_lock_env_rep_constructible). Qed.
