(** Every logical Bitcoin environment has a representing C memory for the
    indexed and current-input environment relations, and the eight registered
    jets over those relations run and return the canonical result for every
    environment and input, with no memory, frame or environment premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Import Simplicity.Ty Simplicity.Digest Simplicity.BitMachine Simplicity.Translate.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_uint32_array_init.
Require Import C.jet_application_contract C.jet_application_sep C.jet_application_partial.
Require Import C.jet_frame_constructible_app C.jet_env_constructible C.jet_env_constructible_array.
Require Import C.jet_bitcoin_linkage C.jet_bitcoin_env_constructible.
Require Import C.jet_bitcoin_indexed_scalar C.jet_bitcoin_indexed_scalar_jets.
Require Import C.jet_bitcoin_indexed_ptr C.jet_bitcoin_indexed_ptr_jets.
Require Import C.jet_bitcoin_current_jets C.jet_bitcoin_current_ptr_jets.
Require Import C.jet_bitcoin_input_value_local C.jet_app_executable_registry.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Ltac divides := apply Z.mod_divide; [discriminate|reflexivity].

Lemma bitcoin_inputs_fit (e : Bitcoin.env) sz : 0 <= sz <= 1000 ->
  sz * Z.of_nat (length (sigTxIn (Bitcoin.envTx e))) <= 18446744073709551615 /\
  0 <= Z.of_nat (length (sigTxIn (Bitcoin.envTx e))) < 4294967296.
Proof.
  intros Hsz. pose proof (sigTxInBounds (Bitcoin.envTx e)) as Hb. rewrite Zlength_correct in Hb.
  change Int.modulus with 4294967296 in Hb. split; [nia|lia].
Qed.

Lemma bitcoin_outputs_fit (e : Bitcoin.env) sz : 0 <= sz <= 1000 ->
  sz * Z.of_nat (length (sigTxOut (Bitcoin.envTx e))) <= 18446744073709551615 /\
  0 <= Z.of_nat (length (sigTxOut (Bitcoin.envTx e))) < 4294967296.
Proof.
  intros Hsz. pose proof (sigTxOutBounds (Bitcoin.envTx e)) as Hb. rewrite Zlength_correct in Hb.
  change Int.modulus with 4294967296 in Hb. split; [nia|lia].
Qed.

(** The skeleton for a logical environment and an element relation on whole
    records. *)
Lemma bitcoin_env_array {X : Type} (e : Bitcoin.env) (xs : list X)
    (R : mem -> block -> Z -> X -> Prop) (sz adelta cdelta : Z) :
  0 < sz -> (8 | sz) -> elem_local R sz -> elem_buildable 8 R sz ->
  0 <= adelta -> adelta + 8 <= 488 -> (8 | adelta) ->
  0 <= cdelta -> cdelta + 8 <= 488 -> (8 | cdelta) ->
  adelta + 8 <= cdelta \/ cdelta + 8 <= adelta ->
  0 <= Z.of_nat (length xs) < 4294967296 ->
  exists m be bt bin nI ixv,
    Mem.valid_block m be /\ Mem.valid_block m bt /\ Mem.valid_block m bin /\
    Mem.load Mptr m be 0 = Some (Vptr bt (Ptrofs.repr 0)) /\
    Mem.load Mint64 m be 48 = Some (Vlong ixv) /\
    Mem.load Mptr m bt adelta = Some (Vptr bin (Ptrofs.repr 0)) /\
    Mem.load Mint64 m bt cdelta = Some (Vlong nI) /\
    Int64.unsigned nI = Z.of_nat (length xs) /\
    Int64.unsigned ixv = Z.of_nat (Bitcoin.envIx e) /\
    forall j x, nth_error xs j = Some x -> R m bin (0 + sz * Z.of_nat j) x.
Proof.
  intros Hsz Hal HL HB Ha0 Ha1 Haa Hc0 Hc1 Hca Hdis Hn.
  destruct (env_array_built xs R 56 488 48 sz adelta cdelta
    (Int64.repr (Z.of_nat (Bitcoin.envIx e))) Mem.empty
    ltac:(lia) ltac:(lia) ltac:(divides) ltac:(lia) Hal HL HB Ha0 Ha1 Haa Hc0 Hc1 Hca Hdis)
    as (m & be & bt & bin & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HR).
  pose proof (Bitcoin.envIxBounded e) as Hix.
  pose proof (sigTxInBounds (Bitcoin.envTx e)) as HbI. rewrite Zlength_correct in HbI.
  change Int.modulus with 4294967296 in HbI.
  exists m, be, bt, bin, (Int64.repr (Z.of_nat (length xs))), (Int64.repr (Z.of_nat (Bitcoin.envIx e))).
  repeat (split; [assumption|]).
  split; [apply repr_small; lia|]. split; [apply repr_small; lia|exact HR].
Qed.

Ltac close HR :=
  rewrite ?ptrofs_max; repeat split;
  first [reflexivity | lia | assumption | exact HR].

Section Scalar.
Context {X : Type} (elems_of : Bitcoin.env -> list X) (valz : X -> Z).
Variables (sz voff adelta cdelta : Z).
Hypothesis Hsz : 0 < sz.
Hypothesis Hal : (8 | sz).
Hypothesis Hv0 : 0 <= voff.
Hypothesis Hva : (8 | voff).
Hypothesis Hvin : voff + 8 <= sz.
Hypothesis Ha0 : 0 <= adelta.
Hypothesis Ha1 : adelta + 8 <= 488.
Hypothesis Haa : (8 | adelta).
Hypothesis Hc0 : 0 <= cdelta.
Hypothesis Hc1 : cdelta + 8 <= 488.
Hypothesis Hca : (8 | cdelta).
Hypothesis Hdis : adelta + 8 <= cdelta \/ cdelta + 8 <= adelta.

Let R : mem -> block -> Z -> X -> Prop :=
  fun m b ofs x => Mem.load Mint64 m b (ofs + voff) = Some (Vlong (Int64.repr (valz x))).

Lemma scalar_R_local : elem_local R sz.
Proof.
  eapply elem_local_larger;
    [|apply (elem_local_shift (fun m b ofs (x : X) =>
        Mem.load Mint64 m b ofs = Some (Vlong (Int64.repr (valz x)))) 8 voff Hv0);
      apply (load_local Mint64 (fun x : X => Vlong (Int64.repr (valz x))))]. lia.
Qed.

Lemma scalar_R_buildable : elem_buildable 8 R sz.
Proof.
  eapply elem_buildable_larger;
    [|apply (elem_buildable_shift 8 (fun m b ofs (x : X) =>
        Mem.load Mint64 m b ofs = Some (Vlong (Int64.repr (valz x)))) 8 voff Hv0 Hva);
      apply (int64_buildable (fun x : X => Int64.repr (valz x)))]. lia.
Qed.

Theorem indexed_scalar_rep_constructible (e : Bitcoin.env) :
  sz * Z.of_nat (length (elems_of e)) <= 18446744073709551615 ->
  0 <= Z.of_nat (length (elems_of e)) < 4294967296 ->
  exists m env fp,
    indexed_scalar_rep elems_of valz sz voff adelta cdelta m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  intros Hs Hn.
  destruct (bitcoin_env_array e (elems_of e) R sz adelta cdelta Hsz Hal scalar_R_local
    scalar_R_buildable Ha0 Ha1 Haa Hc0 Hc1 Hca Hdis Hn)
    as (m & be & bt & bin & nI & ixv & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HnI & Hixv & HR).
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0, bin, 0, nI. close HR. }
  repeat constructor; assumption.
Qed.

Theorem current_scalar_rep_constructible (e : Bitcoin.env) :
  sz * Z.of_nat (length (elems_of e)) <= 18446744073709551615 ->
  0 <= Z.of_nat (length (elems_of e)) < 4294967296 ->
  exists m env, current_scalar_rep elems_of valz sz voff adelta cdelta m env e.
Proof.
  intros Hs Hn.
  destruct (bitcoin_env_array e (elems_of e) R sz adelta cdelta Hsz Hal scalar_R_local
    scalar_R_buildable Ha0 Ha1 Haa Hc0 Hc1 Hca Hdis Hn)
    as (m & be & bt & bin & nI & ixv & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HnI & Hixv & HR).
  exists m, (Vptr be (Ptrofs.repr 0)).
  exists be, 0, bt, 0, bin, 0, nI, ixv. close HR.
Qed.
End Scalar.

Section Ptr.
Context {X : Type} (elems_of : Bitcoin.env -> list X) (elemrep : mem -> block -> Z -> X -> Prop).
Variables (sz poff psz adelta cdelta al : Z).
Hypothesis Hsz : 0 < sz.
Hypothesis Hal : (8 | sz).
Hypothesis Hp0 : 0 <= poff.
Hypothesis Hal8 : (al | 8).
Hypothesis Hpa : (al | poff).
Hypothesis Hpin : poff + psz <= sz.
Hypothesis HL : elem_local elemrep psz.
Hypothesis HB : elem_buildable al elemrep psz.
Hypothesis Ha0 : 0 <= adelta.
Hypothesis Ha1 : adelta + 8 <= 488.
Hypothesis Haa : (8 | adelta).
Hypothesis Hc0 : 0 <= cdelta.
Hypothesis Hc1 : cdelta + 8 <= 488.
Hypothesis Hca : (8 | cdelta).
Hypothesis Hdis : adelta + 8 <= cdelta \/ cdelta + 8 <= adelta.

Let R : mem -> block -> Z -> X -> Prop := fun m b ofs x => elemrep m b (ofs + poff) x.

Lemma ptr_R_local : elem_local R sz.
Proof. eapply elem_local_larger; [|apply (elem_local_shift elemrep psz poff Hp0 HL)]. lia. Qed.

Lemma ptr_R_buildable : elem_buildable 8 R sz.
Proof.
  eapply elem_buildable_align; [exact Hal8|].
  eapply elem_buildable_larger; [|apply (elem_buildable_shift al elemrep psz poff Hp0 Hpa HB)]. lia.
Qed.

Theorem indexed_ptr_rep_constructible (e : Bitcoin.env) :
  sz * Z.of_nat (length (elems_of e)) <= 18446744073709551615 ->
  0 <= Z.of_nat (length (elems_of e)) < 4294967296 ->
  exists m env fp,
    indexed_ptr_rep elems_of elemrep sz poff adelta cdelta m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  intros Hs Hn.
  destruct (bitcoin_env_array e (elems_of e) R sz adelta cdelta Hsz Hal ptr_R_local
    ptr_R_buildable Ha0 Ha1 Haa Hc0 Hc1 Hca Hdis Hn)
    as (m & be & bt & bin & nI & ixv & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HnI & Hixv & HR).
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0, bin, 0, nI. close HR. }
  repeat constructor; assumption.
Qed.

Theorem current_ptr_rep_constructible (e : Bitcoin.env) :
  sz * Z.of_nat (length (elems_of e)) <= 18446744073709551615 ->
  0 <= Z.of_nat (length (elems_of e)) < 4294967296 ->
  exists m env fp,
    current_ptr_rep elems_of Bitcoin.envIx elemrep sz poff adelta cdelta m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  intros Hs Hn.
  destruct (bitcoin_env_array e (elems_of e) R sz adelta cdelta Hsz Hal ptr_R_local
    ptr_R_buildable Ha0 Ha1 Haa Hc0 Hc1 Hca Hdis Hn)
    as (m & be & bt & bin & nI & ixv & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HnI & Hixv & HR).
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0, bin, 0, nI, ixv. close HR. }
  repeat constructor; assumption.
Qed.
End Ptr.

(** Element builders. *)
Lemma bitcoin_outpoint_rep_buildable : elem_buildable 8 outpoint_rep 40.
Proof.
  eapply elem_buildable_impl;
    [|apply (elem_buildable_pair 8
        (fun m b ofs (x : sigTxInput) => uint32_array_at m b ofs (outpoint_words x))
        (fun m b ofs (x : sigTxInput) =>
          Mem.load Mint64 m b ofs = Some (Vlong (outpoint_ix (sigTxiPreviousOutpoint x))))
        0 32 32 8 40); try lia; try divides].
  - intros m b ofs x [H1 H2]. rewrite Z.add_0_r in H1. split; assumption.
  - apply words_local. intro x. exact (hash256_len _).
  - eapply elem_buildable_align; [|apply words_buildable; intro x; exact (hash256_len _)]. divides.
  - apply int64_buildable.
Qed.

Lemma bitcoin_outpoint_rep_local : elem_local outpoint_rep 40.
Proof.
  intros m1 m2 b ofs x [Hr Hix] Hl. split.
  - eapply (words_local outpoint_words); [intro; exact (hash256_len _)|exact Hr|].
    intros c o v H1 H2. apply Hl; lia.
  - apply (Hl Mint64 (ofs + 32) _); [lia|change (size_chunk Mint64) with 8; lia|exact Hix].
Qed.

Lemma bitcoin_input_value_env_rep_constructible (e : Bitcoin.env) :
  exists m env fp, bitcoin_input_value_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  destruct (bitcoin_inputs_fit e 160 ltac:(lia)) as [Hs Hn].
  destruct (bitcoin_env_array e (sigTxIn (Bitcoin.envTx e))
    (fun m b ofs (x : sigTxInput) => Mem.load Mint64 m b (ofs + 104) = Some (Vlong (sigTxiValue x)))
    160 0 448 ltac:(lia) ltac:(divides))
    as (m & be & bt & bin & nI & ixv & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HnI & Hixv & HR);
    try lia; try divides; try (left; lia); try exact Hn.
  - eapply elem_local_larger;
      [|apply (elem_local_shift (fun m b ofs (x : sigTxInput) =>
          Mem.load Mint64 m b ofs = Some (Vlong (sigTxiValue x))) 8 104 ltac:(lia));
        apply (load_local Mint64 (fun x : sigTxInput => Vlong (sigTxiValue x)))]. lia.
  - eapply elem_buildable_larger;
      [|apply (elem_buildable_shift 8 (fun m b ofs (x : sigTxInput) =>
          Mem.load Mint64 m b ofs = Some (Vlong (sigTxiValue x))) 8 104 ltac:(lia) ltac:(divides));
        apply (int64_buildable sigTxiValue)]. lia.
  - exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
    { exists be, 0, bt, 0, bin, 0, nI. close HR. }
    repeat constructor; assumption.
Qed.

(** * No-premise statements *)

Ltac sideI e :=
  first [ lia | divides | (left; lia) | (right; lia)
        | exact (proj1 (bitcoin_inputs_fit e 160 ltac:(lia)))
        | exact (proj2 (bitcoin_inputs_fit e 160 ltac:(lia)))
        | exact (proj1 (bitcoin_outputs_fit e 40 ltac:(lia)))
        | exact (proj2 (bitcoin_outputs_fit e 40 ltac:(lia))) ].

Theorem bitcoin_input_value_runs_everywhere : ltac:(statement bitcoin_input_value_local_spec_executable).
Proof.
  exact (sep_runs_everywhere _ _ _ _ _ bitcoin_input_value_local_spec_executable
    bitcoin_input_value_env_rep_constructible).
Qed.

Theorem bitcoin_input_sequence_runs_everywhere :
  ltac:(statement bitcoin_input_sequence_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact bitcoin_input_sequence_local_spec_executable|]. intros e.
  eapply (@indexed_scalar_rep_constructible _ (fun e => sigTxIn (Bitcoin.envTx e))
    (fun txi => Int.unsigned (sigTxiSequence txi)) 160 144 0 448); sideI e.
Qed.

Theorem bitcoin_output_value_runs_everywhere :
  ltac:(statement bitcoin_output_value_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact bitcoin_output_value_local_spec_executable|]. intros e.
  eapply (@indexed_scalar_rep_constructible _ (fun e => sigTxOut (Bitcoin.envTx e))
    (fun txo => Int64.signed (txoValue txo)) 40 0 8 456); sideI e.
Qed.

Theorem bitcoin_current_value_runs_everywhere :
  ltac:(statement bitcoin_current_value_local_spec_executable).
Proof.
  eapply plain_runs_everywhere; [exact bitcoin_current_value_local_spec_executable|]. intros e.
  eapply (@current_scalar_rep_constructible _ (fun e => sigTxIn (Bitcoin.envTx e))
    (fun txi => Int64.unsigned (sigTxiValue txi)) 160 104 0 448); sideI e.
Qed.

Theorem bitcoin_current_sequence_runs_everywhere :
  ltac:(statement bitcoin_current_sequence_local_spec_executable).
Proof.
  eapply plain_runs_everywhere; [exact bitcoin_current_sequence_local_spec_executable|]. intros e.
  eapply (@current_scalar_rep_constructible _ (fun e => sigTxIn (Bitcoin.envTx e))
    (fun txi => Int.unsigned (sigTxiSequence txi)) 160 144 0 448); sideI e.
Qed.

Theorem bitcoin_output_script_hash_runs_everywhere :
  ltac:(statement bitcoin_output_script_hash_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact bitcoin_output_script_hash_local_spec_executable|]. intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxOut (Bitcoin.envTx e))
    (fun m b ofs txo => uint32_array_at m b ofs (script_hash_words txo)) 40 8 32 8 456 4);
    first [exact (words_local script_hash_words ltac:(intro; exact (hash256_len _)))
          |exact (words_buildable script_hash_words ltac:(intro; exact (hash256_len _)))
          |sideI e].
Qed.

Theorem bitcoin_input_prev_outpoint_runs_everywhere :
  ltac:(statement bitcoin_input_prev_outpoint_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact bitcoin_input_prev_outpoint_local_spec_executable|]. intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxIn (Bitcoin.envTx e)) outpoint_rep
    160 64 40 0 448 8);
    first [exact bitcoin_outpoint_rep_local|exact bitcoin_outpoint_rep_buildable|sideI e].
Qed.

Theorem bitcoin_current_prev_outpoint_runs_everywhere :
  ltac:(statement bitcoin_current_prev_outpoint_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact bitcoin_current_prev_outpoint_local_spec_executable|]. intros e.
  eapply (@current_ptr_rep_constructible _ (fun e => sigTxIn (Bitcoin.envTx e)) outpoint_rep
    160 64 40 0 448 8);
    first [exact bitcoin_outpoint_rep_local|exact bitcoin_outpoint_rep_buildable|sideI e].
Qed.
