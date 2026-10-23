From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Values.
Require Import C.jet_elements_null_overlap_env C.jet_elements_null_overlap_exec.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate.
Require Import C.jet_elements_prim C.jet_elements_null_data_environment.
Require Import C.jet_elements_null_data_output_guard C.jet_elements_null_data_index.
Require Import C.jet_elements_null_data_opcode C.jet_encoding.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition overlap_logical_input : sigTxInput :=
  {| sigTxiPegin := None;
     sigTxiPreviousOutpoint := {| opHash := byteStringHash []; opIndex := Int.zero |};
     sigTxiTxo := {| utxoAsset := Explicit (byteStringHash []);
       utxoAmount := Explicit Int64.zero; utxoScript := [];
       utxoScript_bound := ltac:(change (0 < 4294967296); lia) |};
     sigTxiSequence := Int.zero; sigTxiIssuance := None; sigTxiAnnex := None;
     sigTxiScriptSig := []; sigTxiScriptSig_bound := ltac:(change (0 < 4294967296); lia) |}.

Definition overlap_logical_output : txOutput :=
  {| txoAsset := Explicit (byteStringHash []); txoAmount := Explicit Int64.zero;
     txoNonce := None; txoScript := [Byte.repr 106; Byte.repr 81];
     txoScript_bound := ltac:(change (2 < 4294967296); lia) |}.

Definition overlap_logical_tx : sigTx :=
  {| sigTxVersion := Int.zero; sigTxIn := [overlap_logical_input];
     sigTxOut := [overlap_logical_output]; sigTxLock := Int.zero;
     sigTxInBounds := ltac:(change (0 < 1 < 4294967296); lia);
     sigTxOutBounds := ltac:(change (0 <= 1 < 4294967296); lia) |}.

Definition overlap_logical_environment : Elements.env :=
  {| Elements.envTx := overlap_logical_tx; Elements.envIx := 0%nat;
     Elements.envTap := {| tapleafVersion := Byte.repr 192;
       tapInternalKey := byteStringHash []; tappath := []; tapScriptCMR := byteStringHash [] |};
     Elements.envGenesisBlock := byteStringHash [];
     Elements.envIxBounded := ltac:(change (0 < 1)%nat; lia);
     Elements.envIxWord32 := ltac:(change (0 < 4294967296); lia) |}.

Definition overlap_result_type : Ty.Ty :=
  Ty.Sum Ty.Unit (Ty.Sum Ty.Unit
    (Ty.Sum (Ty.Prod (Word 1) (Word 8)) (Ty.Sum (Ty.Sum Ty.Unit Ty.Unit) (Word 2)))).

Definition overlap_expected_value : Ty.tySem overlap_result_type :=
  inr (inr (inr (inr (@fromZ (WordToZ 2) 0)))).

Lemma overlap_original_spec_value :
  Elements.sem Elements.OutputNullDatum
    (@fromZ (WordToZ 5) 0, @fromZ (WordToZ 5) 0) overlap_logical_environment =
    Some overlap_expected_value.
Proof. reflexivity. Qed.

Definition overlap_env_footprint be bt bout : list (block * Z * Z) :=
  [(be,0,8); (bt,704,712); (bt,8,16); (bout,224,241); (bout,32,36)].

Lemma overlap_environment_represents m be bt bout :
  elements_null_data_output_rep m be 0 bt 0 bout 0 Int64.zero Int64.one true ->
  elements_null_data_count_path m be 0 bt 0 bout 0 Int64.zero Int64.one ->
  overlap_output_fields m bout 0 tt ->
  elements_null_data_environment_rep m (Vptr be Ptrofs.zero) overlap_logical_environment
    (overlap_env_footprint be bt bout).
Proof.
  intros (E0 & EMax & T0 & TMax & EP & TC & More) Count (OP & OC & OF & Code).
  specialize (More eq_refl) as (O0 & OMax & TP & Flag).
  exists be,0,bt,0,bout,0. split; [reflexivity|].
  do 4 (split; [assumption|]). split; [exact EP|]. split; [exact TC|].
  split; [left;reflexivity|]. split; [right;left;reflexivity|].
  intros [|k] txo At; [injection At as <-|destruct k;discriminate].
  unfold elements_null_data_output_environment.
  split; [exact O0|]. split; [exact OMax|]. split; [exact TP|]. split; [exact Flag|].
  split; [right;right;left;reflexivity|]. split; [right;right;right;left;reflexivity|].
  change (elements_null_data_opcode_environment m bout 0 0 [OP1] (overlap_env_footprint be bt bout)).
  split; [change (1 <= 18446744073709551615);lia|]. split; [exact OC|].
  intros [|j] d At; [injection At as <-|destruct j;discriminate].
  exists bout,0. split; [lia|]. split; [change (36 <= 18446744073709551615);lia|].
  split; [exact OP|]. split; [exact Code|].
  split; [right;right;right;right;left;reflexivity|exact I].
Qed.


From compcert Require Import Ctypes Clight ClightBigstep Events.
Require Import C.jet_elements_linkage C.jets_elements C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_application_sep.

(** A successful full public execution with the original input (0,0), a
    satisfiable canonical null-data environment relation and the wrong result.
    Input/output backing storage overlaps; metadata/environment storage does
    not. No evaluator reachability or real-builder execution is claimed. *)
Theorem null_data_overlap_counterexample :
  exists m mf bd bs bw be fp,
    elements_null_data_environment_rep m (Vptr be Ptrofs.zero) overlap_logical_environment fp /\
    Forall (fun '(b,lo,hi) => out_sep bd 0 bw 0 261 261 b lo hi) fp /\
    frame_fields_at m bs 0 bw 40 0 /\
    frame_input_cells_at m bw 40 0
      (@encode (Ty.Prod (Word 5) (Word 5))
        (@fromZ (WordToZ 5) 0, @fromZ (WordToZ 5) 0)) /\
    write_frame_at m bd 0 bw 0 261 261 /\
    Clight2.eval_funcall elements_ge m (Internal f_simplicity_output_null_datum)
      [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vptr be Ptrofs.zero] E0 mf (Vint Int.one) /\
    frame_fields_at mf bd 0 bw 0 0 /\
    Elements.sem Elements.OutputNullDatum
      (@fromZ (WordToZ 5) 0, @fromZ (WordToZ 5) 0) overlap_logical_environment =
      Some overlap_expected_value /\
    ~ frame_output_cells_at mf bw 0 261 (encode overlap_expected_value).
Proof.
  destruct overlap_public_execution_witness
    as (m & mf & bd & bs & bw & be & bt & bout & Source & InputI & InputJ & Frame & Rep & Count
      & Output & (ED & EW & TD & TW & OD & OW) & Call & Cells & Final).
  exists m,mf,bd,bs,bw,be,(overlap_env_footprint be bt bout).
  split; [apply overlap_environment_represents; assumption|]. split.
  - assert (Meta : forall b lo hi, In b [be;bt;bout] -> out_sep bd 0 bw 0 261 261 b lo hi).
    { intros b lo hi H. destruct H as [<-|[<-|[<-|[]]]]; split; left; assumption. }
    unfold overlap_env_footprint.
    repeat (constructor; [apply Meta; cbn; tauto|]). constructor.
  - split; [exact Source|]. split.
    + apply frame_input_word_pair_encode. exact (conj InputI InputJ).
    + split; [exact Frame|]. split; [exact Call|]. split; [exact Final|].
      split; [exact overlap_original_spec_value|]. intro Correct.
      pose proof (Cells 1%nat (Some false) eq_refl) as ActualBit.
      pose proof (Correct 1%nat (Some true) eq_refl) as ExpectedBit.
      destruct ActualBit as (_ & wa & LA & BA).
      destruct ExpectedBit as (_ & we & LE & BE).
      assert (wa = we) by congruence. subst we. congruence.
Qed.
