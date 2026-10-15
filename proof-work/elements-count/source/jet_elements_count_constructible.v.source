(** Actual Elements count-jet execution without an assumed environment
    relation. The two unrestricted local contracts remain the authoritative
    arbitrary-frame results. Here their initial memory/frame premises are
    constructed for every logical environment, proving they are non-vacuous.
    This is not a proof that the production Elements environment builder
    establishes all fields of a full transaction environment. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Import Simplicity.Ty Simplicity.Word Simplicity.BitMachine Simplicity.Translate.
Require Import Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_contract C.jet_frame_constructible_app.
Require Import C.jet_env_constructible C.jet_frame_layout C.jet_output_layout C.jet_encoding.
Require Import C.jet_elements_count_canonical C.jet_elements_count_local C.jet_elements_executable_count.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Lemma elements_count_record_constructible delta (count : Elements.env -> Z) e :
  0 <= delta -> delta + 8 <= 760 -> (8 | delta) ->
  0 <= count e < Int64.modulus ->
  exists m env, elements_count_env_rep delta count m env e.
Proof.
  intros Hd0 Hd1 Hda Hcount.
  destruct (three_blocks Mem.empty 88 760 0)
    as (m & be & bt & unused & Net & _ & _ & Ve & Vt & _ & Pe & Pt & _).
  destruct (built_store_ptr m be 0 bt (Ptrofs.repr 0) 0 8 eq_refl)
    as (m1 & B1 & L1).
  { intros o Ho. apply Pe. lia. }
  { apply Z.divide_0_r. }
  { lia. }
  { lia. }
  pose proof (built_range_perm _ _ _ _ _ bt 0 760 Cur Writable B1 Pt) as Pt1.
  destruct (built_store_int64 m1 bt delta (Int64.repr (count e)) delta (delta + 8))
    as (m2 & B2 & L2).
  { intros o Ho. apply Pt1. lia. }
  { exact Hda. }
  { lia. }
  { lia. }
  unfold elements_count_env_rep.
  exists m2, (Vptr be (Ptrofs.repr 0)), be, 0, bt, 0, (Int64.repr (count e)).
  split; [reflexivity|].
  split; [change (0 <= 0 <= 18446744073709551615); lia|].
  split; [lia|].
  split; [change (0 + 760 <= 18446744073709551615); lia|].
  split.
  { eapply built_load_some; [exact B2|left; exact Net|exact L1]. }
  split; [exact L2|].
  apply Int64.unsigned_repr. change (0 <= count e <= 18446744073709551615).
  change (0 <= count e < 18446744073709551616) in Hcount. lia.
Qed.

Lemma elements_num_inputs_env_rep_constructible e :
  exists m env, elements_num_inputs_env_rep m env e.
Proof.
  unfold elements_num_inputs_env_rep.
  apply elements_count_record_constructible; [lia|lia|exists 87; reflexivity|].
  pose proof (sigTxInBounds (Elements.envTx e)) as H.
  rewrite Zlength_correct in H.
  change Int.modulus with 4294967296 in H.
  change (0 <= Z.of_nat (length (sigTxIn (Elements.envTx e))) < 18446744073709551616).
  lia.
Qed.

Lemma elements_num_outputs_env_rep_constructible e :
  exists m env, elements_num_outputs_env_rep m env e.
Proof.
  unfold elements_num_outputs_env_rep.
  apply elements_count_record_constructible; [lia|lia|exists 88; reflexivity|].
  pose proof (sigTxOutBounds (Elements.envTx e)) as H.
  rewrite Zlength_correct in H.
  change Int.modulus with 4294967296 in H.
  change (0 <= Z.of_nat (length (sigTxOut (Elements.envTx e))) < 18446744073709551616).
  lia.
Qed.

(** Every logical input/environment has a concrete C call and encoded result;
    no frame, memory, environment-representation or libc premise is supplied.
    The starting C memory is existential, not an arbitrary caller memory. *)
Definition elements_constructed_execution (f : function) (A B : Ty)
    (spec : A -> Elements.env -> option B) : Prop :=
  forall (a : A) (e : Elements.env),
  exists m bd bs bw env mf value,
    spec a e = Some value /\
    Clight2.eval_funcall elements_ge m (Internal f)
      [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw 0 (Z.of_nat (bitSize B)) (encode value).

Lemma elements_constructed_execution_from_local f A B rep spec :
  application_runs_on_fresh_frames f elements_ge Elements.env A B rep spec ->
  (forall e, exists m env, rep m env e) ->
  elements_constructed_execution f A B spec.
Proof.
  intros HRun HRep a e. destruct (HRep e) as (m0 & env & Hr).
  destruct (HRun a e env m0 Hr) as (m & bd & bs & bw & mf & value & H1 & H2 & H3).
  exists m, bd, bs, bw, env, mf, value. repeat split; assumption.
Qed.

Theorem elements_num_inputs_constructed_execution :
  elements_constructed_execution f_simplicity_num_inputs Ty.Unit Word32
    (fun a e => @elements_transaction_num_inputs_spec (PrimitivePrimSem option_Monad_Zero) a e).
Proof.
  exact (elements_constructed_execution_from_local _ _ _ _ _
    elements_num_inputs_local_spec_executable elements_num_inputs_env_rep_constructible).
Qed.

Theorem elements_num_outputs_constructed_execution :
  elements_constructed_execution f_simplicity_num_outputs Ty.Unit Word32
    (fun a e => @elements_transaction_num_outputs_spec (PrimitivePrimSem option_Monad_Zero) a e).
Proof.
  exact (elements_constructed_execution_from_local _ _ _ _ _
    elements_num_outputs_local_spec_executable elements_num_outputs_env_rep_constructible).
Qed.
