(** The taproot environment relations of the Elements application jets are
    established by the real [simplicity_elements_mallocTapEnv]: for the
    block it returns ([tapenv_built]) and a logical taproot environment that
    describes the bytes read ([el_tapenv_describes]), the relations of
    [script_cmr], [internal_key], [tapleaf_version] and [tappath] hold for
    any [txEnv] whose taproot pointer is that block.  [tappath] is stated
    for the relation of [C.jet_elements_tappath_nullable], which the builder
    establishes for every path length (it stores a null path pointer for an
    empty path). *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Values Memory.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import C.jet_uint32_array_init C.jet_sha_add_n_calls C.jet_elements_prim.
Require Import C.jet_elements_hash_elem C.jet_elements_hash_getter_local C.jet_elements_script_cmr_local.
Require Import C.jet_elements_tapleaf_version_local C.jet_elements_tappath_nullable.
Require Import C.jet_elements_env_tomidstate C.jet_elements_env_tapenv_key C.jet_elements_env_tapenv.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

Definition el_tapenv_describes (t : tapEnv) (nb cb0 : int) (kb cmrb : list int) (pb : nat -> list int) : Prop :=
  Int.repr (Byte.unsigned (tapleafVersion t)) = Int.and cb0 (Int.repr 254) /\
  hash256_reg (tapScriptCMR t) = tm_words cmrb /\
  length (tappath t) = Z.to_nat (Int.unsigned nb) /\
  (forall j h, nth_error (tappath t) j = Some h -> tm_words (pb j) = hash256_reg h) /\
  hash256_reg (tapInternalKey t) = tm_words kb.

Section Ready.
Variables (m : mem) (bD : block) (oD : Z) (bE : block) (e : Elements.env).
Variables (nb cb0 : int) (kb cmrb : list int) (pb : nat -> list int).
Hypothesis HoD : 0 <= oD /\ oD + 88 <= Ptrofs.max_unsigned.
Hypothesis HPtr : Mem.load Mptr m bD (oD + 8) = Some (Vptr bE Ptrofs.zero).
Hypothesis HB : tapenv_built m bE nb cb0 kb cmrb pb.
Hypothesis HD : el_tapenv_describes (Elements.envTap e) nb cb0 kb cmrb pb.

Let env := Vptr bD (Ptrofs.repr oD).

Lemma b176 : 0 + 176 <= Ptrofs.max_unsigned.
Proof. change Ptrofs.max_unsigned with 18446744073709551615. lia. Qed.

Theorem el_ready_script_cmr :
  elements_script_cmr_env_rep m env e [(bD, oD + 8, oD + 16); (bE, 0 + 136, 0 + 168)].
Proof.
  destruct HD as (_ & Dc & _). unfold tapenv_built in HB. cbv beta zeta in HB.
  destruct HB as (_ & _ & _ & _ & _ & TCmr & _).
  exists bD, oD, bE, 0. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact b176|]. split; [exact HPtr|]. split; [|reflexivity].
  rewrite Z.add_0_l. apply u32_of_nth. intros i Hi. rewrite hash256_len in Hi. rewrite Dc. apply TCmr, Hi.
Qed.

Theorem el_ready_internal_key :
  hash_getter_rep (fun e => tapInternalKey (Elements.envTap e)) 8 104 176 m env e
    [(bD, oD + 8, oD + 8 + 8); (bE, 0 + 104, 0 + 104 + 32)].
Proof.
  destruct HD as (_ & _ & _ & _ & DK). unfold tapenv_built in HB. cbv beta zeta in HB.
  destruct HB as (_ & _ & _ & _ & TKey & _).
  exists bD, oD, bE, 0. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact b176|]. split; [exact HPtr|]. split; [|reflexivity].
  rewrite Z.add_0_l. apply u32_of_nth. intros i Hi. rewrite hash256_len in Hi. rewrite DK. apply TKey, Hi.
Qed.

Theorem el_ready_tapleaf_version :
  elements_tapleaf_version_env_rep m env e [(bD, oD + 8, oD + 16)].
Proof.
  destruct HD as (Dv & _). unfold tapenv_built in HB. cbv beta zeta in HB.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & TVer & _).
  exists bD, oD, bE, 0. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact b176|]. split; [exact HPtr|]. split; [|reflexivity].
  rewrite Dv. exact TVer.
Qed.

Theorem el_ready_tappath :
  0 <= Int.unsigned nb <= 128 ->
  elements_tappath_env_rep_nullable m env e
    [(bD, oD + 8, oD + 16); (bE, 0 + 0, 0 + 8);
     (bE, 176, 176 + 32 * Z.of_nat (length (tappath (Elements.envTap e))))].
Proof.
  intros HN. destruct HD as (_ & _ & DLn & DP & _). unfold tapenv_built in HB. cbv beta zeta in HB.
  destruct HB as (TP0 & _ & _ & _ & _ & _ & TLen & _ & TArr).
  exists bD, oD, bE, 0, bE, 176.
  split; [reflexivity|]. split; [rewrite DLn; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact b176|]. split; [lia|].
  split; [rewrite DLn; change Ptrofs.max_unsigned with 18446744073709551615; lia|].
  split; [exact HPtr|].
  split.
  { intros Hpos. rewrite Z.add_0_l. unfold te_path_value in TP0.
    destruct (Z.eq_dec (Int.unsigned nb) 0) as [E0|_]; [rewrite DLn in Hpos; lia|exact TP0]. }
  split.
  { rewrite Z.add_0_l, DLn, Z2Nat.id, Int.repr_unsigned by lia. exact TLen. }
  split; [|reflexivity].
  intros j h Hj. unfold hash_elem_rep. apply u32_of_nth. intros i Hi. rewrite hash256_len in Hi.
  rewrite <- (DP j h Hj).
  assert (Hjn : (j < Z.to_nat (Int.unsigned nb))%nat) by (rewrite <- DLn; apply nth_error_Some; congruence).
  apply TArr; assumption.
Qed.
End Ready.
