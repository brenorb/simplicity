(** Raw canonical contract and boundary checks for the nullable tappath proof.
    No execution, output, or path-pointer load is assumed for an empty path. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Import C.jet_application_sep C.jet_bitcoin_ext_prim C.jet_bitcoin_raw_env.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_raw_jets.
Require Import C.jet_bitcoin_tappath_local.
Require Import C.jet_bitcoin_tappath_nullable.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem bitcoin_tappath_nullable_raw_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tappath bitcoin_ge
    raw_bitcoin_environment Word8 (Ty.Sum Ty.Unit Word256)
    (raw_env_rep bitcoin_tappath_env_rep_nullable) (raw_ext_sem BitcoinExt.Tappath).
Proof.
  apply application_raw_primitive_local_spec_sep.
  exact bitcoin_tappath_nullable_local_spec.
Qed.

Lemma bitcoin_tappath_env_rep_nonempty m env e fp :
  0 < Z.of_nat (length (extTappath e)) ->
  bitcoin_tappath_env_rep_nullable m env e fp ->
  bitcoin_tappath_env_rep m env e fp.
Proof.
  intros Hpos
    (be & ebase & bt & tbase & bp & pbase & H1 & H2 & H3 & H4 & H5 &
     H6 & H7 & H8 & H9 & H10 & H11 & H12).
  exists be, ebase, bt, tbase, bp, pbase.
  repeat (split; [assumption|]). split; [exact (H9 Hpos)|].
  repeat (split; [assumption|]). assumption.
Qed.

Lemma bitcoin_tappath_nullable_empty m be ebase bt tbase e :
  extTappath e = [] ->
  0 <= ebase -> ebase + 56 <= Ptrofs.max_unsigned ->
  0 <= tbase -> tbase + 176 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Mem.load Mint8unsigned m bt (tbase + 168) = Some (Vint Int.zero) ->
  bitcoin_tappath_env_rep_nullable m (Vptr be (Ptrofs.repr ebase)) e
    [(be, ebase + 8, ebase + 16); (bt, tbase + 0, tbase + 8); (bt, 0, 0)].
Proof.
  intros Hempty He0 He1 Ht0 Ht1 Htap Hlen.
  unfold bitcoin_tappath_env_rep_nullable. rewrite Hempty.
  exists be, ebase, bt, tbase, bt, 0.
  split; [reflexivity|].
  split; [exact He0|]. split; [exact He1|].
  split; [exact Ht0|]. split; [exact Ht1|].
  split; [lia|]. split.
  { change (0 <= 18446744073709551615). lia. }
  split; [exact Htap|]. split; [cbn; lia|].
  split; [exact Hlen|]. split; [|reflexivity].
  intros j h Hj. destruct j; discriminate Hj.
Qed.

Lemma bitcoin_tappath_empty_cells a :
  tappath_cells [] a = Some false :: repeat None 256.
Proof.
  unfold tappath_cells. destruct (Z.to_nat (toZ a)); reflexivity.
Qed.

Lemma bitcoin_tappath_empty_sem logical a :
  raw_tap_path logical = [] ->
  raw_ext_sem BitcoinExt.Tappath a logical = Some (inl tt).
Proof.
  intros Hempty. cbn [raw_ext_sem]. rewrite Hempty.
  destruct (Z.to_nat (toZ a)); reflexivity.
Qed.

Lemma bitcoin_tappath_nullable_raw_empty m be ebase bt tbase logical :
  raw_tap_path logical = [] ->
  0 <= ebase -> ebase + 56 <= Ptrofs.max_unsigned ->
  0 <= tbase -> tbase + 176 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Mem.load Mint8unsigned m bt (tbase + 168) = Some (Vint Int.zero) ->
  raw_env_rep bitcoin_tappath_env_rep_nullable m (Vptr be (Ptrofs.repr ebase)) logical
    [(be, ebase + 8, ebase + 16); (bt, tbase + 0, tbase + 8); (bt, 0, 0)].
Proof.
  intros Hempty He0 He1 Ht0 Ht1 Htap Hlen.
  assert (Hpath : (length (raw_tap_path logical) <= 128)%nat)
    by (rewrite Hempty; cbn; lia).
  exists Hpath. apply bitcoin_tappath_nullable_empty; try assumption.
Qed.

(** The old contract cannot describe the actual builder's NULL case. *)
Lemma bitcoin_tappath_old_rep_rejects_null m be ebase bt tbase e fp :
  0 <= ebase -> ebase + 56 <= Ptrofs.max_unsigned ->
  0 <= tbase -> tbase + 176 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Mem.load Mptr m bt (tbase + 0) = Some (Vlong Int64.zero) ->
  ~ bitcoin_tappath_env_rep m (Vptr be (Ptrofs.repr ebase)) e fp.
Proof.
  intros He0 He1 Ht0 Ht1 Htap Hnull
    (be' & ebase' & bt' & tbase' & bp & pbase & Henv &
     He0' & He1' & Ht0' & Ht1' & Hp0 & Hp1 & HLtap & HLpath & Hrest).
  injection Henv as Hbe Hofs. subst be'.
  assert (Ebase : ebase = ebase').
  { change (Ptrofs.unsigned (Ptrofs.repr ebase) =
      Ptrofs.unsigned (Ptrofs.repr ebase')) in Hofs.
    rewrite !Ptrofs.unsigned_repr in Hofs by lia. exact Hofs. }
  subst ebase'. rewrite Htap in HLtap. injection HLtap as Hbt Htofs. subst bt'.
  assert (Tbase : tbase = tbase').
  { change (Ptrofs.unsigned (Ptrofs.repr tbase) =
      Ptrofs.unsigned (Ptrofs.repr tbase')) in Htofs.
    rewrite !Ptrofs.unsigned_repr in Htofs by lia. exact Htofs. }
  subst tbase'. rewrite Hnull in HLpath. discriminate HLpath.
Qed.
