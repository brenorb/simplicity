(** The pad phase of the padding jets: the counted loop of identical
    constant writes as a single write effect. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_output_layout_step C.jet_encoding C.jet_bitcoin_effects C.jet_core_loop C.jet_core_pad_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque ge0.
Set Default Timeout 60.

Lemma rep_cells_length cells k : length (rep_cells cells k) = (k * length cells)%nat.
Proof.
  unfold rep_cells. induction k as [|k IH]; [reflexivity|].
  cbn [repeat concat]. rewrite app_length, IH. reflexivity.
Qed.

Lemma core_pad_loop_phase e le (c w : Z) cnt stmt (cells : list Cell) m0 bd dbase bw edge cursor total :
  typeof cnt = tint ->
  (forall m' k, 0 <= k <= c -> eval_expr ge0 e (le_at le k) m' cnt (Vint (Int.repr c))) ->
  0 <= c <= 1000 -> Z.of_nat (length cells) = w -> 0 < w ->
  write_frame_at m0 bd dbase bw edge cursor total -> 0 < total -> c * w <= total ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  (forall le' m cur, le'!_dst = Some (Vptr bd (Ptrofs.repr dbase)) -> write_frame_at m bd dbase bw edge cur w ->
    exists m', Clight2.exec_stmt ge0 e le' m stmt E0 le' m' Out_normal /\
      write_effect m m' bd dbase bw edge cur w cells) ->
  exists m', Clight2.exec_stmt ge0 e le m0 (core_for_loop cnt stmt) E0 (le_at le c) m' Out_normal /\
    write_effect m0 m' bd dbase bw edge cursor (c * w) (rep_cells cells (Z.to_nat c)).
Proof.
  intros Hty Hcnt Hc Hw Hwpos HF Htot Hct Hdst Hstep.
  assert (HQ0 : write_effect m0 m0 bd dbase bw edge cursor (0 * w) (rep_cells cells (Z.to_nat 0))).
  { destruct (write_frame_at_head m0 bd dbase bw edge cursor total Htot HF)
      as [_ [_ [_ [w0 Hw0]]]].
    pose proof HF as [_ [HFields _]].
    replace (0 * w) with 0 by lia. replace (Z.to_nat 0) with 0%nat by reflexivity.
    eapply write_effect_nil; [exact HFields|exists w0; exact Hw0]. }
  destruct (exec_for_loop e le cnt stmt c
    (fun k m => write_effect m0 m bd dbase bw edge cursor (k * w) (rep_cells cells (Z.to_nat k)))
    m0 Hty Hcnt Hc HQ0) as (m' & Hexec & HQ).
  - intros k m Hk HQk.
    assert (Hlen : Z.of_nat (length (rep_cells cells (Z.to_nat k))) = k * w).
    { rewrite rep_cells_length, Nat2Z.inj_mul, Z2Nat.id by lia. rewrite Hw. reflexivity. }
    assert (HFm : write_frame_at m bd dbase bw edge (cursor - k * w) (total - k * w)).
    { eapply write_frame_at_after_effect with (m := m0) (cells := rep_cells cells (Z.to_nat k));
        [exact Hlen|nia| |exact HQk].
      replace (k * w + (total - k * w)) with total by lia. exact HF. }
    assert (HFw : write_frame_at m bd dbase bw edge (cursor - k * w) w).
    { eapply write_frame_at_shorter; [|exact HFm]. nia. }
    assert (Hdk : (le_at le k)!_dst = Some (Vptr bd (Ptrofs.repr dbase)))
      by (unfold le_at; rewrite PTree.gso by discriminate; exact Hdst).
    destruct (Hstep (le_at le k) m (cursor - k * w) Hdk HFw) as (m1 & Hexec1 & Heff1).
    exists m1. split; [exact Hexec1|].
    replace ((k + 1) * w) with (k * w + w) by lia.
    replace (Z.to_nat (k + 1)) with (Z.to_nat k + 1)%nat by lia.
    rewrite rep_cells_add.
    assert (Hcells1 : rep_cells cells 1 = cells) by (unfold rep_cells; cbn; apply app_nil_r).
    rewrite Hcells1.
    eapply write_effect_seq with (m1 := m); try eassumption; try lia.
    eapply write_frame_at_shorter; [|exact HF]. nia.
  - exists m'. split; [exact Hexec|exact HQ].
Qed.
