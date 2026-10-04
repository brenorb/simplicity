(** Position-level invariant of copyBitsHelper: output position [p] of the
    write frame holds the input bit at stream position [C - p], where
    [C = cursor - 1 + read_cursor].  Stage results are stated per destination
    word and assembled into the cell-level postcondition. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory.
Require Import Simplicity.BitMachine.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout C.jet_encoding.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 30.

Definition copied (m0 mf : mem) (bi : block) (edge : Z) (bw : block) (outedge C lo hi : Z) : Prop :=
  forall p b, lo <= p < hi -> frame_input_bit_at m0 bi edge (C - p) b ->
    frame_output_bit_at mf bw outedge p b.

Lemma copied_app m0 mf bi edge bw outedge C lo mid hi :
  copied m0 mf bi edge bw outedge C lo mid -> copied m0 mf bi edge bw outedge C mid hi ->
  copied m0 mf bi edge bw outedge C lo hi.
Proof.
  intros H1 H2 p b Hp Hin. destruct (zlt p mid); [apply H1|apply H2]; try exact Hin; lia.
Qed.

Lemma copied_sub m0 mf bi edge bw outedge C lo hi lo' hi' :
  copied m0 mf bi edge bw outedge C lo hi -> lo <= lo' -> hi' <= hi ->
  copied m0 mf bi edge bw outedge C lo' hi'.
Proof. intros H Hl Hh p b Hp Hin. apply H; [lia|exact Hin]. Qed.

Lemma copied_preserved m0 mf mf' bi edge bw outedge C lo hi :
  copied m0 mf bi edge bw outedge C lo hi ->
  (forall p, lo <= p < hi ->
    Mem.load Mint64 mf' bw (outedge + 8 * (p / 64)) = Mem.load Mint64 mf bw (outedge + 8 * (p / 64))) ->
  copied m0 mf' bi edge bw outedge C lo hi.
Proof.
  intros H HL p b Hp Hin. destruct (H p b Hp Hin) as [H0 [w [Hw Hb]]].
  split; [exact H0|]. exists w. split; [rewrite HL by exact Hp; exact Hw|exact Hb].
Qed.

(** Bits [lo, hi) of destination word [d] come from source word [k] shifted by [delta]. *)
Lemma copied_word m0 mf bi edge bw outedge C d k delta lo hi W S :
  Mem.load Mint64 mf bw (outedge + 8 * d) = Some (Vlong W) ->
  Mem.load Mint64 m0 bi (edge - 8 * (1 + k)) = Some (Vlong S) ->
  0 <= d -> 0 <= lo -> hi <= 64 ->
  C - 64 * d - 63 + delta = 64 * k ->
  (forall i, lo <= i < hi -> 0 <= i + delta < 64 /\ Int64.testbit W i = Int64.testbit S (i + delta)) ->
  copied m0 mf bi edge bw outedge C (64 * d + lo) (64 * d + hi).
Proof.
  intros HW HS Hd Hlo Hhi Heq Hbits p b Hp (_ & _ & w & Hw & Hb).
  set (i := p - 64 * d).
  assert (Hi : lo <= i < hi) by (unfold i; lia).
  destruct (Hbits i Hi) as [Hr Ht].
  assert (Hpd : p / 64 = d) by (symmetry; apply (Z.div_unique p 64 d i); unfold i; lia).
  assert (Hpm : p mod 64 = i) by (symmetry; apply (Z.mod_unique p 64 d i); unfold i; lia).
  assert (Hq : C - p = 64 * k + (63 - (i + delta))) by (unfold i; lia).
  assert (Hqd : (C - p) / 64 = k)
    by (symmetry; apply (Z.div_unique (C - p) 64 k (63 - (i + delta))); lia).
  assert (Hqm : (C - p) mod 64 = 63 - (i + delta))
    by (symmetry; apply (Z.mod_unique (C - p) 64 k (63 - (i + delta))); lia).
  rewrite Hqd in Hw. rewrite Hqm in Hb.
  rewrite HS in Hw. injection Hw as <-.
  split; [lia|]. exists W. split; [rewrite Hpd; exact HW|].
  rewrite Hpm, Ht, Hb. unfold Int64.testbit. f_equal. lia.
Qed.

Lemma copied_output_cells m0 mf bi edge rc bw outedge cursor cells :
  frame_input_cells_at m0 bi edge rc cells ->
  copied m0 mf bi edge bw outedge (cursor - 1 + rc) (cursor - Z.of_nat (length cells)) cursor ->
  frame_output_cells_at mf bw outedge cursor cells.
Proof.
  intros Hin Hc i c Hi.
  assert (Hlt : (i < length cells)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  specialize (Hin i c Hi).
  assert (Hstep : forall b, frame_input_bit_at m0 bi edge (rc + Z.of_nat i) b ->
    frame_output_bit_at mf bw outedge (cursor - 1 - Z.of_nat i) b).
  { intros b Hb. apply Hc; [lia|].
    replace (cursor - 1 + rc - (cursor - 1 - Z.of_nat i)) with (rc + Z.of_nat i) by lia. exact Hb. }
  destruct c as [b|]; cbn [cell_matches] in *.
  - apply Hstep; exact Hin.
  - destruct Hin as [b Hb]. exists b. apply Hstep; exact Hb.
Qed.

(** Every input position of the cell list has a loadable source word. *)
Lemma input_cells_word m bi edge rc cells j :
  frame_input_cells_at m bi edge rc cells -> 0 <= j < Z.of_nat (length cells) ->
  0 <= rc + j <= Int64.max_unsigned /\
  8 * (1 + (rc + j) / 64) <= edge <= Ptrofs.max_unsigned /\
  exists S, Mem.load Mint64 m bi (edge - 8 * (1 + (rc + j) / 64)) = Some (Vlong S).
Proof.
  intros Hin Hj.
  destruct (nth_error cells (Z.to_nat j)) as [c|] eqn:Hn;
    [|apply nth_error_None in Hn; lia].
  specialize (Hin _ _ Hn). rewrite Z2Nat.id in Hin by lia.
  assert (Hbit : exists b, frame_input_bit_at m bi edge (rc + j) b).
  { destruct c as [b|]; cbn [cell_matches] in Hin; [exists b; exact Hin|exact Hin]. }
  destruct Hbit as (b & HR & HE & S & HS & _).
  split; [exact HR|]. split; [exact HE|]. exists S. exact HS.
Qed.
