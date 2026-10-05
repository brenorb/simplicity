(** Numeric reading of the input bits of a jet. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Memory.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_frame_spec C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_encoding.
Require Import C.jet_frame_inv.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

(** Value of a list of bits, most significant first. *)
Fixpoint bits_val (l : list bool) : Z :=
  match l with
  | [] => 0
  | b :: t => (if b then 2 ^ Z.of_nat (length t) else 0) + bits_val t
  end.

Lemma bits_val_range l : 0 <= bits_val l < 2 ^ Z.of_nat (length l).
Proof.
  induction l as [|b t IH]; simpl bits_val; [simpl; lia|].
  change (length (b :: t)) with (S (length t)). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  assert (0 < 2 ^ Z.of_nat (length t)) by (apply Z.pow_pos_nonneg; lia).
  destruct b; lia.
Qed.

Lemma bits_val_testbit l : forall i, (i < length l)%nat ->
  Z.testbit (bits_val l) (Z.of_nat (length l - 1 - i)) = nth i l false.
Proof.
  induction l as [|b t IH]; intros i Hi; [simpl in Hi; lia|].
  pose proof (bits_val_range t) as Hr. simpl bits_val. simpl length in *.
  set (n := Z.of_nat (length t)) in *.
  destruct i as [|i].
  - replace (S (length t) - 1 - 0)%nat with (length t) by lia. fold n. simpl nth.
    destruct b.
    + replace (2 ^ n + bits_val t) with (bits_val t + 1 * 2 ^ n) by lia.
      rewrite Z.testbit_true by (unfold n; lia).
      rewrite Z.div_add by (apply Z.pow_nonzero; unfold n; lia).
      rewrite Z.div_small by lia. reflexivity.
    + rewrite Z.add_0_l.
      destruct (Z.eq_dec (bits_val t) 0) as [->|Hne]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
  - replace (S (length t) - 1 - S i)%nat with (length t - 1 - i)%nat by lia. simpl nth.
    rewrite <- (IH i ltac:(lia)).
    destruct b; [|rewrite Z.add_0_l; reflexivity].
    replace (2 ^ n + bits_val t) with (bits_val t + 1 * 2 ^ n) by lia.
    rewrite <- (Z.mod_pow2_bits_low (bits_val t + 1 * 2 ^ n) n) by (unfold n; lia).
    rewrite Z.mod_add by (apply Z.pow_nonzero; unfold n; lia).
    rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma nth_firstn_lt {A} (l : list A) d : forall n i, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  induction l as [|a t IH]; intros n i Hi; destruct n; try lia; [destruct i; reflexivity|].
  destruct i; [reflexivity|]. simpl. apply IH. lia.
Qed.
Lemma nth_skipn_add {A} (l : list A) d : forall k i, nth i (skipn k l) d = nth (k + i) l d.
Proof.
  induction l as [|a t IH]; intros k i; destruct k; simpl; try reflexivity; [destruct i; reflexivity|].
  apply IH.
Qed.

Section INPUT.
Variables (m0 : mem) (bd : block) (dbase : Z) (bw : block) (outedge cursor N : Z) (bi : block).
Variables (edge rc : Z) (ibits : list bool).
Hypothesis Hin : frame_input_cells_at m0 bi edge rc (map Some ibits).

Definition ifield (k n : nat) : Z := bits_val (firstn n (skipn k ibits)).

Lemma ifield_range k n : (k + n <= length ibits)%nat -> 0 <= ifield k n < 2 ^ Z.of_nat n.
Proof.
  intros H. unfold ifield. pose proof (bits_val_range (firstn n (skipn k ibits))) as Hr.
  rewrite firstn_length, skipn_length in Hr. replace (Nat.min n (length ibits - k)) with n in Hr by lia. exact Hr.
Qed.

Lemma input_bi_valid : ibits <> [] -> Mem.valid_block m0 bi.
Proof.
  intros Hne. destruct ibits as [|b t]; [congruence|].
  specialize (Hin 0%nat (Some b) eq_refl). cbn [cell_matches] in Hin.
  destruct Hin as (_ & _ & w & Hl & _). exact (load_valid _ _ _ _ _ Hl).
Qed.

(** The byte at bit position [p] of the input, as an input word. *)
Lemma input_byte_word m outs p :
  finv m0 bd dbase bw outedge cursor N bi m false outs ->
  (p + 8 <= length ibits)%nat ->
  @frame_input_word_at 3 m bi edge (rc + Z.of_nat p) (@fromZ (WordToZ 3) (ifield p 8)).
Proof.
  intros Hf Hp. apply frame_input_word_at_iff. intros i Hi. change (Z.of_nat (2 ^ 3)) with 8 in *.
  pose proof (finv_input m0 bd dbase bw outedge cursor N bi m outs edge rc (map Some ibits) Hf Hin) as Hc.
  assert (Hq : (p + Z.to_nat i < length ibits)%nat) by lia.
  specialize (Hc (p + Z.to_nat i)%nat (Some (nth (p + Z.to_nat i) ibits false))).
  rewrite nth_error_map, (nth_error_nth' ibits false Hq) in Hc. specialize (Hc eq_refl).
  cbn [cell_matches] in Hc.
  replace (rc + Z.of_nat (p + Z.to_nat i)) with (rc + Z.of_nat p + i) in Hc by lia.
  replace (Z.testbit (@toZ (WordToZ 3) (@fromZ (WordToZ 3) (ifield p 8))) (8 - 1 - i))
    with (nth (p + Z.to_nat i) ibits false); [exact Hc|].
  rewrite to_fromZ. change (two_power_nat (ToZ.Theory.bitSize (WordToZ 3))) with 256.
  assert (Hr : 0 <= ifield p 8 < 256) by exact (ifield_range p 8 Hp).
  rewrite Z.mod_small by lia. unfold ifield.
  pose proof (bits_val_testbit (firstn 8 (skipn p ibits)) (Z.to_nat i)) as Ht.
  rewrite firstn_length, skipn_length in Ht. replace (Nat.min 8 (length ibits - p)) with 8%nat in Ht by lia.
  specialize (Ht ltac:(lia)). replace (Z.of_nat (8 - 1 - Z.to_nat i)) with (8 - 1 - i) in Ht by lia.
  rewrite Ht. rewrite nth_firstn_lt by lia. rewrite nth_skipn_add. reflexivity.
Qed.
End INPUT.
