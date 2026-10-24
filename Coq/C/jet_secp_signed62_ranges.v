(** Radix-2^62 value windows used to recover the actual inverse caller's
    top-limb bounds and the capacity of a shortened active array. *)
From Coq Require Import ZArith Lia.
Require Import C.jet_secp_modinv_normalize62_words.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma s62_radix_power_succ n :
  2^(62*Z.of_nat (S n))=2^62*2^(62*Z.of_nat n).
Proof.
  rewrite Nat2Z.inj_succ.
  replace (62*Z.succ (Z.of_nat n)) with (62+62*Z.of_nat n) by lia.
  rewrite Z.pow_add_r by lia;reflexivity.
Qed.

Lemma s62_value_window n w : (forall i,(i<n)%nat -> 0<=w i<2^62) ->
  2^(62*Z.of_nat n)*w n<=norm62_value_z n w<2^(62*Z.of_nat n)*(w n+1).
Proof.
  induction n as [|n IH] in w|-*;intro Low.
  - change (1*w 0%nat<=w 0%nat<1*(w 0%nat+1));rewrite !Z.mul_1_l;lia.
  - pose proof (Low 0%nat ltac:(lia)) as Head.
    pose proof (IH (fun i=>w (S i)) ltac:(intros i I;apply Low;lia)) as Tail.
    rewrite s62_radix_power_succ;cbn [norm62_value_z];rewrite <-!Z.mul_assoc;lia.
Qed.

Lemma s62_value_top_bound n w : (forall i,(i<n)%nat -> 0<=w i<2^62) ->
  Z.abs (norm62_value_z n w)<=2^(62*Z.of_nat (S n)) -> Z.abs (w n)<=2^62.
Proof.
  intros Low Value;pose proof (s62_value_window n w Low) as Window.
  assert (Positive : 0<2^(62*Z.of_nat n)) by (apply Z.pow_pos_nonneg;lia).
  apply Z.abs_le in Value;rewrite s62_radix_power_succ in Value;apply Z.abs_le;nia.
Qed.

Lemma s62_unit_top_capacity n w : (forall i,(i<n)%nat -> 0<=w i<2^62) ->
  (w n=0 \/ w n= -1) -> Z.abs (norm62_value_z n w)<=2^(62*Z.of_nat n).
Proof.
  intros Low Top;pose proof (s62_value_window n w Low) as Window.
  assert (Positive : 0<2^(62*Z.of_nat n)) by (apply Z.pow_pos_nonneg;lia).
  destruct Top as [Zero|Mone];[rewrite Zero in Window|rewrite Mone in Window];apply Z.abs_le;nia.
Qed.
