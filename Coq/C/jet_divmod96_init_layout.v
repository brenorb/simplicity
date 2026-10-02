(** Exact machine values and the invariant after the actual C initialization. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Coqlib Integers Maps.
Require Import C.jets C.jet_divmod96_value C.jet_divmod96_init.
Require Import C.jet_divmod96_init_exec C.jet_divmod96_loop_layout.
Import Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma divmod96_initial_values ah al b :
  Int64.modulus <= 2 * Int64.unsigned b -> Int64.unsigned ah < Int64.unsigned b ->
  Int64.unsigned al < divmod96_radix ->
  let q := divmod96_clamp ah (divmod96_high b) in
  Int64.unsigned (divmod96_initial_rh ah b) =
    Int64.unsigned ah - Int64.unsigned q * Int64.unsigned (divmod96_high b) /\
  Int64.unsigned (divmod96_initial_d ah b) =
    Int64.unsigned q * Int64.unsigned (divmod96_low b).
Proof.
  intros Hnorm Hah Hal. cbn zeta.
  destruct (divmod96_machine_initial_bounds ah al b Hnorm Hah Hal)
    as (Hq & Hrh & Hd & Hdelta).
  pose proof (Int64.unsigned_range_2 ah) as HA.
  pose proof (Int64.unsigned_range (divmod96_high b)) as HBH.
  assert (Hprod : 0 <= Int64.unsigned (divmod96_clamp ah (divmod96_high b)) *
      Int64.unsigned (divmod96_high b) <= Int64.max_unsigned) by nia.
  unfold divmod96_initial_rh, divmod96_initial_d.
  rewrite (Int64.mul_commut Int64.one), Int64.mul_one.
  split.
  - unfold Int64.sub, Int64.mul.
    rewrite (Int64.unsigned_repr _ Hprod). apply Int64.unsigned_repr. lia.
  - unfold Int64.mul. apply Int64.unsigned_repr.
    change Int64.modulus with (Int64.max_unsigned + 1) in Hd. lia.
Qed.

Lemma divmod96_initial_invariant ah al b :
  Int64.modulus <= 2 * Int64.unsigned b -> Int64.unsigned ah < Int64.unsigned b ->
  Int64.unsigned al < divmod96_radix ->
  divmod96_loop_inv (Int64.unsigned ah) al (divmod96_high b) (divmod96_low b)
    (divmod96_clamp ah (divmod96_high b)) (divmod96_initial_rh ah b) (divmod96_initial_d ah b) /\
  -2 * divmod96_denominator (divmod96_high b) (divmod96_low b) <=
    divmod96_delta (divmod96_initial_rh ah b) al (divmod96_initial_d ah b).
Proof.
  intros Hnorm Hah Hal.
  destruct (divmod96_machine_initial_bounds ah al b Hnorm Hah Hal)
    as (Hq & Hrh & Hd & Hdelta).
  destruct (divmod96_initial_values ah al b Hnorm Hah Hal) as [HR HD].
  destruct (divmod96_denominator_parts b Hnorm) as [Hbh [Hbl Hb]].
  unfold divmod96_loop_inv, divmod96_delta, divmod96_denominator.
  rewrite HR, HD. split.
  - split; [exact Hq|]. split; [ring|]. split; [reflexivity|]. nia.
  - nia.
Qed.

Lemma divmod96_initial_loop_env le bq ofs ah al b :
  le!_q = Some (Vptr bq ofs) -> le!_al = Some (Vlong al) ->
  divmod96_loop_env (divmod96_init_env le ah b) bq ofs
    (divmod96_initial_rh ah b) (divmod96_high b) al (divmod96_initial_d ah b) (divmod96_low b).
Proof.
  intros HQ HA. unfold divmod96_loop_env, divmod96_init_env.
  repeat split; repeat first [rewrite PTree.gss | rewrite PTree.gso by discriminate];
    first [reflexivity | assumption].
Qed.

Lemma divmod96_initial_r_pointer le ah b :
  (divmod96_init_env le ah b)!_r = le!_r.
Proof.
  unfold divmod96_init_env. rewrite !PTree.gso by discriminate. reflexivity.
Qed.
