(** Every logical Elements environment has a representing C memory, for the
    indexed and current-input environment relations.

    The memory is three fresh blocks (environment record, transaction record,
    input or output array) filled by stores; the element relation is built by
    the consumer's element builder.  With the executability theorems this
    removes the environment relation as a premise: see
    [jet_elements_runs_everywhere]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values.
Require Import C.jet_env_constructible C.jet_elements_prim.
Require Import C.jet_elements_indexed_ptr C.jet_elements_indexed_scalar.
Require Import C.jet_elements_current_ptr_jets C.jet_elements_current_gen C.jet_elements_current_jets.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 60.

Lemma ptrofs_max : Ptrofs.max_unsigned = 18446744073709551615.
Proof. reflexivity. Qed.
Lemma int64_max : Int64.max_unsigned = 18446744073709551615.
Proof. reflexivity. Qed.

(** The shared skeleton: environment record pointing to the transaction
    record, which holds the array pointer and the count; the current index;
    and the array of elements. *)
Lemma elements_env_built {X : Type} (xs : list X) (R : mem -> block -> Z -> X -> Prop)
    (sz adelta cdelta : Z) (ixv : int64) (m0 : mem) :
  0 <= sz -> (8 | sz) -> elem_local R sz -> elem_buildable 8 R sz ->
  0 <= adelta -> adelta + 8 <= 760 -> (8 | adelta) ->
  0 <= cdelta -> cdelta + 8 <= 760 -> (8 | cdelta) ->
  adelta + 8 <= cdelta \/ cdelta + 8 <= adelta ->
  exists m be bt bin,
    Mem.valid_block m be /\ Mem.valid_block m bt /\ Mem.valid_block m bin /\
    Mem.load Mptr m be 0 = Some (Vptr bt (Ptrofs.repr 0)) /\
    Mem.load Mint64 m be 80 = Some (Vlong ixv) /\
    Mem.load Mptr m bt adelta = Some (Vptr bin (Ptrofs.repr 0)) /\
    Mem.load Mint64 m bt cdelta = Some (Vlong (Int64.repr (Z.of_nat (length xs)))) /\
    forall j x, nth_error xs j = Some x -> R m bin (0 + sz * Z.of_nat j) x.
Proof.
  intros Hsz Hal HL HB Ha0 Ha1 Haa Hc0 Hc1 Hca Hdis.
  destruct (three_blocks m0 88 760 (sz * Z.of_nat (length xs)))
    as (m & be & bt & bin & Net & Nei & Nti & Ve & Vt & Vi & Pe & Pt & Pi).
  destruct (built_store_ptr m be 0 bt (Ptrofs.repr 0) 0 8 eq_refl) as (m1 & B1 & L1);
    [intros o Ho; apply Pe; lia|apply Z.divide_0_r|lia|lia|].
  destruct (built_store_int64 m1 be 80 ixv 80 88) as (m2 & B2 & L2);
    [eapply built_range_perm; [exact B1|]; intros o Ho; apply Pe; lia|exists 10; reflexivity|lia|lia|].
  destruct (built_store_ptr m2 bt adelta bin (Ptrofs.repr 0) adelta (adelta + 8) eq_refl) as (m3 & B3 & L3);
    [eapply built_range_perm; [exact B2|]; eapply built_range_perm; [exact B1|]; intros o Ho; apply Pt; lia
    |exact Haa|lia|lia|].
  destruct (built_store_int64 m3 bt cdelta (Int64.repr (Z.of_nat (length xs))) cdelta (cdelta + 8))
    as (m4 & B4 & L4);
    [eapply built_range_perm; [exact B3|]; eapply built_range_perm; [exact B2|];
     eapply built_range_perm; [exact B1|]; intros o Ho; apply Pt; lia|exact Hca|lia|lia|].
  destruct (array_buildable R sz Hsz Hal HL HB xs m4 bin 0) as (m5 & B5 & HR).
  { eapply built_range_perm; [exact B4|]. eapply built_range_perm; [exact B3|].
    eapply built_range_perm; [exact B2|]. eapply built_range_perm; [exact B1|]. exact Pi. }
  { apply Z.divide_0_r. }
  destruct B1 as (_ & _ & V1 & _). destruct B2 as (LB2 & _ & V2 & _). destruct B3 as (LB3 & _ & V3 & _).
  destruct B4 as (LB4 & _ & V4 & _). destruct B5 as (LB5 & _ & V5 & _).
  exists m5, be, bt, bin.
  split; [exact (V5 _ (V4 _ (V3 _ (V2 _ (V1 _ Ve)))))|].
  split; [exact (V5 _ (V4 _ (V3 _ (V2 _ (V1 _ Vt)))))|].
  split; [exact (V5 _ (V4 _ (V3 _ (V2 _ (V1 _ Vi)))))|].
  split.
  { rewrite (LB5 Mptr be 0) by (left; exact Nei). rewrite (LB4 Mptr be 0) by (left; exact Net).
    rewrite (LB3 Mptr be 0) by (left; exact Net).
    rewrite (LB2 Mptr be 0) by (right; left; change (size_chunk Mptr) with 8; lia). exact L1. }
  split.
  { rewrite (LB5 Mint64 be 80) by (left; exact Nei). rewrite (LB4 Mint64 be 80) by (left; exact Net).
    rewrite (LB3 Mint64 be 80) by (left; exact Net). exact L2. }
  split.
  { rewrite (LB5 Mptr bt adelta) by (left; exact Nti).
    rewrite (LB4 Mptr bt adelta) by (right; change (size_chunk Mptr) with 8; lia). exact L3. }
  split.
  { rewrite (LB5 Mint64 bt cdelta) by (left; exact Nti). exact L4. }
  exact HR.
Qed.

Section Reps.
Context {X : Type} (elems_of : Elements.env -> list X) (elemrep : mem -> block -> Z -> X -> Prop).
Variables (sz poff psz adelta cdelta al : Z).
Hypothesis Hsz : 0 < sz.
Hypothesis Hal : (8 | sz).
Hypothesis Hp0 : 0 <= poff.
Hypothesis Hal8 : (al | 8).
Hypothesis Hpa : (al | poff).
Hypothesis Hps : 0 <= psz.
Hypothesis Hpin : poff + psz <= sz.
Hypothesis HL : elem_local elemrep psz.
Hypothesis HB : elem_buildable al elemrep psz.
Hypothesis Ha0 : 0 <= adelta.
Hypothesis Ha1 : adelta + 8 <= 760.
Hypothesis Haa : (8 | adelta).
Hypothesis Hc0 : 0 <= cdelta.
Hypothesis Hc1 : cdelta + 8 <= 760.
Hypothesis Hca : (8 | cdelta).
Hypothesis Hdis : adelta + 8 <= cdelta \/ cdelta + 8 <= adelta.

Let R : mem -> block -> Z -> X -> Prop := fun m b ofs x => elemrep m b (ofs + poff) x.

Lemma R_local : elem_local R sz.
Proof.
  eapply elem_local_larger; [|apply (elem_local_shift elemrep psz poff Hp0 HL)]. lia.
Qed.

Lemma R_buildable : elem_buildable 8 R sz.
Proof.
  eapply elem_buildable_align; [exact Hal8|].
  eapply elem_buildable_larger; [|apply (elem_buildable_shift al elemrep psz poff Hp0 Hpa HB)]. lia.
Qed.

Theorem indexed_ptr_rep_constructible (e : Elements.env) (m0 : mem) :
  sz * Z.of_nat (length (elems_of e)) <= Ptrofs.max_unsigned ->
  Z.of_nat (length (elems_of e)) <= Int64.max_unsigned ->
  exists m env fp,
    indexed_ptr_rep elems_of elemrep sz poff adelta cdelta m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  intros Hs Hn.
  destruct (elements_env_built (elems_of e) R sz adelta cdelta Int64.zero m0 ltac:(lia) Hal
    R_local R_buildable Ha0 Ha1 Haa Hc0 Hc1 Hca Hdis)
    as (m & be & bt & bin & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HR).
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  - exists be, 0, bt, 0, bin, 0, (Int64.repr (Z.of_nat (length (elems_of e)))).
    rewrite ptrofs_max in *. rewrite int64_max in Hn.
    repeat split;
      first [reflexivity | lia | assumption | exact HR
            | (apply Int64.unsigned_repr; rewrite int64_max; lia)].
  - repeat constructor; assumption.
Qed.

Theorem current_ptr_rep_constructible (e : Elements.env) (m0 : mem) :
  sz * Z.of_nat (length (elems_of e)) <= Ptrofs.max_unsigned ->
  Z.of_nat (length (elems_of e)) <= Int64.max_unsigned ->
  exists m env fp,
    current_ptr_rep elems_of Elements.envIx elemrep sz poff adelta cdelta m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  intros Hs Hn.
  destruct (elements_env_built (elems_of e) R sz adelta cdelta
    (Int64.repr (Z.of_nat (Elements.envIx e))) m0 ltac:(lia) Hal
    R_local R_buildable Ha0 Ha1 Haa Hc0 Hc1 Hca Hdis)
    as (m & be & bt & bin & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HR).
  pose proof (Elements.envIxWord32 e) as Hix.
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  - exists be, 0, bt, 0, bin, 0, (Int64.repr (Z.of_nat (length (elems_of e)))),
      (Int64.repr (Z.of_nat (Elements.envIx e))).
    rewrite ptrofs_max in *. rewrite int64_max in Hn.
    repeat split;
      first [reflexivity | lia | assumption | exact HR
            | (apply Int64.unsigned_repr; rewrite int64_max; lia)].
  - repeat constructor; assumption.
Qed.
End Reps.

Section GenRep.
Context {X : Type} (elems_of : Elements.env -> list X) (elemrep : mem -> block -> Z -> X -> Prop).
Variables (sz adelta cdelta : Z).
Hypothesis Hsz : 0 < sz.
Hypothesis Hal : (8 | sz).
Hypothesis HL : elem_local elemrep sz.
Hypothesis HB : elem_buildable 8 elemrep sz.
Hypothesis Ha0 : 0 <= adelta.
Hypothesis Ha1 : adelta + 8 <= 760.
Hypothesis Haa : (8 | adelta).
Hypothesis Hc0 : 0 <= cdelta.
Hypothesis Hc1 : cdelta + 8 <= 760.
Hypothesis Hca : (8 | cdelta).
Hypothesis Hdis : adelta + 8 <= cdelta \/ cdelta + 8 <= adelta.

Theorem current_gen_rep_constructible (e : Elements.env) (m0 : mem) :
  sz * Z.of_nat (length (elems_of e)) <= Ptrofs.max_unsigned ->
  Z.of_nat (length (elems_of e)) <= Int64.max_unsigned ->
  exists m env fp,
    current_gen_rep elems_of elemrep sz adelta cdelta m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  intros Hs Hn.
  destruct (elements_env_built (elems_of e) elemrep sz adelta cdelta
    (Int64.repr (Z.of_nat (Elements.envIx e))) m0 ltac:(lia) Hal
    HL HB Ha0 Ha1 Haa Hc0 Hc1 Hca Hdis)
    as (m & be & bt & bin & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HR).
  pose proof (Elements.envIxWord32 e) as Hix.
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  - exists be, 0, bt, 0, bin, 0, (Int64.repr (Z.of_nat (length (elems_of e)))),
      (Int64.repr (Z.of_nat (Elements.envIx e))).
    rewrite ptrofs_max in *. rewrite int64_max in Hn.
    repeat split;
      first [reflexivity | lia | assumption | exact HR
            | (apply Int64.unsigned_repr; rewrite int64_max; lia)].
  - repeat constructor; assumption.
Qed.
End GenRep.

(** Input and output counts fit the address arithmetic for any record size
    up to 1000 bytes. *)
Lemma elements_inputs_fit (e : Elements.env) sz : 0 <= sz <= 1000 ->
  sz * Z.of_nat (length (sigTxIn (Elements.envTx e))) <= Ptrofs.max_unsigned /\
  Z.of_nat (length (sigTxIn (Elements.envTx e))) <= Int64.max_unsigned.
Proof.
  intros Hsz. pose proof (sigTxInBounds (Elements.envTx e)) as Hb. rewrite Zlength_correct in Hb.
  change Int.modulus with 4294967296 in Hb. rewrite ptrofs_max, int64_max. split; [nia|lia].
Qed.

Lemma elements_outputs_fit (e : Elements.env) sz : 0 <= sz <= 1000 ->
  sz * Z.of_nat (length (sigTxOut (Elements.envTx e))) <= Ptrofs.max_unsigned /\
  Z.of_nat (length (sigTxOut (Elements.envTx e))) <= Int64.max_unsigned.
Proof.
  intros Hsz. pose proof (sigTxOutBounds (Elements.envTx e)) as Hb. rewrite Zlength_correct in Hb.
  change Int.modulus with 4294967296 in Hb. rewrite ptrofs_max, int64_max. split; [nia|lia].
Qed.
