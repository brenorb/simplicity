(** Memory-aware termination of the actual div_mod_96_64 correction loop.
    All stores and recursive execution premises are derived, not assumed.
    The helper function's entry, initialization and final store remain separate. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_divmod96_arith C.jet_divmod96_value.
Require Import C.jet_divmod96_step C.jet_divmod96_loop.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition divmod96_denominator bh bl :=
  Int64.unsigned bh * divmod96_radix + Int64.unsigned bl.
Definition divmod96_delta rh al d :=
  divmod96_radix * Int64.unsigned rh + Int64.unsigned al - Int64.unsigned d.
Definition divmod96_loop_inv ah al bh bl q rh d :=
  0 <= Int64.unsigned q < divmod96_radix /\
  ah = Int64.unsigned q * Int64.unsigned bh + Int64.unsigned rh /\
  Int64.unsigned d = Int64.unsigned q * Int64.unsigned bl /\
  divmod96_delta rh al d < divmod96_denominator bh bl.
Definition divmod96_loop_env le bq ofs rh bh al d bl :=
  le!_q = Some (Vptr bq ofs) /\ le!_rh = Some (Vlong rh) /\ le!_bh = Some (Vlong bh) /\
  le!_al = Some (Vlong al) /\ le!_d = Some (Vlong d) /\ le!_bl = Some (Vlong bl).

Lemma divmod96_loop_inv_step ah al bh bl q rh d :
  ah < Int64.modulus -> 0 < Int64.unsigned bh < divmod96_radix ->
  Int64.unsigned bl < divmod96_radix -> Int64.unsigned al < divmod96_radix ->
  divmod96_loop_inv ah al bh bl q rh d -> divmod96_guard rh al d = Datatypes.true ->
  divmod96_loop_inv ah al bh bl (Int64.sub q Int64.one) (Int64.add rh bh) (Int64.sub d bl) /\
  divmod96_delta (Int64.add rh bh) al (Int64.sub d bl) =
    divmod96_delta rh al d + divmod96_denominator bh bl.
Proof.
  intros Hah Hbh Hbl Hal [Hq [Hbalance [Hd Hupper]]] HG.
  set (B := divmod96_radix). set (D := divmod96_denominator bh bl).
  assert (HB : 2 <= B) by (unfold B, divmod96_radix; lia).
  pose proof (Int64.unsigned_range rh) as HR. pose proof (Int64.unsigned_range bl) as HBL.
  pose proof (Int64.unsigned_range al) as HAL.
  assert (Hdb : Int64.unsigned d < B * B) by (unfold B; nia).
  pose proof (proj1 (divmod96_guard_negative rh al d Hal Hdb) HG) as Hnegative.
  assert (HA0 : 0 <= ah) by nia.
  destruct (divmod96_correction_step B ah (Int64.unsigned al) D (Int64.unsigned bh)
    (Int64.unsigned bl) (Int64.unsigned q) (Int64.unsigned rh) (Int64.unsigned d)
    (divmod96_delta rh al d) HB HA0 ltac:(unfold B; lia) Hbh ltac:(unfold B; lia)
    eq_refl Hq ltac:(lia) Hbalance Hd eq_refl Hnegative)
    as (HQnext & HRnext & HbalanceNext & HDnext & HdNext & HdeltaNext & HupperNext).
  destruct (divmod96_machine_step_values q rh bh d bl ltac:(lia) ltac:(lia) ltac:(lia))
    as [HQvalue [HRvalue HDvalue]].
  split.
  - unfold divmod96_loop_inv, divmod96_delta. rewrite HQvalue, HRvalue, HDvalue.
    split; [exact HQnext|]. split; [exact HbalanceNext|]. split; [exact HdNext|].
    fold B D. rewrite HdeltaNext. exact HupperNext.
  - unfold divmod96_delta. rewrite HRvalue, HDvalue. exact HdeltaNext.
Qed.

Definition divmod96_loop_result e le m bq ofs ah al bh bl :=
  exists mf lef qf rhf df,
    Clight2.exec_stmt ge0 e le m divmod96_loop_stmt E0 lef mf Out_normal /\
    divmod96_loop_env lef bq ofs rhf bh al df bl /\
    Mem.load Mint64 mf bq (Ptrofs.unsigned ofs) = Some (Vlong qf) /\
    divmod96_loop_inv ah al bh bl qf rhf df /\ 0 <= divmod96_delta rhf al df /\
    (forall id, id <> _t'2 -> id <> _t'3 -> id <> _rh -> id <> _d -> lef!id = le!id) /\
    (forall chunk b addr,
      b <> bq \/ addr + size_chunk chunk <= Ptrofs.unsigned ofs \/ Ptrofs.unsigned ofs + 8 <= addr ->
      Mem.load chunk mf b addr = Mem.load chunk m b addr) /\
    (forall b addr kind p, Mem.perm m b addr kind p -> Mem.perm mf b addr kind p) /\
    Mem.nextblock mf = Mem.nextblock m.

Lemma divmod96_loop_result_exit e le m bq ofs ah al bh bl q rh d :
  Int64.unsigned bl < divmod96_radix -> Int64.unsigned al < divmod96_radix ->
  divmod96_loop_env le bq ofs rh bh al d bl ->
  Mem.load Mint64 m bq (Ptrofs.unsigned ofs) = Some (Vlong q) ->
  divmod96_loop_inv ah al bh bl q rh d -> divmod96_guard rh al d = Datatypes.false ->
  divmod96_loop_result e le m bq ofs ah al bh bl.
Proof.
  intros Hbl Hal Henv HL Hinv HG.
  destruct Henv as (HQ & HR & HB & HA & HD & HBL).
  assert (Hdb : Int64.unsigned d < divmod96_radix * divmod96_radix).
  { destruct Hinv as [Hq [_ [Hd _]]]. pose proof (Int64.unsigned_range bl). nia. }
  assert (Hdelta : 0 <= divmod96_delta rh al d).
  { destruct (Z_lt_ge_dec (divmod96_delta rh al d) 0) as [Hneg|Hnonneg]; [|lia].
    pose proof (proj2 (divmod96_guard_negative rh al d Hal Hdb) Hneg) as Htrue.
    congruence. }
  exists m, (PTree.set _t'2 (Vint Int.zero) le), q, rh, d.
  split; [eapply exec_divmod96_loop_exit; eauto|]. split.
  - unfold divmod96_loop_env. rewrite !PTree.gso by discriminate. repeat split; assumption.
  - split; [exact HL|]. split; [exact Hinv|]. split; [exact Hdelta|].
    split.
    + intros id H2 H3 HRid HDid. rewrite PTree.gso by congruence. reflexivity.
    + split; [intros; reflexivity|]. split; [auto|reflexivity].
Qed.

Theorem eval_divmod96_loop_layout fuel e le m bq ofs ah al bh bl q rh d :
  ah < Int64.modulus -> 0 < Int64.unsigned bh < divmod96_radix ->
  Int64.unsigned bl < divmod96_radix -> Int64.unsigned al < divmod96_radix ->
  divmod96_loop_env le bq ofs rh bh al d bl ->
  Mem.load Mint64 m bq (Ptrofs.unsigned ofs) = Some (Vlong q) ->
  Mem.valid_access m Mint64 bq (Ptrofs.unsigned ofs) Writable ->
  divmod96_loop_inv ah al bh bl q rh d ->
  - Z.of_nat fuel * divmod96_denominator bh bl <= divmod96_delta rh al d ->
  divmod96_loop_result e le m bq ofs ah al bh bl.
Proof.
  intros Hah Hbh Hbl Hal. revert e le m q rh d.
  induction fuel as [|fuel IH]; intros e le m q rh d Henv HL HP Hinv Hlower.
  - assert (HG : divmod96_guard rh al d = Datatypes.false).
    { destruct (divmod96_guard rh al d) eqn:HG; [|reflexivity].
      assert (Hdb : Int64.unsigned d < divmod96_radix * divmod96_radix).
      { destruct Hinv as [Hq [_ [Hd _]]]. pose proof (Int64.unsigned_range bl); nia. }
      pose proof (proj1 (divmod96_guard_negative rh al d Hal Hdb) HG) as Hneg.
      change (-0 * divmod96_denominator bh bl <= divmod96_delta rh al d) in Hlower.
      unfold divmod96_delta in Hlower. lia. }
    eapply divmod96_loop_result_exit; eauto.
  - destruct (divmod96_guard rh al d) eqn:HG.
    + pose proof (divmod96_loop_inv_step ah al bh bl q rh d Hah Hbh Hbl Hal Hinv HG)
        as [HinvNext HdeltaNext].
      set (qnext := Int64.sub q Int64.one).
      set (rhnext := Int64.add rh bh). set (dnext := Int64.sub d bl).
      destruct (Mem.valid_access_store m Mint64 bq (Ptrofs.unsigned ofs) (Vlong qnext) HP) as [ms HS].
      assert (HLnext : Mem.load Mint64 ms bq (Ptrofs.unsigned ofs) = Some (Vlong qnext)).
      { rewrite (Mem.load_store_same Mint64 m bq (Ptrofs.unsigned ofs) (Vlong qnext) ms HS). reflexivity. }
      assert (HPnext : Mem.valid_access ms Mint64 bq (Ptrofs.unsigned ofs) Writable).
      { eapply Mem.store_valid_access_1; eauto. }
      assert (HenvNext : divmod96_loop_env (divmod96_next_env le q rh bh d bl) bq ofs rhnext bh al dnext bl).
      { destruct Henv as (HQ & HR & HB & HA & HD & HBL).
        unfold divmod96_loop_env, divmod96_next_env.
        repeat split; repeat first [rewrite PTree.gss | rewrite PTree.gso by discriminate];
          first [reflexivity | assumption]. }
      assert (HlowerNext : - Z.of_nat fuel * divmod96_denominator bh bl <= divmod96_delta rhnext al dnext).
      { change (-Z.of_nat fuel * divmod96_denominator bh bl <=
          divmod96_delta (Int64.add rh bh) al (Int64.sub d bl)).
        rewrite HdeltaNext. rewrite Nat2Z.inj_succ in Hlower.
        replace (-Z.succ (Z.of_nat fuel) * divmod96_denominator bh bl) with
          (-Z.of_nat fuel * divmod96_denominator bh bl - divmod96_denominator bh bl) in Hlower by ring.
        lia. }
      destruct (IH e (divmod96_next_env le q rh bh d bl) ms qnext rhnext dnext
        HenvNext HLnext HPnext HinvNext HlowerNext)
        as (mf & lef & qf & rhf & df & Htail & HenvFinal & HLfinal & HinvFinal & HdeltaFinal & HtempsFinal & HmemFinal & HpermFinal & HnextFinal).
      exists mf, lef, qf, rhf, df. split.
      * destruct Henv as (HQ & HR & HB & HA & HD & HBL).
        eapply exec_divmod96_loop_take; eauto.
      * split; [exact HenvFinal|]. split; [exact HLfinal|]. split; [exact HinvFinal|].
        split; [exact HdeltaFinal|]. split.
        -- intros id H2 H3 HRid HDid. rewrite HtempsFinal by assumption.
           unfold divmod96_next_env. rewrite !PTree.gso by congruence. reflexivity.
        -- split.
           ++ intros chunk b addr Houtside. rewrite HmemFinal by exact Houtside.
           erewrite Mem.load_store_other; [reflexivity|exact HS|].
           change (b <> bq \/ addr + size_chunk chunk <= Ptrofs.unsigned ofs \/ Ptrofs.unsigned ofs + 8 <= addr).
           exact Houtside.
           ++ split.
              ** intros b addr kind p Hperm. apply HpermFinal. eapply Mem.perm_store_1; eauto.
              ** rewrite HnextFinal. eapply Mem.nextblock_store; exact HS.
    + eapply divmod96_loop_result_exit; eauto.
Qed.
