(** The 64 rounds of the generated compression body against the functional
    model: one checked lemma per round (same tactic), then the chained result
    [interp_spine 79 body st0 = Some stf] with [sarr stf = SHA256.hash_block]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Maps.
Require sha.SHA256 sha.general_lemmas.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_round C.jet_sha_interp C.jet_sha_compress_fun.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

Ltac use_hw Hw :=
  match goal with
  | |- _ = SHA256.W _ ?z =>
      let j := eval cbv in (Z.to_nat (z mod 16)) in exact (Hw j ltac:(lia) ltac:(lia))
  end.

Ltac w_fact Hw :=
  match goal with
  | |- _ = SHA256.W ?MM ?z => let z' := eval cbv in z in change z with z'
  end;
  first [ solve [rewrite W_first by lia; reflexivity]
        | solve [eapply W_step; [lia | use_hw Hw | use_hw Hw | use_hw Hw | use_hw Hw | reflexivity]] ].

Ltac round_tac t :=
  let st := fresh "st" in
  intros st (Hok & Hwd & Hreg & Hw);
  destruct st as [wv0 wdef0 lv0 ldef0 scratch0 sarr0 chunk0];
  unfold st_ok in Hok; cbn [wv wdef lv ldef sarr chunk] in *;
  destruct Hok as (-> & -> & -> & Lw & Ll); subst wdef0;
  destruct wv0 as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 [|w15 [|? ?]]]]]]]]]]]]]]]]];
    try discriminate Lw;
  destruct lv0 as [|a [|b [|c [|d [|e [|f [|g [|h [|? ?]]]]]]]]]; try discriminate Ll;
  unfold regs_inv in Hreg;
  match type of Hreg with ?L = SHA256.Round ?R ?MM ?z =>
    let L' := eval cbv -[Int.add Int.mul c_sigma0 c_sigma1 c_T1 c_T2 Int.zero] in L in let z' := eval cbv in z in
    change (L' = SHA256.Round R MM z') in Hreg end;
  eexists; split;
  [ let x := eval cbv in (round_stmt t) in change (round_stmt t) with x;
    cbv -[Int.add Int.mul c_sigma0 c_sigma1 c_T1 c_T2 Int.zero]; reflexivity
  | split; [unfold st_ok; cbn [wv wdef lv ldef sarr chunk]; repeat split; reflexivity|];
    split; [reflexivity|];
    split;
    [ unfold regs_inv; cbn [lv];
      match goal with |- ?L = SHA256.Round ?R ?MM ?z =>
        let L' := eval cbv -[Int.add Int.mul c_sigma0 c_sigma1 c_T1 c_T2 Int.zero] in L in let z' := eval cbv in z in
        change (L' = SHA256.Round R MM z') end;
      rewrite SHA256.Round_equation; rewrite zlt_false by lia;
      match goal with |- _ = SHA256.rnd_function (SHA256.Round ?R ?MM ?z) _ _ =>
        let z' := eval cbv in z in change z with z' end;
      rewrite <- Hreg; symmetry;
      apply rnd_function_c; [vm_compute; reflexivity | w_fact Hw]
    | unfold w_inv; cbn [wv]; intros j Hj Hjt;
      do 16 (destruct j as [|j];
        [ match goal with |- ?L = SHA256.W ?MM ?z =>
            let L' := eval cbv -[Int.add Int.mul c_sigma0 c_sigma1 c_T1 c_T2 Int.zero] in L in let z' := eval cbv in z in change (L' = SHA256.W MM z') end;
          first [ use_hw Hw | w_fact Hw | exfalso; lia ] | ]);
      exfalso; lia ] ].

Section Rounds.
Variables r0 r1 r2 r3 r4 r5 r6 r7 : int.
Variables c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : int.
Notation regs := (regs r0 r1 r2 r3 r4 r5 r6 r7).
Notation block := (block c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15).
Notation M := (M c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15).
Notation Inv := (Inv r0 r1 r2 r3 r4 r5 r6 r7 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15).

Definition round_prop (t : nat) : Prop :=
  forall st, Inv t st -> exists st', interp (round_stmt t) (reset st) = Some st' /\ Inv (S t) st'.

Lemma round_0 : round_prop 0.
Proof. unfold round_prop. round_tac 0%nat. Qed.
Lemma round_1 : round_prop 1.
Proof. unfold round_prop. round_tac 1%nat. Qed.
Lemma round_2 : round_prop 2.
Proof. unfold round_prop. round_tac 2%nat. Qed.
Lemma round_3 : round_prop 3.
Proof. unfold round_prop. round_tac 3%nat. Qed.
Lemma round_4 : round_prop 4.
Proof. unfold round_prop. round_tac 4%nat. Qed.
Lemma round_5 : round_prop 5.
Proof. unfold round_prop. round_tac 5%nat. Qed.
Lemma round_6 : round_prop 6.
Proof. unfold round_prop. round_tac 6%nat. Qed.
Lemma round_7 : round_prop 7.
Proof. unfold round_prop. round_tac 7%nat. Qed.
Lemma round_8 : round_prop 8.
Proof. unfold round_prop. round_tac 8%nat. Qed.
Lemma round_9 : round_prop 9.
Proof. unfold round_prop. round_tac 9%nat. Qed.
Lemma round_10 : round_prop 10.
Proof. unfold round_prop. round_tac 10%nat. Qed.
Lemma round_11 : round_prop 11.
Proof. unfold round_prop. round_tac 11%nat. Qed.
Lemma round_12 : round_prop 12.
Proof. unfold round_prop. round_tac 12%nat. Qed.
Lemma round_13 : round_prop 13.
Proof. unfold round_prop. round_tac 13%nat. Qed.
Lemma round_14 : round_prop 14.
Proof. unfold round_prop. round_tac 14%nat. Qed.
Lemma round_15 : round_prop 15.
Proof. unfold round_prop. round_tac 15%nat. Qed.
Lemma round_16 : round_prop 16.
Proof. unfold round_prop. round_tac 16%nat. Qed.
Lemma round_17 : round_prop 17.
Proof. unfold round_prop. round_tac 17%nat. Qed.
Lemma round_18 : round_prop 18.
Proof. unfold round_prop. round_tac 18%nat. Qed.
Lemma round_19 : round_prop 19.
Proof. unfold round_prop. round_tac 19%nat. Qed.
Lemma round_20 : round_prop 20.
Proof. unfold round_prop. round_tac 20%nat. Qed.
Lemma round_21 : round_prop 21.
Proof. unfold round_prop. round_tac 21%nat. Qed.
Lemma round_22 : round_prop 22.
Proof. unfold round_prop. round_tac 22%nat. Qed.
Lemma round_23 : round_prop 23.
Proof. unfold round_prop. round_tac 23%nat. Qed.
Lemma round_24 : round_prop 24.
Proof. unfold round_prop. round_tac 24%nat. Qed.
Lemma round_25 : round_prop 25.
Proof. unfold round_prop. round_tac 25%nat. Qed.
Lemma round_26 : round_prop 26.
Proof. unfold round_prop. round_tac 26%nat. Qed.
Lemma round_27 : round_prop 27.
Proof. unfold round_prop. round_tac 27%nat. Qed.
Lemma round_28 : round_prop 28.
Proof. unfold round_prop. round_tac 28%nat. Qed.
Lemma round_29 : round_prop 29.
Proof. unfold round_prop. round_tac 29%nat. Qed.
Lemma round_30 : round_prop 30.
Proof. unfold round_prop. round_tac 30%nat. Qed.
Lemma round_31 : round_prop 31.
Proof. unfold round_prop. round_tac 31%nat. Qed.
Lemma round_32 : round_prop 32.
Proof. unfold round_prop. round_tac 32%nat. Qed.
Lemma round_33 : round_prop 33.
Proof. unfold round_prop. round_tac 33%nat. Qed.
Lemma round_34 : round_prop 34.
Proof. unfold round_prop. round_tac 34%nat. Qed.
Lemma round_35 : round_prop 35.
Proof. unfold round_prop. round_tac 35%nat. Qed.
Lemma round_36 : round_prop 36.
Proof. unfold round_prop. round_tac 36%nat. Qed.
Lemma round_37 : round_prop 37.
Proof. unfold round_prop. round_tac 37%nat. Qed.
Lemma round_38 : round_prop 38.
Proof. unfold round_prop. round_tac 38%nat. Qed.
Lemma round_39 : round_prop 39.
Proof. unfold round_prop. round_tac 39%nat. Qed.
Lemma round_40 : round_prop 40.
Proof. unfold round_prop. round_tac 40%nat. Qed.
Lemma round_41 : round_prop 41.
Proof. unfold round_prop. round_tac 41%nat. Qed.
Lemma round_42 : round_prop 42.
Proof. unfold round_prop. round_tac 42%nat. Qed.
Lemma round_43 : round_prop 43.
Proof. unfold round_prop. round_tac 43%nat. Qed.
Lemma round_44 : round_prop 44.
Proof. unfold round_prop. round_tac 44%nat. Qed.
Lemma round_45 : round_prop 45.
Proof. unfold round_prop. round_tac 45%nat. Qed.
Lemma round_46 : round_prop 46.
Proof. unfold round_prop. round_tac 46%nat. Qed.
Lemma round_47 : round_prop 47.
Proof. unfold round_prop. round_tac 47%nat. Qed.
Lemma round_48 : round_prop 48.
Proof. unfold round_prop. round_tac 48%nat. Qed.
Lemma round_49 : round_prop 49.
Proof. unfold round_prop. round_tac 49%nat. Qed.
Lemma round_50 : round_prop 50.
Proof. unfold round_prop. round_tac 50%nat. Qed.
Lemma round_51 : round_prop 51.
Proof. unfold round_prop. round_tac 51%nat. Qed.
Lemma round_52 : round_prop 52.
Proof. unfold round_prop. round_tac 52%nat. Qed.
Lemma round_53 : round_prop 53.
Proof. unfold round_prop. round_tac 53%nat. Qed.
Lemma round_54 : round_prop 54.
Proof. unfold round_prop. round_tac 54%nat. Qed.
Lemma round_55 : round_prop 55.
Proof. unfold round_prop. round_tac 55%nat. Qed.
Lemma round_56 : round_prop 56.
Proof. unfold round_prop. round_tac 56%nat. Qed.
Lemma round_57 : round_prop 57.
Proof. unfold round_prop. round_tac 57%nat. Qed.
Lemma round_58 : round_prop 58.
Proof. unfold round_prop. round_tac 58%nat. Qed.
Lemma round_59 : round_prop 59.
Proof. unfold round_prop. round_tac 59%nat. Qed.
Lemma round_60 : round_prop 60.
Proof. unfold round_prop. round_tac 60%nat. Qed.
Lemma round_61 : round_prop 61.
Proof. unfold round_prop. round_tac 61%nat. Qed.
Lemma round_62 : round_prop 62.
Proof. unfold round_prop. round_tac 62%nat. Qed.
Lemma round_63 : round_prop 63.
Proof. unfold round_prop. round_tac 63%nat. Qed.

Lemma round_all t : (t < 64)%nat -> round_prop t.
Proof.
  intros Ht.
  destruct t as [|t]; [exact round_0|].
  destruct t as [|t]; [exact round_1|].
  destruct t as [|t]; [exact round_2|].
  destruct t as [|t]; [exact round_3|].
  destruct t as [|t]; [exact round_4|].
  destruct t as [|t]; [exact round_5|].
  destruct t as [|t]; [exact round_6|].
  destruct t as [|t]; [exact round_7|].
  destruct t as [|t]; [exact round_8|].
  destruct t as [|t]; [exact round_9|].
  destruct t as [|t]; [exact round_10|].
  destruct t as [|t]; [exact round_11|].
  destruct t as [|t]; [exact round_12|].
  destruct t as [|t]; [exact round_13|].
  destruct t as [|t]; [exact round_14|].
  destruct t as [|t]; [exact round_15|].
  destruct t as [|t]; [exact round_16|].
  destruct t as [|t]; [exact round_17|].
  destruct t as [|t]; [exact round_18|].
  destruct t as [|t]; [exact round_19|].
  destruct t as [|t]; [exact round_20|].
  destruct t as [|t]; [exact round_21|].
  destruct t as [|t]; [exact round_22|].
  destruct t as [|t]; [exact round_23|].
  destruct t as [|t]; [exact round_24|].
  destruct t as [|t]; [exact round_25|].
  destruct t as [|t]; [exact round_26|].
  destruct t as [|t]; [exact round_27|].
  destruct t as [|t]; [exact round_28|].
  destruct t as [|t]; [exact round_29|].
  destruct t as [|t]; [exact round_30|].
  destruct t as [|t]; [exact round_31|].
  destruct t as [|t]; [exact round_32|].
  destruct t as [|t]; [exact round_33|].
  destruct t as [|t]; [exact round_34|].
  destruct t as [|t]; [exact round_35|].
  destruct t as [|t]; [exact round_36|].
  destruct t as [|t]; [exact round_37|].
  destruct t as [|t]; [exact round_38|].
  destruct t as [|t]; [exact round_39|].
  destruct t as [|t]; [exact round_40|].
  destruct t as [|t]; [exact round_41|].
  destruct t as [|t]; [exact round_42|].
  destruct t as [|t]; [exact round_43|].
  destruct t as [|t]; [exact round_44|].
  destruct t as [|t]; [exact round_45|].
  destruct t as [|t]; [exact round_46|].
  destruct t as [|t]; [exact round_47|].
  destruct t as [|t]; [exact round_48|].
  destruct t as [|t]; [exact round_49|].
  destruct t as [|t]; [exact round_50|].
  destruct t as [|t]; [exact round_51|].
  destruct t as [|t]; [exact round_52|].
  destruct t as [|t]; [exact round_53|].
  destruct t as [|t]; [exact round_54|].
  destruct t as [|t]; [exact round_55|].
  destruct t as [|t]; [exact round_56|].
  destruct t as [|t]; [exact round_57|].
  destruct t as [|t]; [exact round_58|].
  destruct t as [|t]; [exact round_59|].
  destruct t as [|t]; [exact round_60|].
  destruct t as [|t]; [exact round_61|].
  destruct t as [|t]; [exact round_62|].
  destruct t as [|t]; [exact round_63|].
  exfalso; lia.
Qed.

Lemma run_rounds n : forall k st,
  (k + n <= 64)%nat -> Inv k st ->
  exists st', run (map round_stmt (seq k n)) st = Some st' /\ Inv (k + n) st'.
Proof.
  induction n as [|n IH]; intros k st Hk HI.
  - exists st. split; [reflexivity|]. replace (k + 0)%nat with k by lia. exact HI.
  - cbn [seq map run].
    destruct (round_all k ltac:(lia) st HI) as (st1 & E1 & HI1). rewrite E1.
    destruct (IH (S k) st1 ltac:(lia) HI1) as (st2 & E2 & HI2).
    exists st2. split; [exact E2|]. replace (k + S n)%nat with (S k + n)%nat by lia. exact HI2.
Qed.

Definition sha_st0 : cst := mk_cst (repeat Int.zero 16) 0 (repeat Int.zero 8) 0 [] regs block.

Lemma init_run : exists st8, run (firstn 8 body_elems) sha_st0 = Some st8 /\ Inv 0 st8.
Proof.
  eexists. split.
  - let x := eval cbv in (firstn 8 body_elems) in change (firstn 8 body_elems) with x.
    cbv -[Int.add Int.mul c_sigma0 c_sigma1 c_T1 c_T2 Int.zero]. reflexivity.
  - split; [unfold st_ok; cbn [wv wdef lv ldef sarr chunk]; repeat split; reflexivity|].
    split; [reflexivity|]. split.
    + unfold regs_inv. cbn [lv].
      match goal with |- ?L = SHA256.Round ?R ?MM ?z =>
        let L' := eval cbv -[Int.zero] in L in let z' := eval cbv in z in
        change (L' = SHA256.Round R MM z') end.
      rewrite SHA256.Round_equation. rewrite zlt_true by lia. reflexivity.
    + intros j _ Hj. exfalso; lia.
Qed.

Lemma final_run st :
  Inv 64 st -> exists stf, run (skipn 72 body_elems) st = Some stf /\ sarr stf = SHA256.hash_block regs block.
Proof.
  intros (Hok & Hwd & Hreg & Hw).
  destruct st as [wv0 wdef0 lv0 ldef0 scratch0 sarr0 chunk0].
  unfold st_ok in Hok. cbn [wv wdef lv ldef sarr chunk] in *.
  destruct Hok as (-> & -> & -> & Lw & Ll). subst wdef0.
  destruct wv0 as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 [|w15 [|? ?]]]]]]]]]]]]]]]]];
    try discriminate Lw.
  destruct lv0 as [|a [|b [|c [|d [|e [|f [|g [|h [|? ?]]]]]]]]]; try discriminate Ll.
  unfold regs_inv in Hreg.
  match type of Hreg with ?L = SHA256.Round ?R ?MM ?z =>
    let L' := eval cbv -[Int.add Int.mul c_sigma0 c_sigma1 c_T1 c_T2 Int.zero] in L in
    let z' := eval cbv in z in change (L' = SHA256.Round R MM z') in Hreg end.
  eexists. split.
  - let x := eval cbv in (skipn 72 body_elems) in change (skipn 72 body_elems) with x.
    cbv -[Int.add Int.mul c_sigma0 c_sigma1 c_T1 c_T2 Int.zero]. reflexivity.
  - cbn [sarr]. unfold SHA256.hash_block.
    change (SHA256.nthi block) with M. rewrite <- Hreg.
    cbn [general_lemmas.map2 jet_sha_compress_fun.regs].
    repeat rewrite int_mul_one' by reflexivity. reflexivity.
Qed.

Lemma body_elems_split :
  body_elems = firstn 8 body_elems ++ map round_stmt (seq 0 64) ++ skipn 72 body_elems.
Proof. vm_compute. reflexivity. Qed.

Theorem compress_interp_vars :
  exists stf, interp_spine 79 (fn_body f_sha256_compression_portable) sha_st0 = Some stf /\
    sarr stf = SHA256.hash_block regs block.
Proof.
  rewrite interp_spine_run, body_elems_eq. rewrite body_elems_split, run_app.
  destruct init_run as (st8 & E8 & HI8). rewrite E8. rewrite run_app.
  destruct (run_rounds 64 0 st8 ltac:(lia) HI8) as (st72 & E72 & HI72). rewrite E72.
  exact (final_run st72 HI72).
Qed.
End Rounds.

Theorem compress_interp (regs block : list int) :
  length regs = 8%nat -> length block = 16%nat ->
  exists stf,
    interp_spine 79 (fn_body f_sha256_compression_portable)
      (mk_cst (repeat Int.zero 16) 0 (repeat Int.zero 8) 0 [] regs block) = Some stf /\
    sarr stf = SHA256.hash_block regs block.
Proof.
  intros Hr Hb.
  destruct regs as [|r0 [|r1 [|r2 [|r3 [|r4 [|r5 [|r6 [|r7 [|? ?]]]]]]]]]; try discriminate Hr.
  destruct block as [|c0 [|c1 [|c2 [|c3 [|c4 [|c5 [|c6 [|c7 [|c8 [|c9 [|c10 [|c11 [|c12 [|c13 [|c14 [|c15 [|? ?]]]]]]]]]]]]]]]]];
    try discriminate Hb.
  exact (compress_interp_vars r0 r1 r2 r3 r4 r5 r6 r7 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15).
Qed.
