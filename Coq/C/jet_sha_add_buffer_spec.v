(** Literal port of Programs.Sha256.mkLibAssert.ctx8AddBuffer and its option
    semantics: the bytes of the buffer are added to the context; an empty
    buffer still verifies the compression count. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Integers.
Require sha.SHA256 sha.common_lemmas.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Simplicity.Alg Simplicity.SHA256.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_assertion_spec C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha256_count_assertion C.jet_sha_ctx8_spec C.jet_sha_ctx8_model C.jet_sha_ctx8_bridge.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

(** ctx8AddBuffer SingleB =
      ih &&& oh >>> match (drop (iden &&& verifyNumCompression >>> oh)) (ih &&& oh >>> ctx8Add1)
    ctx8AddBuffer (DoubleB b) =
      (ioh &&& oh >>> match ih (ih &&& oh >>> ctx8Addn (bufferVector b))) &&& iih >>> ctx8AddBuffer b *)
Fixpoint ctx8_add_buffer_spec (d : nat) {term : Alg.Assertion.Algebra} :
    @Alg.Assertion.domain term (Ty.Prod sha256_ctx8_type (buffer_type (Word 3) d)) sha256_ctx8_type :=
  match d with
  | O =>
      @AC.comp _ _ _ (Alg.Assertion.toCore term) (AC.pair (AC.drop AC.iden) (AC.take AC.iden))
        (@AC.case _ _ _ _ (Alg.Assertion.toCore term)
          (@AC.drop _ _ _ (Alg.Assertion.toCore term)
            (@AC.comp _ _ _ (Alg.Assertion.toCore term)
              (@AC.pair _ _ _ (Alg.Assertion.toCore term) AC.iden (@sha256_count_assertion_spec term))
              (AC.take AC.iden)))
          (@AC.comp _ _ _ (Alg.Assertion.toCore term) (AC.pair (AC.drop AC.iden) (AC.take AC.iden))
            (@ctx8_add1_spec term)))
  | S d' =>
      @AC.comp _ _ _ (Alg.Assertion.toCore term)
        (@AC.pair _ _ _ (Alg.Assertion.toCore term)
          (@AC.comp _ _ _ (Alg.Assertion.toCore term)
            (AC.pair (AC.drop (AC.take AC.iden)) (AC.take AC.iden))
            (@AC.case _ _ _ _ (Alg.Assertion.toCore term) (AC.drop AC.iden)
              (@AC.comp _ _ _ (Alg.Assertion.toCore term) (AC.pair (AC.drop AC.iden) (AC.take AC.iden))
                (@ctx8_addn_spec (S d') term))))
          (AC.drop (AC.drop AC.iden)))
        (@ctx8_add_buffer_spec d' term)
  end.

Lemma ctx8_add_buffer_spec_parametric d : Alg.Assertion.Parametric (@ctx8_add_buffer_spec d).
Proof.
  induction d.
  - intros alg1 alg2 R. pose proof (ctx8_add1_spec_parametric alg1 alg2 R) as HAdd.
    pose proof (sha256_count_assertion_parametric alg1 alg2 R) as HCount.
    destruct R as [R [HC HA]]. cbn [ctx8_add_buffer_spec].
    set (RC := Alg.Core.Parametric.Pack HC).
    apply (Alg.comp_Parametric RC).
    + apply (Alg.pair_Parametric RC); [apply (Alg.drop_Parametric RC)|apply (Alg.take_Parametric RC)];
        apply Alg.iden_Parametric.
    + apply (Alg.case_Parametric RC).
      * apply (Alg.drop_Parametric RC). apply (Alg.comp_Parametric RC).
        -- apply (Alg.pair_Parametric RC); [apply Alg.iden_Parametric|exact HCount].
        -- apply (Alg.take_Parametric RC), Alg.iden_Parametric.
      * apply (Alg.comp_Parametric RC); [|exact HAdd].
        apply (Alg.pair_Parametric RC); [apply (Alg.drop_Parametric RC)|apply (Alg.take_Parametric RC)];
          apply Alg.iden_Parametric.
  - intros alg1 alg2 R. pose proof (IHd alg1 alg2 R) as HRec.
    pose proof (ctx8_addn_spec_parametric (S d) alg1 alg2 R) as HAdd.
    destruct R as [R [HC HA]]. cbn [ctx8_add_buffer_spec].
    set (RC := Alg.Core.Parametric.Pack HC).
    apply (Alg.comp_Parametric RC); [|exact HRec].
    apply (Alg.pair_Parametric RC).
    + apply (Alg.comp_Parametric RC).
      * apply (Alg.pair_Parametric RC);
          [apply (Alg.drop_Parametric RC), (Alg.take_Parametric RC)|apply (Alg.take_Parametric RC)];
          apply Alg.iden_Parametric.
      * apply (Alg.case_Parametric RC); [apply (Alg.drop_Parametric RC), Alg.iden_Parametric|].
        apply (Alg.comp_Parametric RC); [|exact HAdd].
        apply (Alg.pair_Parametric RC); [apply (Alg.drop_Parametric RC)|apply (Alg.take_Parametric RC)];
          apply Alg.iden_Parametric.
    + apply (Alg.drop_Parametric RC), (Alg.drop_Parametric RC), Alg.iden_Parametric.
Qed.

Definition ctx8_count (c : Ty.tySem sha256_ctx8_type) : Z := @toZ (WordToZ 6) (fst (snd c)).

Fixpoint ctx8_add_buffer_model (d : nat) (c : Ty.tySem sha256_ctx8_type) :
    Ty.tySem (buffer_type (Word 3) d) -> option (Ty.tySem sha256_ctx8_type) :=
  match d return Ty.tySem (buffer_type (Word 3) d) -> option (Ty.tySem sha256_ctx8_type) with
  | O => fun b =>
      match b with
      | inl _ => if ctx8_count c <? ctx8_limit then Some c else None
      | inr x => ctx8_add1_model c x
      end
  | S d' => fun b =>
      match fst b with
      | inl _ => ctx8_add_buffer_model d' c (snd b)
      | inr v =>
          match ctx8_add_list c (vector_values (Word 3) (S d') v) with
          | Some c' => ctx8_add_buffer_model d' c' (snd b)
          | None => None
          end
      end
  end.

Ltac opt_steps :=
  repeat progress (cbv beta iota; cbn [fst snd];
    rewrite ?opt_pair, ?opt_comp, ?opt_take, ?opt_drop, ?opt_iden, ?opt_case).

Lemma ctx8_add_buffer_option d : forall (c : Ty.tySem sha256_ctx8_type)
    (b : Ty.tySem (buffer_type (Word 3) d)),
  @ctx8_add_buffer_spec d optalg (c, b) = ctx8_add_buffer_model d c b.
Proof.
  induction d; intros c b.
  - cbn [ctx8_add_buffer_spec ctx8_add_buffer_model].
    destruct b as [u|x]; opt_steps.
    + destruct c as [buf [count h]]. rewrite sha256_count_assertion_option.
      unfold ctx8_count, ctx8_limit. cbn [fst snd].
      destruct (@toZ (WordToZ 6) count <? 36028797018963968); reflexivity.
    + apply ctx8_add1_option.
  - destruct b as [sv b0]. cbn [ctx8_add_buffer_spec ctx8_add_buffer_model fst snd].
    destruct sv as [u|v]; opt_steps.
    + apply IHd.
    + rewrite ctx8_addn_option.
      destruct (ctx8_add_list c (vector_values (Word 3) (S d) v)) as [c'|]; [|reflexivity].
      opt_steps. apply IHd.
Qed.

Lemma ctx8_add1_some_count c x c' :
  ctx8_add1_model c x = Some c' -> ctx8_count c' < ctx8_limit.
Proof.
  destruct c as [buf [count h]]. unfold ctx8_add1_model.
  match goal with |- context[@buffer_snoc_spec ?X ?d ?alg ?p] =>
    destruct (@buffer_snoc_spec X d alg p) as [blk|buf'] end.
  - match goal with |- (if ?b then _ else _) = _ -> _ => destruct b eqn:HL end; [|discriminate].
    apply Z.ltb_lt in HL. intros HS. injection HS as <-. unfold ctx8_count. cbn [fst snd].
    pose proof (word64_range count) as HR.
    rewrite (@to_fromZ (WordToZ 6)), word64_pow. rewrite Z.mod_small; [exact HL|].
    unfold ctx8_limit in HL. lia.
  - match goal with |- (if ?b then _ else _) = _ -> _ => destruct b eqn:HL end; [|discriminate].
    apply Z.ltb_lt in HL. intros HS. injection HS as <-. exact HL.
Qed.

Lemma ctx8_add_list_some_count l : forall c c', l <> [] ->
  ctx8_add_list c l = Some c' -> ctx8_count c' < ctx8_limit.
Proof.
  induction l as [|x l IH]; intros c c' Hne HS; [contradiction|].
  cbn [ctx8_add_list] in HS. destruct (ctx8_add1_model c x) as [c1|] eqn:E1; [|discriminate].
  destruct l as [|y l'].
  - cbn in HS. injection HS as <-. eapply ctx8_add1_some_count; exact E1.
  - eapply IH; [discriminate|exact HS].
Qed.

Lemma ctx8_add_buffer_model_list d : forall (c : Ty.tySem sha256_ctx8_type)
    (b : Ty.tySem (buffer_type (Word 3) d)),
  (buffer_list (Word 3) d b = [] ->
     ctx8_add_buffer_model d c b = if ctx8_count c <? ctx8_limit then Some c else None) /\
  (buffer_list (Word 3) d b <> [] ->
     ctx8_add_buffer_model d c b = ctx8_add_list c (buffer_list (Word 3) d b)).
Proof.
  induction d; intros c b.
  - destruct b as [u|x]; cbn [ctx8_add_buffer_model buffer_list]; split; intros H;
      try reflexivity; try discriminate; try contradiction.
    cbn [ctx8_add_list]. destruct (ctx8_add1_model c x); reflexivity.
  - destruct b as [sv b0]. cbn [ctx8_add_buffer_model buffer_list fst snd].
    destruct sv as [u|v].
    + cbn [app]. apply IHd.
    + pose proof (vector_values_length (Word 3) (S d) v) as HV.
      assert (Hvne : vector_values (Word 3) (S d) v <> []).
      { intro HN. rewrite HN in HV. cbn in HV. pose proof (Nat.pow_nonzero 2 d ltac:(lia)). lia. }
      split.
      * intros HN. apply app_eq_nil in HN. destruct HN as [HN _]. contradiction.
      * intros _. rewrite ctx8_add_list_app.
        destruct (ctx8_add_list c (vector_values (Word 3) (S d) v)) as [c'|] eqn:EA; [|reflexivity].
        destruct (IHd c' b0) as [IH1 IH2].
        destruct (buffer_list (Word 3) d b0) as [|y l0] eqn:EB.
        -- rewrite (IH1 eq_refl). cbn [ctx8_add_list].
           pose proof (ctx8_add_list_some_count _ _ _ Hvne EA) as HC.
           apply Z.ltb_lt in HC. rewrite HC. reflexivity.
        -- apply IH2. discriminate.
Qed.

Theorem ctx8_add_values (buf : Ty.tySem (buffer_type (Word 3) 5)) (count : Ty.tySem (Word 6))
    (state : Ty.tySem (Word 8)) (vs : list (Ty.tySem (Word 3))) :
  let lbuf := buffer_list (Word 3) 5 buf in
  let regs := state_regs state in
  let total := @toZ (WordToZ 6) count + (Z.of_nat (length lbuf) + Z.of_nat (length vs)) / 64 in
  let result :=
    match vs with
    | [] => if @toZ (WordToZ 6) count <? ctx8_limit then Some (buf, (count, state)) else None
    | _ => ctx8_add_list (buf, (count, state)) vs
    end in
  exists (buf' : Ty.tySem (buffer_type (Word 3) 5)) (h' : Ty.tySem (Word 8)),
    buffer_list (Word 3) 5 buf' = fst (absorb lbuf regs vs) /\
    state_regs h' = snd (absorb lbuf regs vs) /\
    result = if total <? ctx8_limit then Some (buf', (@fromZ (WordToZ 6) total, h')) else None.
Proof.
  intros lbuf regs total result.
  pose proof (buffer_list_length (Word 3) 5 buf) as HL. change (Nat.pow 2 6) with 64%nat in HL. fold lbuf in HL.
  destruct vs as [|v0 vs'].
  - exists buf, state. split; [reflexivity|]. split; [reflexivity|].
    assert (HT : total = @toZ (WordToZ 6) count).
    { unfold total. cbn [length]. rewrite Z.add_0_r, Z.div_small by lia. lia. }
    unfold result. rewrite HT, (@from_toZ (WordToZ 6) count). reflexivity.
  - assert (Hne : v0 :: vs' <> []) by discriminate.
    pose proof (ctx8_add_list_closed (v0 :: vs') buf count state Hne) as HClosed. cbv zeta in HClosed.
    destruct HClosed as [HCa HCb].
    change (exists (buf' : Ty.tySem (buffer_type (Word 3) 5)) (h' : Ty.tySem (Word 8)),
      buffer_list (Word 3) 5 buf' = fst (absorb lbuf regs (v0 :: vs')) /\
      state_regs h' = snd (absorb lbuf regs (v0 :: vs')) /\
      ctx8_add_list (buf, (count, state)) (v0 :: vs') =
        (if total <? ctx8_limit then Some (buf', (@fromZ (WordToZ 6) total, h')) else None)).
    destruct (Z.ltb_spec total ctx8_limit) as [HT|HT].
    + destruct (HCa HT) as (buf' & h' & HS1 & HS2 & HS3). exists buf', h'. auto.
    + destruct (absorb_length (v0 :: vs') lbuf regs HL) as [_ HltA].
      destruct (buffer_exists (Word 3) 5 (fst (absorb lbuf regs (v0 :: vs')))
        ltac:(change (Nat.pow 2 6) with 64%nat; exact HltA)) as [buf' Hb'].
      assert (Hlr : length regs = 8%nat).
      { unfold regs, state_regs. rewrite map_length. apply (jet_word32_chunks.word32_chunks_length 3). }
      assert (HrA : forall vs (lb : list (Ty.tySem (Word 3))) rg, (length lb < 64)%nat -> length rg = 8%nat ->
        length (snd (absorb lb rg vs)) = 8%nat).
      { clear. induction vs as [|x vs IH]; intros lb rg HL Hlr; [exact Hlr|].
        destruct (Nat.eq_dec (length lb) 63) as [E|E].
        - rewrite absorb_cons_full by exact E. apply IH; [cbn; lia|].
          apply sha.common_lemmas.length_hash_block; [exact Hlr|].
          apply jet_sha_be32_exec.be_words_length. rewrite map_length, app_length. cbn [length]. lia.
        - rewrite absorb_cons_small by lia. apply IH; [rewrite app_length; cbn [length]; lia|exact Hlr]. }
      destruct (state_exists _ (HrA (v0 :: vs') lbuf regs HL Hlr)) as [h' Hh'].
      exists buf', h'. split; [exact Hb'|]. split; [exact Hh'|]. apply HCb. exact HT.
Qed.
