(** Sequential-state invariants for the literal [forWhile] recursion: when the
    loop state at counter [j] is [S j], the whole counter block returns [S] at
    the end of the block, and the search stops at the first left-returning
    counter.  Generalizes [for_while_run_first_left] to state-carrying loops. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Import C.jet_forWhile_spec C.jet_word_repr.
Local Open Scope ty_scope.
Local Open Scope Z_scope.
Set Implicit Arguments.
Set Default Timeout 20.

Definition wz n (w : tySem (Word n)) : Z := @toZ (WordToZ n) w.
Definition wsize n : Z := 2 ^ Z.of_nat (Nat.pow 2 n).

Lemma wsize_pos n : 0 < wsize n.
Proof. unfold wsize. apply Z.pow_pos_nonneg; lia. Qed.

Lemma wsize_S n : wsize (S n) = wsize n * wsize n.
Proof.
  unfold wsize. rewrite <- Z.pow_add_r by (apply Nat2Z.is_nonneg).
  f_equal. rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma wz_range n (w : tySem (Word n)) : 0 <= wz n w < wsize n.
Proof. unfold wz, wsize. apply word_toZ_range. Qed.

Lemma wz_pair k (hi lo : tySem (Word k)) : wz (S k) (hi, lo) = wz k hi * wsize k + wz k lo.
Proof.
  unfold wz.
  assert (H : @toZ (WordToZ (S k)) (hi, lo) =
    @toZ (WordToZ k) hi * two_power_nat (ToZ.Theory.bitSize (WordToZ k)) + @toZ (WordToZ k) lo)
    by reflexivity.
  rewrite H, two_power_nat_equiv, word_bitSize. reflexivity.
Qed.

Lemma wz_fromZ n z : 0 <= z < wsize n -> wz n (@fromZ (WordToZ n) z) = z.
Proof.
  intros Hz. unfold wz. rewrite to_fromZ, two_power_nat_equiv, word_bitSize.
  apply Z.mod_small. exact Hz.
Qed.

Lemma wz_zero : wz 0 Bit.zero = 0.
Proof. reflexivity. Qed.
Lemma wz_one : wz 0 Bit.one = 1.
Proof. reflexivity. Qed.

Lemma for_while_run_seq_right {C B A : Ty} (S : Z -> tySem A) n base
    (body : tySem (Ty.Prod (Ty.Prod C (Word n)) A) -> option (tySem (Ty.Sum B A)))
    (context : tySem C) :
  (forall w, body ((context, w), S (base + wz n w)) = Some (inr (S (base + wz n w + 1)))) ->
  for_while_run n body context (S base) = Some (inr (S (base + wsize n))).
Proof.
  revert C S base body context. induction n as [|k IH]; intros C S base body context H.
  - pose proof (H Bit.zero) as H0. pose proof (H Bit.one) as H1.
    rewrite wz_zero in H0. rewrite wz_one in H1.
    rewrite Z.add_0_r in H0.
    pose proof H1 as H1'.
    unfold for_while_run.
    refine (eq_trans (f_equal (fun o : option (tySem (Ty.Sum B A)) =>
      match o with Some (inl result) => Some (inl result) | Some (inr next) => body ((context, Bit.one), next)
        | None => None end) H0) _).
    cbv beta iota.
    refine (eq_trans H1' _). unfold wsize. cbn. f_equal. f_equal. f_equal. lia.
  - cbn [for_while_run].
    assert (HS0 : S base = S (base + 0 * wsize k)) by (f_equal; lia).
    assert (HSE : S (base + wsize (Datatypes.S k)) = S (base + 0 + wsize k * wsize k))
      by (f_equal; rewrite wsize_S; lia).
    refine (eq_trans (f_equal (fun st => for_while_run k _ context st) HS0) _).
    refine (eq_trans (IH C (fun j => S (base + j * wsize k)) 0 _ context _) _).
    + intros w. cbv beta. cbn [fst snd].
      assert (Hb : S (base + (0 + wz k w) * wsize k) = S (base + wz k w * wsize k)) by (f_equal; lia).
      refine (eq_trans (f_equal (fun st => @for_while_run k (Ty.Prod C (Word k)) B A _ (context, w) st) Hb) _).
      refine (eq_trans (IH (Ty.Prod C (Word k)) S (base + wz k w * wsize k) _ (context, w) _) _).
      * intros lo. cbn [fst snd].
        pose proof (H (w, lo)) as Hw. rewrite wz_pair in Hw.
        assert (E1 : S (base + (wz k w * wsize k + wz k lo)) = S (base + wz k w * wsize k + wz k lo))
          by (f_equal; lia).
        assert (E2 : S (base + (wz k w * wsize k + wz k lo) + 1) = S (base + wz k w * wsize k + wz k lo + 1))
          by (f_equal; lia).
        rewrite E1, E2 in Hw. exact Hw.
      * replace (base + (0 + wz k w + 1) * wsize k) with (base + wz k w * wsize k + wsize k) by ring. reflexivity.
    + cbv beta. f_equal. f_equal. f_equal. rewrite wsize_S. lia.
Qed.

Lemma for_while_run_seq_left {C B A : Ty} (S : Z -> tySem A) n base T (res : tySem B)
    (body : tySem (Ty.Prod (Ty.Prod C (Word n)) A) -> option (tySem (Ty.Sum B A)))
    (context : tySem C) :
  base <= T < base + wsize n ->
  (forall w, base + wz n w < T -> body ((context, w), S (base + wz n w)) = Some (inr (S (base + wz n w + 1)))) ->
  (forall w, base + wz n w = T -> body ((context, w), S T) = Some (inl res)) ->
  for_while_run n body context (S base) = Some (inl res).
Proof.
  revert C S base T body context. induction n as [|k IH]; intros C S base T body context HT Hb Ht.
  - unfold wsize in HT. cbn in HT.
    destruct (Z.eq_dec T base) as [E|E].
    + subst T. pose proof (Ht Bit.zero) as H0. rewrite wz_zero, Z.add_0_r in H0.
      unfold for_while_run.
      refine (eq_trans (f_equal (fun o : option (tySem (Ty.Sum B A)) =>
        match o with Some (inl result) => Some (inl result) | Some (inr next) => body ((context, Bit.one), next)
          | None => None end) (H0 eq_refl)) _).
      cbv beta iota. reflexivity.
    + assert (E1 : T = base + 1) by lia. subst T.
      pose proof (Hb Bit.zero) as H0. rewrite wz_zero, Z.add_0_r in H0.
      pose proof (Ht Bit.one) as H1. rewrite wz_one in H1.
      unfold for_while_run.
      refine (eq_trans (f_equal (fun o : option (tySem (Ty.Sum B A)) =>
        match o with Some (inl result) => Some (inl result) | Some (inr next) => body ((context, Bit.one), next)
          | None => None end) (H0 ltac:(lia))) _).
      cbv beta iota. exact (H1 eq_refl).
  - cbn [for_while_run].
    pose proof (wsize_pos k) as Hpos.
    set (M := wsize k) in *.
    assert (HTM : 0 <= (T - base) / M < M).
    { rewrite wsize_S in HT. split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
    set (th := (T - base) / M) in *. set (tl := (T - base) mod M) in *.
    assert (Hdm : T - base = th * M + tl) by (subst th tl; rewrite Z.mul_comm; apply Z.div_mod; lia).
    assert (Htl : 0 <= tl < M) by (subst tl; apply Z.mod_pos_bound; lia).
    assert (HS0 : S base = S (base + 0 * M)) by (f_equal; lia).
    refine (eq_trans (f_equal (fun st => for_while_run k _ context st) HS0) _).
    refine (IH C (fun j => S (base + j * M)) 0 th _ context _ _ _).
    + split; [lia|]. unfold wsize in *. lia.
    + intros w Hw. cbv beta. cbn [fst snd].
      assert (Hbw : S (base + (0 + wz k w) * M) = S (base + wz k w * M)) by (f_equal; lia).
      refine (eq_trans (f_equal (fun st => @for_while_run k (Ty.Prod C (Word k)) B A _ (context, w) st) Hbw) _).
      refine (eq_trans (@for_while_run_seq_right (Ty.Prod C (Word k)) B A S k (base + wz k w * M) _ (context, w) _) _).
      * intros lo. cbn [fst snd].
        pose proof (Hb (w, lo)) as Hw'. rewrite wz_pair in Hw'. change (wsize k) with M in Hw'.
        assert (E1 : S (base + (wz k w * M + wz k lo)) = S (base + wz k w * M + wz k lo)) by (f_equal; lia).
        assert (E2 : S (base + (wz k w * M + wz k lo) + 1) = S (base + wz k w * M + wz k lo + 1)) by (f_equal; lia).
        rewrite E1, E2 in Hw'. apply Hw'.
        pose proof (wz_range k lo). nia.
      * replace (base + (0 + wz k w + 1) * M) with (base + wz k w * M + M) by ring. reflexivity.
    + intros w Hw. cbv beta. cbn [fst snd].
      assert (Hwth : wz k w = th) by lia.
      assert (Hbw : S (base + th * M) = S (base + wz k w * M)) by (f_equal; rewrite Hwth; lia).
      refine (eq_trans (f_equal (fun st => @for_while_run k (Ty.Prod C (Word k)) B A _ (context, w) st) Hbw) _).
      refine (IH (Ty.Prod C (Word k)) S (base + wz k w * M) T _ (context, w) _ _ _).
      * rewrite Hwth. lia.
      * intros lo Hlo. cbn [fst snd].
        pose proof (Hb (w, lo)) as Hw'. rewrite wz_pair in Hw'. change (wsize k) with M in Hw'.
        assert (E1 : S (base + (wz k w * M + wz k lo)) = S (base + wz k w * M + wz k lo)) by (f_equal; lia).
        assert (E2 : S (base + (wz k w * M + wz k lo) + 1) = S (base + wz k w * M + wz k lo + 1)) by (f_equal; lia).
        rewrite E1, E2 in Hw'. apply Hw'. nia.
      * intros lo Hlo. cbn [fst snd].
        pose proof (Ht (w, lo)) as Hw'. rewrite wz_pair in Hw'. change (wsize k) with M in Hw'.
        assert (E1 : base + (wz k w * M + wz k lo) = T) by lia.
        apply Hw' in E1.
        refine (eq_trans (f_equal (fun st => body (_, st)) _) E1). reflexivity.
Qed.

