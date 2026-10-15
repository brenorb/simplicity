(** Literal historical brokenTxLockDistance/Duration. These fold over all
    input sequences, not Bitcoin's current-input relative-lock program. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Require Import C.jet_elements_prim C.jet_forWhile_fold C.jet_forWhile_spec C.jet_forWhile_seq.
Require Import C.jet_word_repr C.jet_minmax_spec C.jet_parse_sequence_spec.
Require Import C.jet_bitcoin_distance_spec C.jet_haskell_word_conversion C.jet_order_spec.
Require Import C.jet_elements_prim_sem C.jet_elements_current_spec.
Require Import C.jet_elements_is_final_spec.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition legacy_parse_tail (distance : bool) {alg : Core.Algebra} :
    alg ((Ty.Unit + (Word16 + Word16)) * Word16) Word16 :=
  case (drop iden) (if distance then case (@minmax_word_spec 4 Datatypes.true alg) (drop iden)
                   else case (drop iden) (@minmax_word_spec 4 Datatypes.true alg)).

Definition legacy_fold_body (distance : bool) {alg : Core.Algebra}
    (op : alg Word32 (Ty.Unit + Word32)) :
    alg ((Ty.Unit * Word32) * Word16) (Word16 + Word16) :=
  (take (drop op) &&& drop iden) >>>
    case (injl (drop iden))
      (injr ((take (@parse_sequence_spec alg) &&& drop iden) >>> legacy_parse_tail distance)).

Definition legacy_version_check {alg : Core.Algebra} (version : alg Ty.Unit Word32) : alg Ty.Unit Bit :=
  (Alg.scribe (haskell_to_word 5 2) &&& version) >>> @le_word_spec alg 5.

Definition legacy_fold_finish (distance : bool) {alg : Core.Algebra}
    (op : alg Word32 (Ty.Unit + Word32)) : alg (Bit * Word16) Word16 :=
  case (drop iden) (for_while_program 5 (legacy_fold_body distance op) >>> copair iden iden).

Definition legacy_fold_program (distance : bool) {alg : Core.Algebra}
    (version : alg Ty.Unit Word32) (op : alg Word32 (Ty.Unit + Word32)) :
    alg Ty.Unit Word16 :=
  (legacy_version_check version &&& zero (n := 4)) >>>
    legacy_fold_finish distance op.

Definition elements_legacy_lock_spec (distance : bool) {alg : Primitive.Algebra} :
    alg Ty.Unit Word16 :=
  legacy_fold_program distance (Primitive.Combinators.prim Elements.Version)
    (Primitive.Combinators.prim Elements.InputSequence).

Lemma legacy_parse_tail_parametric distance :
  Core.Parametric (fun alg => @legacy_parse_tail distance alg).
Proof.
  intros alg1 alg2 R. unfold legacy_parse_tail. apply case_Parametric.
  - auto with parametricity.
  - destruct distance; apply case_Parametric;
      first [apply minmax_word_spec_parametric|auto with parametricity].
Qed.

Lemma legacy_parse_tail_reader distance {E : Type}
    (x : tySem ((Ty.Unit + (Word16 + Word16)) * Word16)) (environment : E) :
  @legacy_parse_tail distance (CoreSem (ReaderT_CIMonad E option_CIMonad)) x environment =
    Some (@legacy_parse_tail distance CoreFunSem x).
Proof.
  exact (@core_reader_sem _ _ (fun alg => @legacy_parse_tail distance alg)
    (legacy_parse_tail_parametric distance) E x environment).
Qed.

Definition legacy_word_step (distance : bool) (a : tySem Word16) (x : tySem Word32) :=
  @legacy_parse_tail distance CoreFunSem (@parse_sequence_spec CoreFunSem x, a).

Definition legacy_reader_step (distance : bool)
    (op : tySem Word32 -> option (tySem (Ty.Unit + Word32)))
    (p : tySem ((Ty.Unit * Word32) * Word16)) : option (tySem (Word16 + Word16)) :=
  match op (snd (fst p)) with
  | Some (inl _) => Some (inl (snd p))
  | Some (inr x) => Some (inr (legacy_word_step distance (snd p) x))
  | None => None
  end.

Lemma legacy_fold_body_reader distance {E : Type}
    (op : CoreSem (ReaderT_CIMonad E option_CIMonad) Word32 (Ty.Unit + Word32))
    (p : tySem ((Ty.Unit * Word32) * Word16)) (environment : E) :
  legacy_fold_body distance op p environment =
    legacy_reader_step distance (fun w => op w environment) p.
Proof.
  destruct p as [[[] w] a]. unfold legacy_fold_body, legacy_reader_step, legacy_word_step.
  destruct (op w environment) as [[u | x] | ] eqn:HO.
  - lazy beta iota zeta delta -[parse_sequence_spec legacy_parse_tail] in HO |- *.
    rewrite HO. reflexivity.
  - pose proof (@core_reader_sem _ _ (@parse_sequence_spec) parse_sequence_spec_parametric E x environment) as HP.
    pose proof (legacy_parse_tail_reader distance (@parse_sequence_spec CoreFunSem x, a) environment) as HT.
    lazy beta iota zeta delta -[parse_sequence_spec legacy_parse_tail] in HO, HP, HT |- *.
    rewrite HO, HP, HT. reflexivity.
  - lazy beta iota zeta delta -[parse_sequence_spec legacy_parse_tail] in HO |- *.
    rewrite HO. reflexivity.
Qed.

Lemma legacy_fold_reader_list distance {X : Type} (xs : list X)
    (enc : X -> tySem Word32)
    (op : CoreSem (ReaderT_CIMonad Elements.env option_CIMonad) Word32 (Ty.Unit + Word32)) environment a :
  Z.of_nat (length xs) < wsize 5 ->
  (forall w, op w environment = Some
    (match nth_error xs (Z.to_nat (wz 5 w)) with Some x => inr (enc x) | None => inl tt end)) ->
  @for_while_program 5 Ty.Unit Word16 Word16 _ (legacy_fold_body distance op) (tt, a) environment =
    Some (inl (fold_left (fun acc x => legacy_word_step distance acc (enc x)) xs a)).
Proof.
  intros Hlen Hop. rewrite for_while_program_reader_sem.
  transitivity (for_while_run 5 (legacy_reader_step distance (fun w => op w environment)) tt a).
  - apply for_while_run_ext. intro p. apply legacy_fold_body_reader.
  - apply (@for_while_run_fold_list X Word16 5 xs
      (fun acc x => legacy_word_step distance acc (enc x)) a); [exact Hlen|].
    intros w acc. unfold legacy_reader_step. cbn [fst snd]. rewrite Hop.
    destruct (nth_error xs (Z.to_nat (wz 5 w))); reflexivity.
Qed.

Lemma legacy_fold_program_parametric distance {alg1 alg2 : Core.Algebra}
    (R : Core.Parametric.Rel alg1 alg2)
    (v1 : alg1 Ty.Unit Word32) (v2 : alg2 Ty.Unit Word32)
    (op1 : alg1 Word32 (Ty.Unit + Word32)) (op2 : alg2 Word32 (Ty.Unit + Word32)) :
  R _ _ v1 v2 -> R _ _ op1 op2 ->
  R _ _ (legacy_fold_program distance v1 op1) (legacy_fold_program distance v2 op2).
Proof.
  intros HV HO. unfold legacy_fold_program, legacy_version_check, legacy_fold_finish.
  apply comp_Parametric.
  - apply pair_Parametric.
    + apply comp_Parametric; [auto with parametricity|apply le_word_spec_parametric].
    + apply zero_Parametric.
  - apply case_Parametric; [auto with parametricity|].
    apply comp_Parametric; [|auto with parametricity].
    apply for_while_program_parametric. unfold legacy_fold_body.
    apply comp_Parametric; [auto with parametricity|].
    apply case_Parametric; [auto with parametricity|].
    apply injr_Parametric. apply comp_Parametric;
      [apply pair_Parametric; [apply take_Parametric, parse_sequence_spec_parametric|auto with parametricity]
      |apply legacy_parse_tail_parametric].
Qed.

Definition legacy_sequence_value (distance : bool) (s : Z) : Z :=
  if Z.testbit s 31 then 0
  else if (if distance then negb (Z.testbit s 22) else Z.testbit s 22)
       then s mod 65536 else 0.

Definition legacy_cache_value (distance : bool) (xs : list sigTxInput) : Z :=
  fold_left (fun a x => Z.max a (legacy_sequence_value distance (Int.unsigned (sigTxiSequence x)))) xs 0.

Lemma legacy_sequence_value_range distance s : 0 <= legacy_sequence_value distance s < 65536.
Proof.
  unfold legacy_sequence_value. destruct (Z.testbit s 31); [lia|].
  destruct (if distance then negb (Z.testbit s 22) else Z.testbit s 22);
    [apply Z.mod_pos_bound; lia|lia].
Qed.

Lemma legacy_max_word_value (a b : tySem Word16) :
  wz 4 (@minmax_word_spec 4 Datatypes.true CoreFunSem (a, b)) = Z.max (wz 4 a) (wz 4 b).
Proof.
  rewrite minmax_word_spec_strict. unfold minmax_select, wz.
  destruct (@toZ (WordToZ 4) a <? @toZ (WordToZ 4) b) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. symmetry. apply Z.max_r. lia.
  - apply Z.ltb_ge in Hlt. symmetry. apply Z.max_l. lia.
Qed.

Lemma legacy_parse_tail_value distance (p : tySem (Ty.Unit + (Word16 + Word16))) a :
  @legacy_parse_tail distance CoreFunSem (p, a) =
  match p with
  | inl _ => a
  | inr (inl x) => if distance then @minmax_word_spec 4 Datatypes.true CoreFunSem (x, a) else a
  | inr (inr x) => if distance then a else @minmax_word_spec 4 Datatypes.true CoreFunSem (x, a)
  end.
Proof. destruct p as [u | [x | x]]; destruct distance; reflexivity. Qed.

Lemma legacy_word_step_value distance a x :
  wz 4 (legacy_word_step distance a x) = Z.max (wz 4 a) (legacy_sequence_value distance (wz 5 x)).
Proof.
  unfold legacy_word_step. rewrite legacy_parse_tail_value, parse_sequence_spec_numeric.
  unfold legacy_sequence_value, wz. pose proof (word_toZ_range 4 a) as HA.
  assert (HM : @toZ (WordToZ 4) (@fromZ (WordToZ 4) (@toZ (WordToZ 5) x)) =
    @toZ (WordToZ 5) x mod 65536).
  { rewrite to_fromZ, two_power_nat_equiv, word_bitSize. reflexivity. }
  destruct (Z.testbit (@toZ (WordToZ 5) x) 31);
    destruct (Z.testbit (@toZ (WordToZ 5) x) 22); destruct distance;
    cbn [negb].
  all: try solve [rewrite Z.max_l by lia; reflexivity].
  all: rewrite minmax_word_spec_strict; unfold minmax_select; rewrite HM.
  all: destruct (@toZ (WordToZ 5) x mod 65536 <? @toZ (WordToZ 4) a) eqn:Hlt.
  all: first [apply Z.ltb_lt in Hlt; symmetry; apply Z.max_l; lia
    |rewrite HM; apply Z.ltb_ge in Hlt; symmetry; apply Z.max_r; lia].
Qed.

Lemma legacy_fold_value distance xs a :
  wz 4 (fold_left (fun acc x => legacy_word_step distance acc
    (@fromZ (WordToZ 5) (Int.unsigned (sigTxiSequence x)))) xs a) =
  fold_left (fun acc x => Z.max acc
    (legacy_sequence_value distance (Int.unsigned (sigTxiSequence x)))) xs (wz 4 a).
Proof.
  revert a. induction xs as [|x xs IH]; intro a; [reflexivity|].
  cbn [fold_left]. rewrite IH, legacy_word_step_value. unfold wz.
  rewrite to_fromZ, two_power_nat_equiv, word_bitSize.
  rewrite Z.mod_small by exact (Int.unsigned_range (sigTxiSequence x)). reflexivity.
Qed.

Lemma legacy_cache_value_range distance xs : 0 <= legacy_cache_value distance xs < 65536.
Proof.
  assert (Hbound : forall ys a, 0 <= a < 65536 ->
    0 <= fold_left (fun acc x => Z.max acc
      (legacy_sequence_value distance (Int.unsigned (sigTxiSequence x)))) ys a < 65536).
  { induction ys as [|x ys IH]; intros a HA; [exact HA|].
    cbn [fold_left]. apply IH.
    pose proof (legacy_sequence_value_range distance (Int.unsigned (sigTxiSequence x))). lia. }
  unfold legacy_cache_value. apply Hbound. lia.
Qed.

Local Opaque haskell_to_word le_word_spec Alg.scribe.

Lemma elements_legacy_version_check_value (environment : Elements.env) :
  exists b, legacy_version_check
    (@Primitive.Combinators.prim Ty.Unit Word32 (PrimitivePrimSem option_Monad_Zero) Elements.Version)
    tt environment = Some b /\
    Bit.toBool b = (2 <=? Int.unsigned (sigTxVersion (Elements.envTx environment))).
Proof.
  set (v := @fromZ (WordToZ 5) (Int.unsigned (sigTxVersion (Elements.envTx environment)))).
  exists (@le_word_spec CoreFunSem 5 (haskell_to_word 5 2, v)). split.
  - assert (HV : @Primitive.Combinators.prim Ty.Unit Word32 (PrimitivePrimSem option_Monad_Zero)
      Elements.Version tt environment = Some v) by reflexivity.
    pose proof (@core_reader_sem _ _ (fun alg => @Alg.scribe Ty.Unit Word32 (haskell_to_word 5 2) alg)
      ltac:(intros alg1 alg2 R; apply scribe_Parametric) Elements.env tt environment) as HS.
    rewrite scribe_correct in HS.
    pose proof (@core_reader_sem _ _ (fun alg => @le_word_spec alg 5) (le_word_spec_parametric 5)
      Elements.env (haskell_to_word 5 2, v) environment) as HL.
    unfold legacy_version_check.
    change (@elements_comp (PrimitivePrimSem option_Monad_Zero) Ty.Unit (Word32 * Word32) Bit
      (@elements_pair (PrimitivePrimSem option_Monad_Zero) Ty.Unit Word32 Word32
        (@Alg.scribe Ty.Unit Word32 (haskell_to_word 5 2) (CoreSem (ReaderT_CIMonad Elements.env option_CIMonad)))
        (Primitive.Combinators.prim Elements.Version))
        (@le_word_spec (CoreSem (ReaderT_CIMonad Elements.env option_CIMonad)) 5) tt environment =
      Some (@le_word_spec CoreFunSem 5 (haskell_to_word 5 2, v))).
    rewrite elements_comp_sem, elements_pair_sem, HS, HV. exact HL.
  - rewrite le_word_spec_numeric. unfold v. rewrite haskell_to_word_matches.
    rewrite !to_fromZ, !two_power_nat_equiv, !word_bitSize.
    change (2 mod 4294967296 <=? Int.unsigned (sigTxVersion (Elements.envTx environment)) mod 4294967296 =
      (2 <=? Int.unsigned (sigTxVersion (Elements.envTx environment)))).
    rewrite Z.mod_small by lia.
    rewrite Z.mod_small by exact (Int.unsigned_range (sigTxVersion (Elements.envTx environment))). reflexivity.
Qed.

Local Opaque for_while_program legacy_fold_body.

Lemma legacy_fold_finish_reader distance
    (op : CoreSem (ReaderT_CIMonad Elements.env option_CIMonad) Word32 (Ty.Unit + Word32))
    a result b environment :
  @for_while_program 5 Ty.Unit Word16 Word16 _ (legacy_fold_body distance op) (tt, a) environment =
    Some (inl result) ->
  legacy_fold_finish distance op (b, a) environment = Some (if Bit.toBool b then result else a).
Proof.
  intro HF. destruct b as [u | u]; destruct u.
  - reflexivity.
  - change (@elements_comp (PrimitivePrimSem option_Monad_Zero) (Ty.Unit * Word16)
      (Word16 + Word16) Word16
      (@for_while_program 5 Ty.Unit Word16 Word16
        (CoreSem (ReaderT_CIMonad Elements.env option_CIMonad)) (legacy_fold_body distance op))
      (@copair Word16 Word16 Word16 (CoreSem (ReaderT_CIMonad Elements.env option_CIMonad)) iden iden)
      (tt, a) environment = Some result).
    rewrite elements_comp_sem, HF. reflexivity.
Qed.

Lemma elements_legacy_lock_spec_value distance (environment : Elements.env) :
  @elements_legacy_lock_spec distance (PrimitivePrimSem option_Monad_Zero) tt environment =
  Some (@fromZ (WordToZ 4)
    (if 2 <=? Int.unsigned (sigTxVersion (Elements.envTx environment))
     then legacy_cache_value distance (sigTxIn (Elements.envTx environment)) else 0)).
Proof.
  destruct (elements_legacy_version_check_value environment) as (b & HB & HBool).
  set (op := @Primitive.Combinators.prim Word32 (Ty.Unit + Word32)
    (PrimitivePrimSem option_Monad_Zero) Elements.InputSequence).
  set (acc := @Word.zero 4 CoreFunSem tt).
  set (result := fold_left (fun a x => legacy_word_step distance a
    (@fromZ (WordToZ 5) (Int.unsigned (sigTxiSequence x)))) (sigTxIn (Elements.envTx environment)) acc).
  assert (HF : @for_while_program 5 Ty.Unit Word16 Word16 _ (legacy_fold_body distance op)
    (tt, acc) environment = Some (inl result)).
  { apply legacy_fold_reader_list.
    - pose proof (sigTxInBounds (Elements.envTx environment)) as HBound.
      rewrite Zlength_correct in HBound. exact (proj2 HBound).
    - intro w. exact (final_list_op (sigTxIn (Elements.envTx environment)) w). }
  assert (HZ : @Word.zero 4 (CoreSem (ReaderT_CIMonad Elements.env option_CIMonad)) tt environment = Some acc).
  { apply (@core_reader_sem _ _ (fun alg => @Word.zero 4 alg)
      ltac:(intros alg1 alg2 R; apply zero_Parametric)). }
  assert (Hres : result = @fromZ (WordToZ 4) (legacy_cache_value distance (sigTxIn (Elements.envTx environment)))).
  { rewrite <- (from_toZ result) at 1. fold (wz 4 result).
    unfold result. rewrite legacy_fold_value. change (wz 4 acc) with 0. reflexivity. }
  unfold elements_legacy_lock_spec, legacy_fold_program. fold op.
  change (@elements_comp (PrimitivePrimSem option_Monad_Zero) Ty.Unit (Bit * Word16) Word16
    (@elements_pair (PrimitivePrimSem option_Monad_Zero) Ty.Unit Bit Word16
      (@legacy_version_check (CoreSem (ReaderT_CIMonad Elements.env option_CIMonad))
        (@Primitive.Combinators.prim Ty.Unit Word32 (PrimitivePrimSem option_Monad_Zero) Elements.Version))
      (@Word.zero 4 (CoreSem (ReaderT_CIMonad Elements.env option_CIMonad))))
    (@legacy_fold_finish distance (CoreSem (ReaderT_CIMonad Elements.env option_CIMonad)) op)
    tt environment = Some (@fromZ (WordToZ 4)
      (if 2 <=? Int.unsigned (sigTxVersion (Elements.envTx environment))
       then legacy_cache_value distance (sigTxIn (Elements.envTx environment)) else 0))).
  change (@legacy_version_check (CoreSem (ReaderT_CIMonad Elements.env option_CIMonad))
    (@Primitive.Combinators.prim Ty.Unit Word32 (PrimitivePrimSem option_Monad_Zero) Elements.Version)
    tt environment = Some b) in HB.
  rewrite elements_comp_sem, elements_pair_sem, HB, HZ.
  rewrite legacy_fold_finish_reader with (result := result) by exact HF.
  rewrite HBool, Hres. unfold acc. rewrite zero_fw4.
  destruct (2 <=? Int.unsigned (sigTxVersion (Elements.envTx environment))); reflexivity.
Qed.

