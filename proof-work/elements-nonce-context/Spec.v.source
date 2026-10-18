(** Literal nonceHash program, to be connected to simplicity_nonce_hash.
    This module is a specification/byte-stream bridge, not a jet theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.Util.Option.
Require Simplicity.Alg.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha_ctx8_spec.
Require Import C.jet_encoding C.jet_read8s_layout.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Local Ltac nonce_opt_steps :=
  repeat progress (cbv beta iota; cbn [fst snd];
    rewrite ?opt_pair, ?opt_comp, ?opt_take, ?opt_drop, ?opt_iden, ?opt_case).

Definition nonce_conf_type := Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) Word256.
Definition nonce_value_type := Ty.Sum Ty.Unit nonce_conf_type.
Definition nonce_hash_input_type := Ty.Prod sha256_ctx8_type nonce_value_type.
Definition nonce_byte (z : Z) : Ty.tySem Word8 := @fromZ (WordToZ 3) z.

Definition nonce_prefix_spec {core : Alg.Core.Algebra} :
    @Alg.Core.domain core nonce_conf_type (Ty.Prod Word8 Word256) :=
  AC.copair
    (AC.pair (AC.take (AC.copair (Alg.scribe (nonce_byte 2)) (Alg.scribe (nonce_byte 3))))
             (AC.drop AC.iden))
    (AC.pair (AC.comp AC.unit (Alg.scribe (nonce_byte 1))) AC.iden).

Definition nonce_hash_spec {term : Alg.Assertion.Algebra} :
    @Alg.Assertion.domain term nonce_hash_input_type sha256_ctx8_type :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core (@AC.pair _ _ _ core (AC.drop AC.iden) (AC.take AC.iden))
    (@AC.case _ _ _ _ core
      (@AC.comp _ _ _ core (@AC.pair _ _ _ core (AC.drop AC.iden) (AC.take (@Word.zero 3 core))) (@ctx8_add1_spec term))
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (AC.drop AC.iden) (AC.take (@nonce_prefix_spec core)))
        (@AC.comp _ _ _ core
          (@AC.pair _ _ _ core
            (@AC.comp _ _ _ core (@AC.pair _ _ _ core (AC.take AC.iden) (AC.drop (AC.take AC.iden))) (@ctx8_add1_spec term))
            (@AC.drop _ _ _ core (AC.drop AC.iden)))
          (@ctx8_addn_spec 5 term)))).

Lemma nonce_prefix_spec_parametric : Alg.Core.Parametric (@nonce_prefix_spec).
Proof.
  intros a1 a2 R. unfold nonce_prefix_spec.
  solve [repeat first [apply Alg.scribe_Parametric | apply Alg.copair_Parametric | apply Alg.pair_Parametric |
    apply Alg.take_Parametric | apply Alg.drop_Parametric | apply Alg.comp_Parametric |
    apply Alg.unit_Parametric | apply Alg.iden_Parametric]].
Qed.

Lemma nonce_hash_spec_parametric : Alg.Assertion.Parametric (@nonce_hash_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (ctx8_add1_spec_parametric alg1 alg2 R) as H1.
  pose proof (ctx8_addn_spec_parametric 5 alg1 alg2 R) as H32.
  destruct R as [R [HC HA]]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold nonce_hash_spec.
  solve [repeat first [exact H1 | exact H32 | apply (nonce_prefix_spec_parametric _ _ RC) | apply (Word.zero_Parametric RC) |
    apply (Alg.comp_Parametric RC) | apply (Alg.pair_Parametric RC) | apply (Alg.case_Parametric RC) |
    apply (Alg.take_Parametric RC) | apply (Alg.drop_Parametric RC) | apply (Alg.iden_Parametric RC)]].
Qed.

Definition nonce_prefix_value (p : Ty.tySem nonce_conf_type) : Ty.tySem Word8 * Ty.tySem Word256 :=
  match p with
  | inl (odd, h) => ((match odd with inl _ => nonce_byte 2 | inr _ => nonce_byte 3 end), h)
  | inr h => (nonce_byte 1, h)
  end.

Lemma nonce_prefix_core p : @nonce_prefix_spec Alg.CoreFunSem p = nonce_prefix_value p.
Proof.
  destruct p as [[[[]|[]] h]|h]; reflexivity.
Qed.

Definition nonce_hash_bytes (a : Ty.tySem nonce_value_type) : list (Ty.tySem Word8) :=
  match a with
  | inl _ => [nonce_byte 0]
  | inr p => fst (nonce_prefix_value p) :: vector_values (Word 3) 5 (snd (nonce_prefix_value p))
  end.

Lemma nonce_hash_option (c : Ty.tySem sha256_ctx8_type) (a : Ty.tySem nonce_value_type) :
  @nonce_hash_spec optalg (c, a) = ctx8_add_list c (nonce_hash_bytes a).
Proof.
  assert (HZ : forall u, @Word.zero 3 (Alg.Assertion.toCore optalg) u = Some (nonce_byte 0)).
  { intros []. rewrite (opt_core (fun alg => @Word.zero 3 alg)
      (fun a1 a2 R => @Word.zero_Parametric 3 a1 a2 R) tt).
    reflexivity. }
  assert (HP : forall p, @nonce_prefix_spec (Alg.Assertion.toCore optalg) p = Some (nonce_prefix_value p)).
  { intro p. rewrite (opt_core (fun alg => @nonce_prefix_spec alg) nonce_prefix_spec_parametric p).
    rewrite nonce_prefix_core. reflexivity. }
  unfold nonce_hash_spec. destruct a as [[]|p]; nonce_opt_steps.
  - rewrite HZ. cbv beta iota. rewrite ctx8_add1_option.
    cbn [nonce_hash_bytes ctx8_add_list]. destruct (ctx8_add1_model c (nonce_byte 0)); reflexivity.
  - rewrite HP. cbv beta iota.
    destruct (nonce_prefix_value p) as [prefix body] eqn:EP.
    nonce_opt_steps. rewrite ctx8_add1_option.
    unfold nonce_hash_bytes. rewrite EP. cbn [fst snd].
    change (ctx8_add_list c (prefix :: vector_values (Word 3) 5 body)) with
      (match ctx8_add1_model c prefix with
       | Some c' => ctx8_add_list c' (vector_values (Word 3) 5 body) | None => None end).
    destruct (ctx8_add1_model c prefix) as [c'|]; [apply (ctx8_addn_option 5)|reflexivity].
Qed.

Lemma nonce_hash_bytes_length a :
  length (nonce_hash_bytes a) = match a with inl _ => 1%nat | inr _ => 33%nat end.
Proof.
  destruct a as [u|p]; cbn [nonce_hash_bytes length]; [reflexivity|].
  rewrite vector_values_length. reflexivity.
Qed.

Lemma nonce_hash_input_bits : bitSize nonce_hash_input_type = 1089%nat.
Proof. reflexivity. Qed.

Lemma nonce_none_encoding :
  @encode nonce_value_type (inl tt) = Some false :: repeat None 258.
Proof. reflexivity. Qed.
Lemma nonce_explicit_encoding (h : Ty.tySem Word256) :
  @encode nonce_value_type (inr (inr h)) = [Some true; Some true; None] ++ encode h.
Proof. reflexivity. Qed.
Lemma nonce_confidential_encoding (odd : bool) (h : Ty.tySem Word256) :
  @encode nonce_value_type (inr (inl ((if odd then inr tt else inl tt), h))) =
    [Some true; Some false; Some odd] ++ encode h.
Proof. destruct odd; reflexivity. Qed.

Lemma nonce_prefix_ints :
  word8_array_value (nonce_byte 0) = Int.zero /\
  word8_array_value (nonce_byte 1) = Int.one /\
  word8_array_value (nonce_byte 2) = Int.repr 2 /\
  word8_array_value (nonce_byte 3) = Int.repr 3.
Proof. vm_compute; repeat split; reflexivity. Qed.

Lemma nonce_none_stream : map word8_array_value (nonce_hash_bytes (inl tt)) = [Int.zero].
Proof. change ([word8_array_value (nonce_byte 0)] = [Int.zero]). rewrite (proj1 nonce_prefix_ints). reflexivity. Qed.
Lemma nonce_explicit_stream (h : Ty.tySem Word256) :
  map word8_array_value (nonce_hash_bytes (inr (inr h))) =
    Int.one :: map word8_array_value (vector_values (Word 3) 5 h).
Proof.
  change (word8_array_value (nonce_byte 1) :: map word8_array_value (vector_values (Word 3) 5 h) =
    Int.one :: map word8_array_value (vector_values (Word 3) 5 h)).
  rewrite (proj1 (proj2 nonce_prefix_ints)). reflexivity.
Qed.
Lemma nonce_confidential_stream (odd : bool) (h : Ty.tySem Word256) :
  map word8_array_value (nonce_hash_bytes (inr (inl ((if odd then inr tt else inl tt), h)))) =
    Int.repr (if odd then 3 else 2) :: map word8_array_value (vector_values (Word 3) 5 h).
Proof.
  destruct odd.
  - change (word8_array_value (nonce_byte 3) :: map word8_array_value (vector_values (Word 3) 5 h) =
      Int.repr 3 :: map word8_array_value (vector_values (Word 3) 5 h)).
    rewrite (proj2 (proj2 (proj2 nonce_prefix_ints))). reflexivity.
  - change (word8_array_value (nonce_byte 2) :: map word8_array_value (vector_values (Word 3) 5 h) =
      Int.repr 2 :: map word8_array_value (vector_values (Word 3) 5 h)).
    rewrite (proj1 (proj2 (proj2 nonce_prefix_ints))). reflexivity.
Qed.
