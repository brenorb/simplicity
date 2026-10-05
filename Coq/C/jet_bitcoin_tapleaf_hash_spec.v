(** Literal port of Bitcoin.Programs.SigHash.tapleafHash
      tapleafHash = ((ctx8InitTag "TapLeaf")
                &&& (primitive TapleafVersion &&& scribe (toWord8 32)) >>> ctx8Addn vector2)
                &&& (primitive ScriptCMR) >>> ctx8Addn vector32 >>> ctx8Finalize
    and its value: the tagged hash of the leaf version, the byte 32 and the
    script CMR.  No C execution here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Digest.
Require Simplicity.Alg Simplicity.SHA256.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_spec C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha256_iv_init C.jet_read8s_layout C.jet_word32_chunks.
Require Import C.jet_sha_ctx8_spec C.jet_sha_ctx8_model C.jet_sha_finalize_exec C.jet_sha_finalize_spec.
Require Import C.jet_sha_tapdata_spec C.jet_sha_hash_closed.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

(** ** ctx8InitTag *)
Definition ctx8_init_tag_spec (prefix : Ty.tySem (Word 8)) {term : Alg.Core.Algebra} :
    @Alg.Core.domain term Ty.Unit sha256_ctx8_type :=
  AC.pair (buffer_empty_spec (Word 3) 5 Ty.Unit) (AC.pair one64_spec (Alg.scribe prefix)).

Lemma ctx8_init_tag_spec_parametric prefix : Alg.Core.Parametric (@ctx8_init_tag_spec prefix).
Proof.
  intros alg1 alg2 R. unfold ctx8_init_tag_spec, one64_spec.
  apply Alg.pair_Parametric; [apply buffer_empty_spec_parametric|].
  apply Alg.pair_Parametric; [|apply Alg.scribe_Parametric].
  apply Alg.comp_Parametric; [apply Bit.true_Parametric|apply left_pad_low_1_n_parametric].
Qed.

Lemma ctx8_init_tag_spec_value prefix :
  @ctx8_init_tag_spec prefix Alg.CoreFunSem tt = (buffer_empty_value (Word 3) 5, (one64, prefix)).
Proof.
  unfold ctx8_init_tag_spec.
  change (@AC.pair _ _ _ Alg.CoreFunSem (buffer_empty_spec (Word 3) 5 Ty.Unit)
      (AC.pair one64_spec (Alg.scribe prefix)) tt) with
    (@buffer_empty_spec (Word 3) 5 Ty.Unit Alg.CoreFunSem tt,
     (one64, @Alg.scribe Ty.Unit (Word 8) prefix Alg.CoreFunSem tt)).
  rewrite buffer_empty_spec_value, Alg.scribe_correct. reflexivity.
Qed.

(** Hashing a non-empty byte list from a tagged initial context. *)
Lemma tagged_hash_closed prefix (bs : list (Ty.tySem (Word 3))) :
  bs <> [] -> 1 + Z.of_nat (length bs) / 64 < ctx8_limit ->
  match ctx8_add_list (buffer_empty_value (Word 3) 5, (one64, prefix)) bs with
  | Some c' => @ctx8_finalize_spec optalg c'
  | None => None
  end = Some (from_hash256 (mk_hash256 (sha_stream [] (state_regs prefix) 1 bs))).
Proof.
  intros Hne HT.
  pose proof (ctx8_hash_closed bs (buffer_empty_value (Word 3) 5) one64 prefix Hne) as HC.
  cbv zeta in HC. rewrite buffer_list_empty, one64_value in HC. apply HC. exact HT.
Qed.

(** ** The "TapLeaf" tag *)
Definition tapleaf_prefix : Ty.tySem (Word 8) :=
  @fromZ (WordToZ 8) 70958157933520607839019537422246167060091032002336751475331932121621309354185.
Definition tapleaf_tag_word : Ty.tySem (Word 8) :=
  @fromZ (WordToZ 8) 79116870754516498155377025264173316429806398436674791508357063697857940875758.
Definition tapleaf_tag_block : Ty.tySem (Word 9) :=
  @fromZ (WordToZ 9) 4419371652836376455474968878630918397760145670010128363765783181683530450169627206189720363646590656808003891873351972755786637110606967735627562008707128.
Definition tapleaf_tag_bytes : list int := map Int.repr [84; 97; 112; 76; 101; 97; 102].

Lemma tapleaf_tag_hash_eval :
  @Simplicity.SHA256.hashBlock Alg.CoreFunSem (iv_word, tapleaf_tag_block) = tapleaf_tag_word.
Proof. vm_compute. reflexivity. Qed.

Lemma tapleaf_prefix_eval :
  @Simplicity.SHA256.hashBlock Alg.CoreFunSem (iv_word, (tapleaf_tag_word, tapleaf_tag_word)) = tapleaf_prefix.
Proof. vm_compute. reflexivity. Qed.

Lemma tapleaf_tag_block_bytes :
  map Int.unsigned (map word8_array_value (vector_values (Word 3) 6 tapleaf_tag_block)) =
  map Int.unsigned (tapleaf_tag_bytes ++ sha_pad (Int64.repr 7)).
Proof. vm_compute. reflexivity. Qed.

(** ** The program *)
Definition byte32 : Ty.tySem (Word 3) := @fromZ (WordToZ 3) 32.

Definition tapleaf_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
       (@AC.comp _ _ _ core
          (@AC.pair _ _ _ core (@ctx8_init_tag_spec tapleaf_prefix core)
             (@AC.pair _ _ _ core
                (@PF.Combinators.prim _ _ alg (BitcoinFull.Ext BitcoinExt.TapleafVersion))
                (@Alg.scribe Ty.Unit (Word 3) byte32 core)))
          (@ctx8_addn_spec 1 term))
       (@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.ScriptCMR)))
    (@AC.comp _ _ _ core (@ctx8_addn_spec 5 term) (@ctx8_finalize_spec term)).

Definition tapleaf_bytes (e : ext_environment) : list (Ty.tySem (Word 3)) :=
  [@fromZ (WordToZ 3) (extTapleafVersion e); byte32] ++
  vector_values (Word 3) 5 (from_hash256 (Bitcoin.envScriptCMR (extBase e))).

Definition tapleaf_hash_of (e : ext_environment) : hash256 :=
  mk_hash256 (sha_stream [] (state_regs tapleaf_prefix) 1 (tapleaf_bytes e)).

Theorem tapleaf_hash_spec_sem (e : ext_environment) :
  @tapleaf_hash_spec fullalg tt e = Some (from_hash256 (tapleaf_hash_of e)).
Proof.
  unfold tapleaf_hash_spec. cbv zeta.
  rewrite fx_comp, fx_pair, fx_comp, fx_pair, fx_pair.
  rewrite (fx_core (fun alg => @ctx8_init_tag_spec tapleaf_prefix alg)
    (ctx8_init_tag_spec_parametric tapleaf_prefix)), ctx8_init_tag_spec_value.
  rewrite !fx_prim.
  change (BitcoinFull.sem (BitcoinFull.Ext BitcoinExt.TapleafVersion) tt e) with
    (Some (@fromZ (WordToZ 3) (extTapleafVersion e))).
  change (BitcoinFull.sem (BitcoinFull.Base Bitcoin.ScriptCMR) tt e) with
    (Some (from_hash256 (Bitcoin.envScriptCMR (extBase e)))).
  rewrite (fx_core (fun alg => @Alg.scribe Ty.Unit (Word 3) byte32 alg)
    (fun a1 a2 R => @Alg.scribe_Parametric a1 a2 R Ty.Unit (Word 3) byte32)), Alg.scribe_correct.
  cbv beta iota.
  rewrite (fx_assert (fun alg => @ctx8_addn_spec 1 alg) (ctx8_addn_spec_parametric 1)), (ctx8_addn_option 1).
  assert (HB : tapleaf_bytes e <> []) by discriminate.
  assert (HT : 1 + Z.of_nat (length (tapleaf_bytes e)) / 64 < ctx8_limit).
  { unfold tapleaf_bytes. rewrite app_length, vector_values_length. reflexivity. }
  unfold tapleaf_hash_of. rewrite <- (tagged_hash_closed tapleaf_prefix (tapleaf_bytes e) HB HT).
  unfold tapleaf_bytes. rewrite ctx8_add_list_app.
  match goal with |- match match ?X with _ => _ end with _ => _ end = _ =>
    destruct X as [c1|] eqn:H1 end;
  match goal with |- _ = match match ?Y with _ => _ end with _ => _ end =>
    match type of H1 with _ = ?r => assert (H2 : Y = r) by exact H1; rewrite H2 end end;
  [|reflexivity].
  rewrite fx_comp.
  rewrite (fx_assert (fun alg => @ctx8_addn_spec 5 alg) (ctx8_addn_spec_parametric 5)), (ctx8_addn_option 5).
  match goal with |- match ?X with _ => _ end = _ => destruct X as [c2|] eqn:H3 end;
  try (match goal with |- _ = match ?Y with _ => _ end =>
    match type of H3 with _ = ?r => assert (H4 : Y = r) by exact H3; rewrite H4 end end);
  [|reflexivity].
  apply (fx_assert (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric).
Qed.
