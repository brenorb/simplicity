(** Buildability and locality of the Elements element relations: each can be
    established by stores at any suitably aligned writable place and depends
    only on the loads inside its extent. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values.
Require Import Simplicity.Digest.
Require Import C.jet_uint32_array_init C.jet_env_constructible C.jet_elements_prim.
Require Import C.jet_elements_hash_elem C.jet_elements_indexed_ptr_jets.
Require Import C.jet_elements_asset_jets C.jet_elements_amount_jets.
Require Import C.jet_elements_issuance_jets C.jet_elements_issuance_amount_jets.
Require Import C.jet_elements_current_gen_jets.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Ltac divides := apply Z.mod_divide; [discriminate|reflexivity].

Lemma hash_words_len (h : hash256) : length (hash256_reg h) = 8%nat.
Proof. exact (hash256_len h). Qed.

(** ** Outpoint *)
Lemma outpoint_rep_buildable : elem_buildable 8 outpoint_rep 40.
Proof.
  eapply elem_buildable_impl;
    [|apply (elem_buildable_pair 8
        (fun m b ofs (x : sigTxInput) => uint32_array_at m b ofs (outpoint_words x))
        (fun m b ofs (x : sigTxInput) =>
          Mem.load Mint64 m b ofs = Some (Vlong (outpoint_ix (sigTxiPreviousOutpoint x))))
        0 32 32 8 40); try lia; try divides].
  - intros m b ofs x [H1 H2]. rewrite Z.add_0_r in H1. split; assumption.
  - apply words_local. intro x. apply hash_words_len.
  - eapply elem_buildable_align; [|apply words_buildable; intro x; apply hash_words_len]. divides.
  - apply int64_buildable.
Qed.

Lemma outpoint_rep_local : elem_local outpoint_rep 40.
Proof.
  intros m1 m2 b ofs x [Hr Hix] Hl. split.
  - eapply (words_local outpoint_words); [intro; apply hash_words_len|exact Hr|].
    intros c o v H1 H2. apply Hl; lia.
  - apply (Hl Mint64 (ofs + 32) _); [lia|change (size_chunk Mint64) with 8; lia|exact Hix].
Qed.

(** ** Confidential asset and optional nonce *)
Lemma asset_rep_buildable {X : Type} (g : X -> assetWith unit) :
  elem_buildable 4 (fun m b ofs x => asset_rep m b ofs (g x)) 36.
Proof.
  eapply elem_buildable_impl;
    [|apply (elem_buildable_pair 4
        (fun m b ofs (x : X) => uint32_array_at m b ofs (asset_words (g x)))
        (fun m b ofs (x : X) => Mem.load Mint32 m b ofs = Some (Vint (conf_prefix (g x))))
        0 32 32 4 36); try lia; try divides].
  - intros m b ofs x [H1 H2]. rewrite Z.add_0_r in H1. split; assumption.
  - apply words_local. intro x. apply asset_words_length.
  - apply words_buildable. intro x. apply asset_words_length.
  - apply int32_buildable.
Qed.

Lemma asset_rep_local {X : Type} (g : X -> assetWith unit) :
  elem_local (fun m b ofs x => asset_rep m b ofs (g x)) 36.
Proof. intros m1 m2 b ofs x Hr Hl. exact (asset_rep_mono m1 m2 b ofs (g x) Hr Hl). Qed.

Lemma nonce_rep_buildable {X : Type} (g : X -> option nonce) :
  elem_buildable 4 (fun m b ofs x => nonce_rep m b ofs (g x)) 36.
Proof.
  eapply elem_buildable_impl;
    [|apply (elem_buildable_pair 4
        (fun m b ofs (x : X) => uint32_array_at m b ofs (nonce_words (g x)))
        (fun m b ofs (x : X) => Mem.load Mint32 m b ofs = Some (Vint (nonce_prefix (g x))))
        0 32 32 4 36); try lia; try divides].
  - intros m b ofs x [H1 H2]. rewrite Z.add_0_r in H1. split; [intros _; exact H1|exact H2].
  - apply words_local. intro x. apply nonce_words_length.
  - apply words_buildable. intro x. apply nonce_words_length.
  - apply int32_buildable.
Qed.

Lemma nonce_rep_local {X : Type} (g : X -> option nonce) :
  elem_local (fun m b ofs x => nonce_rep m b ofs (g x)) 36.
Proof.
  intros m1 m2 b ofs x [Hr Hp] Hl. split.
  - intros Hn. eapply (words_local (fun n => nonce_words n)); [intro; apply nonce_words_length|exact (Hr Hn)|].
    intros c o v H1 H2. apply Hl; lia.
  - apply (Hl Mint32 (ofs + 32) _); [lia|change (size_chunk Mint32) with 4; lia|exact Hp].
Qed.

(** ** Confidential amount *)
Lemma amount_rep_buildable {X : Type} (g : X -> amountWith unit) :
  elem_buildable 8 (fun m b ofs x => amount_rep m b ofs (g x)) 40.
Proof.
  intros x m b ofs HP HA. unfold amount_rep.
  assert (HA4 : (4 | ofs)) by (eapply Z.divide_trans; [|exact HA]; divides).
  destruct (built_store_int32 m b (ofs + 32) (conf_prefix (g x)) (ofs + 32) (ofs + 36))
    as (m1 & B1 & L1);
    [intros o Ho; apply HP; lia|apply Z.divide_add_r; [exact HA4|divides]|lia|lia|].
  assert (HD : exists m2, built m1 m2 b ofs (ofs + 32) /\
    match g x with
    | Explicit v => Mem.load Mint64 m2 b ofs = Some (Vlong v)
    | Confidential (Point _ h) _ => uint32_array_at m2 b ofs (hash256_reg h)
    end).
  { destruct (g x) as [v|[odd h] p].
    - destruct (built_store_int64 m1 b ofs v ofs (ofs + 32)) as (m2 & B2 & L2);
        [eapply built_range_perm; [exact B1|]; intros o Ho; apply HP; lia|exact HA|lia|lia|].
      exists m2. split; assumption.
    - destruct (built_uint32_array (hash256_reg h) m1 b ofs) as (m2 & B2 & L2).
      { rewrite hash_words_len. eapply built_range_perm; [exact B1|]. intros o Ho. apply HP. lia. }
      { exact HA4. }
      rewrite hash_words_len in B2. exists m2. split; assumption. }
  destruct HD as (m2 & B2 & HD).
  exists m2. split; [|split; [exact HD|]].
  - eapply built_trans; (eapply built_weaken; [| |eassumption]; lia).
  - eapply built_load_some; [exact B2| |exact L1]. right; right. lia.
Qed.

Lemma amount_rep_local {X : Type} (g : X -> amountWith unit) :
  elem_local (fun m b ofs x => amount_rep m b ofs (g x)) 40.
Proof. intros m1 m2 b ofs x Hr Hl. exact (amount_rep_mono m1 m2 b ofs (g x) Hr Hl). Qed.

(** ** Asset followed by amount in one record *)
Lemma asset_amount_buildable {X : Type} (ga : X -> assetWith unit) (gm : X -> amountWith unit) pa pm sz :
  0 <= pa -> (8 | pa) -> pa + 36 <= pm -> (8 | pm) -> pm + 40 <= sz ->
  elem_buildable 8 (fun m b ofs x => asset_rep m b (ofs + pa) (ga x) /\ amount_rep m b (ofs + pm) (gm x)) sz.
Proof.
  intros H0 Ha Hd Hm Hin.
  apply (elem_buildable_pair 8 (fun m b ofs (x : X) => asset_rep m b ofs (ga x))
    (fun m b ofs (x : X) => amount_rep m b ofs (gm x)) pa 36 pm 40 sz); try assumption; try lia.
  - apply asset_rep_local.
  - eapply elem_buildable_align; [|apply asset_rep_buildable]. divides.
  - apply amount_rep_buildable.
Qed.

Lemma asset_amount_local {X : Type} (ga : X -> assetWith unit) (gm : X -> amountWith unit) pa pm sz :
  0 <= pa -> pa + 36 <= sz -> 0 <= pm -> pm + 40 <= sz ->
  elem_local (fun m b ofs x => asset_rep m b (ofs + pa) (ga x) /\ amount_rep m b (ofs + pm) (gm x)) sz.
Proof.
  intros. apply (elem_local_pair (fun m b ofs (x : X) => asset_rep m b ofs (ga x))
    (fun m b ofs (x : X) => amount_rep m b ofs (gm x)) pa 36 pm 40 sz); try assumption.
  - apply asset_rep_local.
  - apply amount_rep_local.
Qed.

(** ** Issuance *)
Lemma hash_option_buildable {X : Type} (g : X -> option hash256) :
  elem_buildable 8 (fun m b ofs x => forall h, g x = Some h -> uint32_array_at m b ofs (hash256_reg h)) 32.
Proof.
  apply elem_buildable_option; [lia|].
  eapply elem_buildable_align; [|apply (words_buildable hash256_reg hash_words_len)]. divides.
Qed.

Lemma hash_option_local {X : Type} (g : X -> option hash256) :
  elem_local (fun m b ofs x => forall h, g x = Some h -> uint32_array_at m b ofs (hash256_reg h)) 32.
Proof. apply elem_local_option. apply (words_local hash256_reg hash_words_len). Qed.

Lemma issuance_hash_rep_buildable delta gh :
  0 <= delta -> (8 | delta) -> delta + 32 <= 272 ->
  elem_buildable 8 (issuance_hash_rep delta gh) 280.
Proof.
  intros H0 Ha Hd.
  eapply elem_buildable_impl;
    [|apply (elem_buildable_pair 8
        (fun m b ofs (x : sigTxInput) =>
          forall h, gh (sigTxiIssuance x) = Some h -> uint32_array_at m b ofs (hash256_reg h))
        (fun m b ofs (x : sigTxInput) =>
          Mem.load Mint32 m b ofs = Some (Vint (issuance_tag (sigTxiIssuance x))))
        delta 32 272 4 280); try assumption; try lia; try divides].
  - intros m b ofs x [H1 H2]. split; assumption.
  - apply hash_option_local.
  - apply hash_option_buildable.
  - eapply elem_buildable_align; [|apply int32_buildable]. divides.
Qed.

Lemma issuance_hash_rep_local delta gh : 0 <= delta -> delta + 32 <= 280 ->
  elem_local (issuance_hash_rep delta gh) 280.
Proof.
  intros H0 Hd m1 m2 b ofs x [Ht Hh] Hl. split.
  - apply (Hl Mint32 (ofs + 272) _); [lia|change (size_chunk Mint32) with 4; lia|exact Ht].
  - intros h Hg. eapply (words_local hash256_reg hash_words_len); [exact (Hh h Hg)|].
    intros c o v H1 H2. apply Hl; lia.
Qed.

Lemma issuance_amount_rep_buildable : elem_buildable 8 issuance_amount_rep 280.
Proof.
  eapply elem_buildable_impl;
    [|apply (elem_buildable_pair 8
        (fun m b ofs (x : sigTxInput) =>
          forall i, sigTxiIssuance x = Some i -> amount_rep m b ofs (clearPrf (issuance_amount i)))
        (fun m b ofs (x : sigTxInput) =>
          Mem.load Mint32 m b ofs = Some (Vint (issuance_tag (sigTxiIssuance x))))
        232 40 272 4 280); try lia; try divides].
  - intros m b ofs x [H1 H2]. split; assumption.
  - apply elem_local_option. apply (amount_rep_local (fun i => clearPrf (issuance_amount i))).
  - apply elem_buildable_option; [lia|]. apply (amount_rep_buildable (fun i => clearPrf (issuance_amount i))).
  - eapply elem_buildable_align; [|apply int32_buildable]. divides.
Qed.

Lemma issuance_amount_rep_local : elem_local issuance_amount_rep 280.
Proof.
  intros m1 m2 b ofs x [Ht Hh] Hl. split.
  - apply (Hl Mint32 (ofs + 272) _); [lia|change (size_chunk Mint32) with 4; lia|exact Ht].
  - intros i Hi. eapply amount_rep_mono; [exact (Hh i Hi)|].
    intros c o v H1 H2. apply Hl; lia.
Qed.

(** ** A flag byte and an optional hash *)
Lemma flag_hash_rep_buildable g foff hoff :
  0 <= hoff -> (8 | hoff) -> hoff + 32 <= foff -> foff + 1 <= 544 ->
  elem_buildable 8 (flag_hash_rep g foff hoff) 544.
Proof.
  intros H0 Ha Hd Hin x m b ofs HP HA. unfold flag_hash_rep.
  destruct (hash_option_buildable g x m b (ofs + hoff)) as (m1 & B1 & L1);
    [intros o Ho; apply HP; lia|apply Z.divide_add_r; assumption|].
  destruct (built_store_bool m1 b (ofs + foff) (opt_is_some (g x)) (ofs + foff) (ofs + foff + 1))
    as (m2 & B2 & L2);
    [eapply built_range_perm; [exact B1|]; intros o Ho; apply HP; lia|lia|lia|].
  exists m2. split; [|split; [exact L2|]].
  - eapply built_trans; (eapply built_weaken; [| |eassumption]; lia).
  - intros h Hg. unfold hash_elem_rep.
    eapply (words_local hash256_reg hash_words_len); [exact (L1 h Hg)|].
    intros c o v H1 H2 Hl. eapply built_load_some; [exact B2| |exact Hl]. right; left. lia.
Qed.

Lemma flag_hash_rep_local g foff hoff :
  0 <= hoff -> hoff + 32 <= 544 -> 0 <= foff -> foff + 1 <= 544 ->
  elem_local (flag_hash_rep g foff hoff) 544.
Proof.
  intros H0 H1 H2 H3 m1 m2 b ofs x [Hf Hh] Hl. split.
  - apply (Hl Mint8unsigned (ofs + foff) _); [lia|change (size_chunk Mint8unsigned) with 1; lia|exact Hf].
  - intros h Hg. unfold hash_elem_rep in *.
    eapply (words_local hash256_reg hash_words_len); [exact (Hh h Hg)|].
    intros c o v Ha Hb. apply Hl; lia.
Qed.
