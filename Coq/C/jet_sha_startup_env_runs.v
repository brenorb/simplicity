(** The three environment-reading SHA-unit jets from any memory satisfying the
    startup invariant: for every input and every logical environment an
    environment and frames are constructed on top of it, the jet runs and
    returns the canonical result, and the invariant is re-established.  The
    environment relation and all global-object facts are discharged; the
    only premise left is [memcpy_model] of the accepted theorems. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Simplicity.Alg.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_exec C.jet_memcpy_model C.jet_bitmachine_rep C.jet_application_sep.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_frame_layout.
Require Import C.jet_input_layout C.jet_output_layout C.jet_output_layout_step C.jet_write_layout C.jet_encoding.
Require Import C.jet_constant_layout C.jet_wide C.jet_complement_wide_layout.
Require Import C.jet_read32s_layout C.jet_write32s_layout C.jet_uint32_array_init C.jet_sha256_iv_init.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_transport C.jet_sha_compress_call C.jet_sha_block_local.
Require Import C.jet_sha_ctx8_model C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_uchars_prep.
Require Import C.jet_sha_uchars_exec C.jet_sha_hash_exec C.jet_sha_finalize_exec.
Require Import C.jet_sha_add_n_init C.jet_sha_add_n_calls C.jet_sha_add_n_exec C.jet_sha_ctx8_add_jets.
Require Import C.jet_sha_ctx8_finalize_jet.
Require Import C.jet_sha_tapdata_prep C.jet_sha_tapdata_jet.
Require Import C.jet_sha_ctx_abs C.jet_sha_ctxi C.jet_sha_tagged_ctx C.jet_sha_hash_io.
Require Import C.jet_bitcoin_make_tapleaf_exec.
Require Import C.jet_bitcoin_effects C.jet_bitcoin_env_load.
Require Import C.jet_sha_indexed_exec C.jet_sha_index_eval C.jet_sha_steps.
Require Import C.jet_forWhile_seq C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim.
Require Import C.jet_bitcoin_words_hash C.jet_bitcoin_composite_hash.
Require Import C.jet_bitcoin_vh_hash_spec C.jet_bitcoin_vh_hash_prep.
Require Import C.jet_bitcoin_vh_hash_spec C.jet_bitcoin_vh_hash_prep C.jet_bitcoin_output_hash_jet.
Require Import C.jet_bitcoin_input_utxo_hash_jet.
Require Import C.jet_sha_u32be_exec C.jet_sha_ctxi_u32 C.jet_bitcoin_ctx_hash_spec C.jet_bitcoin_tx_hash.
Require Import C.jet_bitcoin_build_tapleaf_spec C.jet_bitcoin_input_hash_spec.
Require Import C.jet_buffer_input C.jet_read8s_layout C.jet_word32_chunks C.jet_readBit_layout.
Require Import C.jet_bitcoin_output_hash_jet C.jet_bitcoin_input_utxo_hash_jet C.jet_bitcoin_input_hash_jet.
Require Import C.jet_clight_forward C.jet_sha_initial_globals.
Require Import C.jet_sha_startup_globals C.jet_sha_startup_state.
Require Import C.jet_sha_startup_setup C.jet_sha_startup_env_callers C.jet_sha_startup_executable.
Require Import C.jet_frame_constructible_app C.jet_env_constructible C.jet_env_constructible_ext.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Set Default Timeout 120.

(** The invariant survives any extension of memory. *)
Lemma sha_startup_state_extension m0 m :
  sha_startup_state m0 -> memory_extension m0 m -> sha_startup_state m.
Proof.
  intros HS HE. eapply sha_startup_state_preserved; [exact HS| |].
  - intros b Hb. destruct (HE b Hb) as (Hv & _ & Hp). split; [exact Hv|].
    intros ofs p HP. exact (Hp ofs Max p HP).
  - intros chunk b ofs HIn.
    destruct (HE b (sha_state_blocks_valid m0 b HS HIn)) as (_ & Hl & _). exact (Hl chunk ofs).
Qed.

Lemma hlen (h : hash256) : length (hash256_reg h) = 8%nat.
Proof. exact (hash256_len h). Qed.

Ltac divides := apply Z.mod_divide; [discriminate|reflexivity].

Ltac keeps B :=
  rewrite (proj1 B) by
    (first [left; assumption | left; apply not_eq_sym; assumption
           | right; try change (size_chunk Mptr) with 8; cbn [size_chunk]; lia]).

(** Environment record, transaction record and an array of elements, built
    on top of any memory. *)
Lemma sha_env_array {X : Type} (m0 : mem) (xs : list X) (R : mem -> block -> Z -> X -> Prop)
    (sz adelta cdelta : Z) :
  0 <= sz -> (8 | sz) -> elem_local R sz -> elem_buildable 8 R sz ->
  0 <= adelta -> adelta + 8 <= 488 -> (8 | adelta) ->
  0 <= cdelta -> cdelta + 8 <= 488 -> (8 | cdelta) ->
  adelta + 8 <= cdelta \/ cdelta + 8 <= adelta ->
  exists m be bt bin,
    memory_extension m0 m /\
    Mem.valid_block m be /\ Mem.valid_block m bt /\ Mem.valid_block m bin /\
    Mem.load Mptr m be 0 = Some (Vptr bt (Ptrofs.repr 0)) /\
    Mem.load Mptr m bt adelta = Some (Vptr bin (Ptrofs.repr 0)) /\
    Mem.load Mint64 m bt cdelta = Some (Vlong (Int64.repr (Z.of_nat (length xs)))) /\
    forall j x, nth_error xs j = Some x -> R m bin (0 + sz * Z.of_nat j) x.
Proof.
  intros Hsz Hal HL HB Ha0 Ha1 Haa Hc0 Hc1 Hca Hdis.
  destruct (three_blocks_ext m0 56 488 (sz * Z.of_nat (length xs)))
    as (m & be & bt & bin & Net & Nei & Nti & Ve & Vt & Vi & Pe & Pt & Pi & E0' & Fe & Ft & Fi).
  destruct (built_store_ptr m be 0 bt (Ptrofs.repr 0) 0 8 eq_refl) as (m1 & B1 & L1);
    [intros o Ho; apply Pe; lia|apply Z.divide_0_r|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 488 Cur Writable B1 Pt) as Pt1.
  pose proof (built_range_perm _ _ _ _ _ bin 0 _ Cur Writable B1 Pi) as Pi1.
  destruct (built_store_ptr m1 bt adelta bin (Ptrofs.repr 0) adelta (adelta + 8) eq_refl) as (m2 & B2 & L2);
    [intros o Ho; apply Pt1; lia|exact Haa|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 488 Cur Writable B2 Pt1) as Pt2.
  pose proof (built_range_perm _ _ _ _ _ bin 0 _ Cur Writable B2 Pi1) as Pi2.
  destruct (built_store_int64 m2 bt cdelta (Int64.repr (Z.of_nat (length xs))) cdelta (cdelta + 8))
    as (m3 & B3 & L3); [intros o Ho; apply Pt2; lia|exact Hca|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bin 0 _ Cur Writable B3 Pi2) as Pi3.
  destruct (array_buildable R sz Hsz Hal HL HB xs m3 bin 0 Pi3 (Z.divide_0_r 8)) as (m4 & B4 & HR).
  exists m4, be, bt, bin.
  split.
  { eapply built_extension; [|exact Fi|exact B4]. eapply built_extension; [|exact Ft|exact B3].
    eapply built_extension; [|exact Ft|exact B2]. eapply built_extension; [exact E0'|exact Fe|exact B1]. }
  split; [repeat match goal with B : built _ _ _ _ _ |- _ => apply (proj1 (proj2 (proj2 B))) end; exact Ve|].
  split; [repeat match goal with B : built _ _ _ _ _ |- _ => apply (proj1 (proj2 (proj2 B))) end; exact Vt|].
  split; [repeat match goal with B : built _ _ _ _ _ |- _ => apply (proj1 (proj2 (proj2 B))) end; exact Vi|].
  split. { keeps B4. keeps B3. keeps B2. exact L1. }
  split. { keeps B4. keeps B3. exact L2. }
  split. { keeps B4. exact L3. }
  exact HR.
Qed.

Lemma nth_error_combine {A B : Type} (l1 : list A) (l2 : list B) : forall j a b,
  nth_error l1 j = Some a -> nth_error l2 j = Some b -> nth_error (combine l1 l2) j = Some (a, b).
Proof.
  revert l2. induction l1 as [|x t IH]; intros l2 j a b H1 H2; [destruct j; discriminate|].
  destruct l2 as [|y u]; [destruct j; discriminate|].
  destruct j as [|j]; cbn in *; [congruence|exact (IH u j a b H1 H2)].
Qed.

(** * Element relations *)

Lemma oh_elem_local : elem_local oh_elem_rep 40.
Proof.
  intros m1 m2 b ofs x [Hv Hh] Hl. split.
  - apply (Hl Mint64 ofs _); [lia|change (size_chunk Mint64) with 8; lia|exact Hv].
  - eapply (words_local hash256_reg hlen); [exact Hh|]. intros c o v H1 H2. apply Hl; lia.
Qed.

Lemma value_hash_buildable {X : Type} (gv : X -> int64) (gh : X -> hash256) :
  elem_buildable 8 (fun m b ofs x =>
    Mem.load Mint64 m b ofs = Some (Vlong (gv x)) /\
    uint32_array_at m b (ofs + 8) (hash256_reg (gh x))) 40.
Proof.
  eapply elem_buildable_impl;
    [|apply (elem_buildable_pair 8
        (fun m b ofs (x : X) => Mem.load Mint64 m b ofs = Some (Vlong (gv x)))
        (fun m b ofs (x : X) => uint32_array_at m b ofs (hash256_reg (gh x)))
        0 8 8 32 40); try lia; try divides].
  - intros m b ofs x [H1 H2]. rewrite Z.add_0_r in H1. split; assumption.
  - apply (load_local Mint64 (fun x : X => Vlong (gv x))).
  - apply int64_buildable.
  - eapply elem_buildable_align; [|apply (words_buildable (fun x : X => hash256_reg (gh x)));
      intro x; apply hlen]. divides.
Qed.

Lemma oh_elem_buildable : elem_buildable 8 oh_elem_rep 40.
Proof. exact (value_hash_buildable txoValue (fun o => byteStringHash (txoScript o))). Qed.

Definition iu_R (m : mem) (b : block) (ofs : Z) (x : sigTxInput * hash256) : Prop :=
  iu_elem_rep m b (ofs + 104) (sigTxiValue (fst x)) (snd x).

Lemma iu_R_local : elem_local iu_R 160.
Proof.
  intros m1 m2 b ofs x [Hv Hh] Hl. split.
  - apply (Hl Mint64 (ofs + 104) _); [lia|change (size_chunk Mint64) with 8; lia|exact Hv].
  - eapply (words_local hash256_reg hlen); [exact Hh|]. intros c o v H1 H2. apply Hl; lia.
Qed.

Lemma iu_R_buildable : elem_buildable 8 iu_R 160.
Proof.
  eapply elem_buildable_larger;
    [|apply (elem_buildable_shift 8 _ 40 104 ltac:(lia) ltac:(divides)
        (value_hash_buildable (fun x : sigTxInput * hash256 => sigTxiValue (fst x)) snd))]. lia.
Qed.

Definition ih_R (m : mem) (b : block) (ofs : Z) (x : sigTxInput * option hash256) : Prop :=
  ih_elem_rep m b ofs (fst x) (snd x).

Lemma ih_R_local : elem_local ih_R 160.
Proof.
  intros m1 m2 b ofs x (H1 & H2 & H3 & H4 & H5) Hl. unfold ih_R, ih_elem_rep.
  split; [|split; [|split; [|split]]].
  - eapply (words_local hash256_reg hlen); [exact H1|]. intros c o v Ha Hb. apply Hl; lia.
  - apply (Hl Mint64 (ofs + 96) _); [lia|change (size_chunk Mint64) with 8; lia|exact H2].
  - apply (Hl Mint64 (ofs + 144) _); [lia|change (size_chunk Mint64) with 8; lia|exact H3].
  - apply (Hl Mint8unsigned (ofs + 152) _); [lia|change (size_chunk Mint8unsigned) with 1; lia|exact H4].
  - intros h Hax. eapply (words_local hash256_reg hlen); [exact (H5 h Hax)|].
    intros c o v Ha Hb. apply Hl; lia.
Qed.

Lemma arr_keep m m' b lo hi b' ofs (h : hash256) :
  built m m' b lo hi -> b' <> b \/ ofs + 32 <= lo \/ hi <= ofs ->
  uint32_array_at m b' ofs (hash256_reg h) -> uint32_array_at m' b' ofs (hash256_reg h).
Proof.
  intros HB Hd Hr.
  exact (elem_local_built (fun m b ofs (h : hash256) => uint32_array_at m b ofs (hash256_reg h)) 32
    m m' b lo hi b' ofs h (words_local hash256_reg hlen) HB Hd Hr).
Qed.

Lemma ih_R_buildable : elem_buildable 8 ih_R 160.
Proof.
  intros [txi ax] m b ofs HP HA. unfold ih_R, ih_elem_rep. cbn [fst snd].
  assert (HA4 : (4 | ofs)) by (eapply Z.divide_trans; [|exact HA]; divides).
  assert (H0 : exists m1, built m m1 b ofs (ofs + 32) /\
    forall h, ax = Some h -> uint32_array_at m1 b (ofs + 0) (hash256_reg h)).
  { destruct ax as [h|].
    - destruct (built_uint32_array (hash256_reg h) m b ofs) as (m1 & B1 & L1);
        [rewrite hlen; intros o Ho; apply HP; lia|exact HA4|].
      rewrite hlen in B1. exists m1. split; [exact B1|].
      intros h' Hh. inversion Hh; subst h'. rewrite Z.add_0_r. exact L1.
    - exists m. split; [apply built_refl|]. intros h Hh. discriminate. }
  destruct H0 as (m1 & B1 & L1).
  pose proof (built_range_perm _ _ _ _ _ b ofs (ofs + 160) Cur Writable B1 HP) as P1.
  destruct (built_uint32_array (hash256_reg (opHash (sigTxiPreviousOutpoint txi))) m1 b (ofs + 64))
    as (m2 & B2 & L2);
    [rewrite hlen; intros o Ho; apply P1; lia|apply Z.divide_add_r; [exact HA4|divides]|].
  rewrite hlen in B2.
  pose proof (built_range_perm _ _ _ _ _ b ofs (ofs + 160) Cur Writable B2 P1) as P2.
  destruct (built_store_int64 m2 b (ofs + 96)
    (Int64.repr (Int.unsigned (opIndex (sigTxiPreviousOutpoint txi)))) (ofs + 96) (ofs + 104))
    as (m3 & B3 & L3);
    [intros o Ho; apply P2; lia|apply Z.divide_add_r; [exact HA|divides]|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ b ofs (ofs + 160) Cur Writable B3 P2) as P3.
  destruct (built_store_int64 m3 b (ofs + 144) (Int64.repr (Int.unsigned (sigTxiSequence txi)))
    (ofs + 144) (ofs + 152)) as (m4 & B4 & L4);
    [intros o Ho; apply P3; lia|apply Z.divide_add_r; [exact HA|divides]|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ b ofs (ofs + 160) Cur Writable B4 P3) as P4.
  destruct (built_store_bool m4 b (ofs + 152) (ih_has ax) (ofs + 152) (ofs + 153)) as (m5 & B5 & L5);
    [intros o Ho; apply P4; lia|lia|lia|].
  exists m5. split.
  { eapply built_trans; [eapply built_weaken; [| |exact B1]; lia|].
    eapply built_trans; [eapply built_weaken; [| |exact B2]; lia|].
    eapply built_trans; [eapply built_weaken; [| |exact B3]; lia|].
    eapply built_trans; (eapply built_weaken; [| |eassumption]; lia). }
  split.
  { eapply arr_keep; [exact B5|right; left; lia|].
    eapply arr_keep; [exact B4|right; left; lia|].
    eapply arr_keep; [exact B3|right; left; lia|exact L2]. }
  split.
  { rewrite (proj1 B5) by (right; left; cbn; lia). rewrite (proj1 B4) by (right; left; cbn; lia).
    exact L3. }
  split; [rewrite (proj1 B5) by (right; left; cbn; lia); exact L4|].
  split; [exact L5|].
  intros h Hh.
  eapply arr_keep; [exact B5|right; left; lia|].
  eapply arr_keep; [exact B4|right; left; lia|].
  eapply arr_keep; [exact B3|right; left; lia|].
  eapply arr_keep; [exact B2|right; left; lia|exact (L1 h Hh)].
Qed.

(** * Environments on top of the invariant

    The relation is produced for every memory that keeps the loads of the
    constructed one (so that it survives the frame construction), and
    modulo the global facts, which the invariant provides. *)
Definition sha_env_built (rep : mem -> val -> ext_environment -> list (block * Z * Z) -> Prop)
    (m0 : mem) (e : ext_environment) : Prop :=
  exists m env fp,
    sha_startup_state m /\ memory_extension m0 m /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp /\
    forall m', (forall b c o, Mem.valid_block m b -> Mem.load c m' b o = Mem.load c m b o) ->
      sha_globals_ok m' -> rep m' env e (fp ++ sha_global_footprint).

Lemma ptrofs_max : Ptrofs.max_unsigned = 18446744073709551615.
Proof. reflexivity. Qed.

Lemma repr_small z : 0 <= z < 4294967296 -> Int64.unsigned (Int64.repr z) = z.
Proof.
  intros H. apply Int64.unsigned_repr. change Int64.max_unsigned with 18446744073709551615. lia.
Qed.

Lemma ext_inputs_fit (e : ext_environment) :
  0 <= Z.of_nat (length (sigTxIn (Bitcoin.envTx (extBase e)))) < 4294967296.
Proof.
  pose proof (sigTxInBounds (Bitcoin.envTx (extBase e))) as Hb. rewrite Zlength_correct in Hb.
  change Int.modulus with 4294967296 in Hb. lia.
Qed.

Lemma ext_outputs_fit (e : ext_environment) :
  0 <= Z.of_nat (length (sigTxOut (Bitcoin.envTx (extBase e)))) < 4294967296.
Proof.
  pose proof (sigTxOutBounds (Bitcoin.envTx (extBase e))) as Hb. rewrite Zlength_correct in Hb.
  change Int.modulus with 4294967296 in Hb. lia.
Qed.

Lemma output_hash_env_built m0 e : sha_startup_state m0 -> sha_env_built output_hash_rep m0 e.
Proof.
  intros HS. pose proof (ext_outputs_fit e) as Hn.
  destruct (sha_env_array m0 (sigTxOut (Bitcoin.envTx (extBase e))) oh_elem_rep 40 8 456
    ltac:(lia) ltac:(divides) oh_elem_local oh_elem_buildable
    ltac:(lia) ltac:(lia) ltac:(divides) ltac:(lia) ltac:(lia) ltac:(divides) ltac:(left; lia))
    as (m & be & bt & bin & HE & Ve & Vt & Vi & L1 & L2 & L3 & HR).
  exists m, (Vptr be (Ptrofs.repr 0)),
    [(be, 0, 0 + 8); (bt, 0 + 8, 0 + 16);
    (bin, 0, 0 + 40 * Z.of_nat (length (sigTxOut (Bitcoin.envTx (extBase e)))))].
  split; [exact (sha_startup_state_extension m0 m HS HE)|]. split; [exact HE|]. split.
  2:{ intros m' Hl Hg.
      exists be, 0, bt, 0, bin, 0, (Int64.repr (Z.of_nat (length (sigTxOut (Bitcoin.envTx (extBase e)))))).
      rewrite ptrofs_max.
      split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [lia|]. split; [lia|].
      split; [rewrite (Hl be Mptr _ Ve); exact L1|].
      split; [rewrite (Hl bt Mptr _ Vt); exact L2|].
      split; [rewrite (Hl bt Mint64 _ Vt); exact L3|].
      split; [apply repr_small; exact Hn|].
      split.
      { intros j o Hj. eapply oh_elem_local; [exact (HR j o Hj)|].
        intros c o' v _ _ Hv. rewrite (Hl bin c o' Vi). exact Hv. }
      split; [exact Hg|reflexivity]. }
  repeat constructor; assumption.
Qed.

Lemma input_utxo_hash_env_built m0 e :
  sha_startup_state m0 -> sha_env_built input_utxo_hash_rep m0 e.
Proof.
  intros HS. pose proof (ext_inputs_fit e) as Hn.
  set (ins := sigTxIn (Bitcoin.envTx (extBase e))) in *.
  assert (Hlen : length (combine ins (extInScriptHash e)) = length ins).
  { rewrite combine_length, (extInScriptHash_len e). apply Nat.min_id. }
  destruct (sha_env_array m0 (combine ins (extInScriptHash e)) iu_R 160 0 448
    ltac:(lia) ltac:(divides) iu_R_local iu_R_buildable
    ltac:(lia) ltac:(lia) ltac:(divides) ltac:(lia) ltac:(lia) ltac:(divides) ltac:(left; lia))
    as (m & be & bt & bin & HE & Ve & Vt & Vi & L1 & L2 & L3 & HR).
  rewrite Hlen in L3.
  exists m, (Vptr be (Ptrofs.repr 0)),
    [(be, 0, 0 + 8); (bt, 0 + 0, 0 + 8); (bin, 0, 0 + 160 * Z.of_nat (length ins))].
  split; [exact (sha_startup_state_extension m0 m HS HE)|]. split; [exact HE|]. split.
  2:{ intros m' Hl Hg.
      exists be, 0, bt, 0, bin, 0, (Int64.repr (Z.of_nat (length ins))).
      rewrite ptrofs_max.
      split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [lia|]. split; [fold ins; lia|].
      split; [rewrite (Hl be Mptr _ Ve); exact L1|].
      split; [rewrite (Hl bt Mptr _ Vt); exact L2|].
      split; [rewrite (Hl bt Mint64 _ Vt); exact L3|].
      split; [apply repr_small; exact Hn|].
      split.
      { intros j txi sh Hj Hs.
        pose proof (HR j (txi, sh) (nth_error_combine _ _ j txi sh Hj Hs)) as Hr.
        eapply (iu_R_local m m' bin _ (txi, sh)); [exact Hr|].
        intros c o' v _ _ Hv. rewrite (Hl bin c o' Vi). exact Hv. }
      split; [exact Hg|reflexivity]. }
  repeat constructor; assumption.
Qed.

Lemma input_hash_env_built m0 e : sha_startup_state m0 -> sha_env_built input_hash_rep m0 e.
Proof.
  intros HS. pose proof (ext_inputs_fit e) as Hn.
  set (ins := sigTxIn (Bitcoin.envTx (extBase e))) in *.
  assert (Hlen : length (combine ins (extInAnnexHash e)) = length ins).
  { rewrite combine_length, (extInAnnexHash_len e). apply Nat.min_id. }
  destruct (sha_env_array m0 (combine ins (extInAnnexHash e)) ih_R 160 0 448
    ltac:(lia) ltac:(divides) ih_R_local ih_R_buildable
    ltac:(lia) ltac:(lia) ltac:(divides) ltac:(lia) ltac:(lia) ltac:(divides) ltac:(left; lia))
    as (m & be & bt & bin & HE & Ve & Vt & Vi & L1 & L2 & L3 & HR).
  rewrite Hlen in L3.
  exists m, (Vptr be (Ptrofs.repr 0)),
    [(be, 0, 0 + 8); (bt, 0 + 0, 0 + 8); (bin, 0, 0 + 160 * Z.of_nat (length ins))].
  split; [exact (sha_startup_state_extension m0 m HS HE)|]. split; [exact HE|]. split.
  2:{ intros m' Hl Hg.
      exists be, 0, bt, 0, bin, 0, (Int64.repr (Z.of_nat (length ins))).
      rewrite ptrofs_max.
      split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [lia|]. split; [fold ins; lia|].
      split; [rewrite (Hl be Mptr _ Ve); exact L1|].
      split; [rewrite (Hl bt Mptr _ Vt); exact L2|].
      split; [rewrite (Hl bt Mint64 _ Vt); exact L3|].
      split; [apply repr_small; exact Hn|].
      split.
      { intros j txi ax Hj Hs.
        pose proof (HR j (txi, ax) (nth_error_combine _ _ j txi ax Hj Hs)) as Hr.
        eapply (ih_R_local m m' bin _ (txi, ax)); [exact Hr|].
        intros c o' v _ _ Hv. rewrite (Hl bin c o' Vi). exact Hv. }
      split; [exact Hg|reflexivity]. }
  repeat constructor; assumption.
Qed.

(** * The jets from any memory with the invariant

    For every input and every logical environment: an environment and
    frames are built on top of the given memory (which may be the initial
    memory of the unit), the jet returns true and leaves the canonical
    result, the invariant holds again and the given memory is untouched. *)
Definition sha_env_runs_everywhere (f : function) (A B : Ty)
    (spec : A -> ext_environment -> option B) : Prop :=
  forall (a : A) (e : ext_environment) (m0 : mem),
  sha_startup_state m0 ->
  exists m bd bs bw env mf value,
    spec a e = Some value /\
    Clight2.eval_funcall sha_ge m (Internal f)
      [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw 0 (Z.of_nat (bitSize B)) (encode value) /\
    sha_startup_state mf /\
    (forall b chunk ofs, Mem.valid_block m0 b ->
      Mem.load chunk mf b ofs = Mem.load chunk m0 b ofs).

Theorem sha_startup_env_runs f A B rep spec :
  sha_startup_env_spec f ext_environment A B rep spec ->
  Z.of_nat (bitSize A) <= Int64.max_unsigned ->
  Z.of_nat (bitSize B) <= Int64.max_unsigned ->
  (forall m0 e, sha_startup_state m0 -> sha_env_built rep m0 e) ->
  sha_env_runs_everywhere f A B spec.
Proof.
  intros HSpec HA HB HBuilt a e m0 HS0.
  destruct (HBuilt m0 e HS0) as (m1 & env & fp & HS1 & HE & HV & HRep).
  destruct (sha_startup_frames_constructible m1 (encode a) (Z.of_nat (bitSize B)) HS1)
    as (m & bd & bs & bi & bw & edge & HS & HBase & HAlign & HFields & HInput & HOutput & HOld).
  { rewrite encode_length. exact HA. }
  { lia. }
  assert (HSep : Forall (fun '(b, lo, hi) =>
      out_sep bd 0 bw 0 (Z.of_nat (bitSize B)) (Z.of_nat (bitSize B)) b lo hi) fp).
  { eapply Forall_impl; [|exact HV]. intros [[b lo] hi] Hb.
    destruct (HOld b Hb) as (_ & Nd & Nw & _). split; left; assumption. }
  destruct (HSpec e env m bd 0 bs 0 bi bw edge 0 (Z.of_nat (bitSize B)) 0 a fp HS
    (fun Hg => HRep m (fun b c o Hb => proj2 (proj2 (proj2 (HOld b Hb))) c o) Hg)
    HSep HBase HAlign HFields ltac:(lia) ltac:(lia) HInput HOutput)
    as (mf & value & HValue & HCall & HOut & _ & _ & HLoads & HFinal).
  exists m, bd, bs, bw, env, mf, value.
  split; [exact HValue|]. split; [exact HCall|]. split; [exact HOut|]. split; [exact HFinal|].
  intros b chunk ofs Hb. destruct (HE b Hb) as (Hv1 & Hl1 & _).
  destruct (HOld b Hv1) as (Hv & Nd & Nw & HL).
  rewrite HLoads; [rewrite HL; exact (Hl1 chunk ofs)|exact Hv|left; exact Nd|left; exact Nw].
Qed.

Theorem bitcoin_output_hash_startup_runs_everywhere : memcpy_model ->
  sha_env_runs_everywhere f_simplicity_bitcoin_output_hash (Word 5) (Ty.Sum Ty.Unit (Word 8))
    (fun a e => @vh_hash_spec (BitcoinFull.Base Bitcoin.OutputValue)
      (BitcoinFull.Base Bitcoin.OutputScriptHash) fullalg a e).
Proof.
  intros Hmodel.
  exact (sha_startup_env_runs _ _ _ _ _ (bitcoin_output_hash_startup_env_spec Hmodel)
    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) output_hash_env_built).
Qed.

Theorem bitcoin_input_utxo_hash_startup_runs_everywhere : memcpy_model ->
  sha_env_runs_everywhere f_simplicity_bitcoin_input_utxo_hash (Word 5) (Ty.Sum Ty.Unit (Word 8))
    (fun a e => @vh_hash_spec (BitcoinFull.Base Bitcoin.InputValue)
      (BitcoinFull.Ext BitcoinExt.InputScriptHash) fullalg a e).
Proof.
  intros Hmodel.
  exact (sha_startup_env_runs _ _ _ _ _ (bitcoin_input_utxo_hash_startup_env_spec Hmodel)
    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) input_utxo_hash_env_built).
Qed.

Theorem bitcoin_input_hash_startup_runs_everywhere : memcpy_model ->
  sha_env_runs_everywhere f_simplicity_bitcoin_input_hash (Word 5) (Ty.Sum Ty.Unit (Word 8))
    (fun a e => @input_hash_spec fullalg a e).
Proof.
  intros Hmodel.
  exact (sha_startup_env_runs _ _ _ _ _ (bitcoin_input_hash_startup_env_spec Hmodel)
    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) input_hash_env_built).
Qed.
