(** The remaining twenty Elements jets run for every logical environment:
    representing memories for the record-only relations (transaction and
    environment records), the taproot record, the transaction id, the
    genesis hash, the scalar input relations and the annex/pegin arrays.

    With [jet_elements_runs_everywhere] every proved Elements jet has a
    statement without memory, frame or environment premise.  [tappath] keeps
    the bound its relation states on the input itself (at most 128 path
    elements, the C record stores the length in one byte). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Import Simplicity.Ty Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_partial C.jet_uint32_array_init C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_encoding.
Require Import C.jet_application_contract C.jet_application_sep C.jet_application_partial.
Require Import C.jet_frame_constructible_app C.jet_env_constructible C.jet_env_constructible_array.
Require Import C.jet_elements_prim C.jet_elements_linkage C.jet_elements_env_constructible.
Require Import C.jet_elements_hash_elem C.jet_elements_hash_getter_local.
Require Import C.jet_elements_indexed_scalar C.jet_elements_current_jets.
Require Import C.jet_elements_version_local C.jet_elements_locktime_local C.jet_elements_current_index_local.
Require Import C.jet_elements_count_local C.jet_elements_is_final_spec C.jet_elements_is_final_local.
Require Import C.jet_elements_lock_local C.jet_elements_check_lock.
Require Import C.jet_elements_script_cmr_local C.jet_elements_genesis_hash_local.
Require Import C.jet_elements_tapleaf_version_local C.jet_elements_tappath_local.
Require C.jet_elements_annex_local C.jet_elements_pegin_local.
Require Import C.jet_elements_executable C.jet_elements_executable_lock C.jet_elements_executable_count.
Require Import C.jet_elements_executable_current C.jet_elements_runs_everywhere.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Ltac divides := apply Z.mod_divide; [discriminate|reflexivity].

Ltac keepe B :=
  rewrite (proj1 B) by
    (first [left; assumption | left; apply not_eq_sym; assumption
           | right; try change (size_chunk Mptr) with 8; cbn [size_chunk]; lia]).

Ltac valid_through V :=
  repeat match goal with B : built _ _ _ _ _ |- _ => apply (proj1 (proj2 (proj2 B))) end; exact V.

Lemma hlen (h : hash256) : length (hash256_reg h) = 8%nat.
Proof. exact (hash256_len h). Qed.

Lemma hash_elem_local : elem_local hash_elem_rep 32.
Proof. exact (words_local hash256_reg hlen). Qed.

Lemma hash_elem_buildable : elem_buildable 4 hash_elem_rep 32.
Proof. exact (words_buildable hash256_reg hlen). Qed.

Lemma arr_keep m m' b lo hi b' ofs (h : hash256) :
  built m m' b lo hi -> b' <> b \/ ofs + 32 <= lo \/ hi <= ofs ->
  uint32_array_at m b' ofs (hash256_reg h) -> uint32_array_at m' b' ofs (hash256_reg h).
Proof. intros HB Hd Hr. exact (elem_local_built hash_elem_rep 32 m m' b lo hi b' ofs h hash_elem_local HB Hd Hr). Qed.

Lemma byte_load_result n : 0 <= n < 256 ->
  Val.load_result Mint8unsigned (Vint (Int.repr n)) = Vint (Int.repr n).
Proof.
  intros Hn. cbn. f_equal. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr n))).
  rewrite Int.zero_ext_mod by (change Int.zwordsize with 32; lia).
  rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  change (two_p 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma repr_small z : 0 <= z < 4294967296 -> Int64.unsigned (Int64.repr z) = z.
Proof. intros H. apply Int64.unsigned_repr. rewrite int64_max. lia. Qed.

(** * Environment and transaction records *)
Lemma elements_record_built (ix nI nO ver lt : int64) (final : bool) :
  exists m be bt,
    Mem.valid_block m be /\ Mem.valid_block m bt /\
    Mem.load Mptr m be 0 = Some (Vptr bt (Ptrofs.repr 0)) /\
    Mem.load Mint64 m be 80 = Some (Vlong ix) /\
    Mem.load Mint64 m bt 696 = Some (Vlong nI) /\
    Mem.load Mint64 m bt 704 = Some (Vlong nO) /\
    Mem.load Mint64 m bt 720 = Some (Vlong ver) /\
    Mem.load Mint64 m bt 728 = Some (Vlong lt) /\
    Mem.load Mint8unsigned m bt 752 = Some (Vint (if final then Int.one else Int.zero)).
Proof.
  destruct (three_blocks Mem.empty 88 760 0)
    as (m & be & bt & bin & Net & _ & _ & Ve & Vt & _ & Pe & Pt & _).
  destruct (built_store_ptr m be 0 bt (Ptrofs.repr 0) 0 8 eq_refl) as (m1 & B1 & L1);
    [intros o Ho; apply Pe; lia|apply Z.divide_0_r|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ be 0 88 Cur Writable B1 Pe) as Pe1.
  pose proof (built_range_perm _ _ _ _ _ bt 0 760 Cur Writable B1 Pt) as Pt1.
  destruct (built_store_int64 m1 be 80 ix 80 88) as (m2 & B2 & L2);
    [intros o Ho; apply Pe1; lia|divides|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 760 Cur Writable B2 Pt1) as Pt2.
  destruct (built_store_int64 m2 bt 696 nI 696 704) as (m3 & B3 & L3);
    [intros o Ho; apply Pt2; lia|divides|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 760 Cur Writable B3 Pt2) as Pt3.
  destruct (built_store_int64 m3 bt 704 nO 704 712) as (m4 & B4 & L4);
    [intros o Ho; apply Pt3; lia|divides|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 760 Cur Writable B4 Pt3) as Pt4.
  destruct (built_store_int64 m4 bt 720 ver 720 728) as (m5 & B5 & L5);
    [intros o Ho; apply Pt4; lia|divides|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 760 Cur Writable B5 Pt4) as Pt5.
  destruct (built_store_int64 m5 bt 728 lt 728 736) as (m6 & B6 & L6);
    [intros o Ho; apply Pt5; lia|divides|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 760 Cur Writable B6 Pt5) as Pt6.
  destruct (built_store_bool m6 bt 752 final 752 753) as (m7 & B7 & L7);
    [intros o Ho; apply Pt6; lia|lia|lia|].
  exists m7, be, bt.
  split; [valid_through Ve|]. split; [valid_through Vt|].
  split. { keepe B7. keepe B6. keepe B5. keepe B4. keepe B3. keepe B2. exact L1. }
  split. { keepe B7. keepe B6. keepe B5. keepe B4. keepe B3. exact L2. }
  split. { keepe B7. keepe B6. keepe B5. keepe B4. exact L3. }
  split. { keepe B7. keepe B6. keepe B5. exact L4. }
  split. { keepe B7. keepe B6. exact L5. }
  split. { keepe B7. exact L6. }
  exact L7.
Qed.

Lemma elements_env_record (e : Elements.env) :
  exists m be bt,
    Mem.valid_block m be /\ Mem.valid_block m bt /\
    Mem.load Mptr m be 0 = Some (Vptr bt (Ptrofs.repr 0)) /\
    (exists ix, Mem.load Mint64 m be 80 = Some (Vlong ix) /\
       Int64.unsigned ix = Z.of_nat (Elements.envIx e)) /\
    (exists nI, Mem.load Mint64 m bt 696 = Some (Vlong nI) /\
       Int64.unsigned nI = Z.of_nat (length (sigTxIn (Elements.envTx e)))) /\
    (exists nO, Mem.load Mint64 m bt 704 = Some (Vlong nO) /\
       Int64.unsigned nO = Z.of_nat (length (sigTxOut (Elements.envTx e)))) /\
    (exists ver, Mem.load Mint64 m bt 720 = Some (Vlong ver) /\
       Int64.unsigned ver = Int.unsigned (sigTxVersion (Elements.envTx e))) /\
    (exists lt, Mem.load Mint64 m bt 728 = Some (Vlong lt) /\
       Int64.unsigned lt = Int.unsigned (sigTxLock (Elements.envTx e))) /\
    Mem.load Mint8unsigned m bt 752 =
      Some (Vint (bool_int (forallb sequence_final (sigTxIn (Elements.envTx e))))).
Proof.
  pose proof (sigTxInBounds (Elements.envTx e)) as HbI. rewrite Zlength_correct in HbI.
  pose proof (sigTxOutBounds (Elements.envTx e)) as HbO. rewrite Zlength_correct in HbO.
  change Int.modulus with 4294967296 in HbI, HbO.
  pose proof (Elements.envIxWord32 e) as Hix.
  destruct (elements_record_built
    (Int64.repr (Z.of_nat (Elements.envIx e)))
    (Int64.repr (Z.of_nat (length (sigTxIn (Elements.envTx e)))))
    (Int64.repr (Z.of_nat (length (sigTxOut (Elements.envTx e)))))
    (Int64.repr (Int.unsigned (sigTxVersion (Elements.envTx e))))
    (Int64.repr (Int.unsigned (sigTxLock (Elements.envTx e))))
    (forallb sequence_final (sigTxIn (Elements.envTx e))))
    as (m & be & bt & Ve & Vt & L0 & L1 & L2 & L3 & L4 & L5 & L6).
  exists m, be, bt. split; [exact Ve|]. split; [exact Vt|]. split; [exact L0|].
  split; [eexists; split; [exact L1|apply repr_small; lia]|].
  split; [eexists; split; [exact L2|apply repr_small; lia]|].
  split; [eexists; split; [exact L3|apply repr_small; lia]|].
  split; [eexists; split; [exact L4|apply repr_small; exact (Int.unsigned_range _)]|].
  split; [eexists; split; [exact L5|apply repr_small; exact (Int.unsigned_range _)]|exact L6].
Qed.

Ltac rec_env e :=
  destruct (elements_env_record e)
    as (m & be & bt & Ve & Vt & L0 & (ix & Lix & Hix) & (nI & LnI & HnI) & (nO & LnO & HnO) &
        (ver & Lver & Hver) & (lt & Llt & Hlt) & Lfin).

Ltac fin :=
  cbv beta; rewrite ?ptrofs_max; repeat split; cbv beta;
  first [reflexivity | lia | assumption].

Ltac valid_fp := repeat constructor; assumption.

Lemma elements_version_env_rep_constructible e : exists m env, elements_version_env_rep m env e.
Proof. rec_env e. exists m, (Vptr be (Ptrofs.repr 0)), be, 0, bt, 0, ver. fin. Qed.

Lemma elements_locktime_env_rep_constructible e : exists m env, elements_locktime_env_rep m env e.
Proof. rec_env e. exists m, (Vptr be (Ptrofs.repr 0)), be, 0, bt, 0, lt. fin. Qed.

Lemma elements_current_index_env_rep_constructible e :
  exists m env, elements_current_index_env_rep m env e.
Proof. rec_env e. exists m, (Vptr be (Ptrofs.repr 0)), be, 0, ix. fin. Qed.

Lemma elements_num_inputs_env_rep_constructible e : exists m env, elements_num_inputs_env_rep m env e.
Proof.
  rec_env e. unfold elements_num_inputs_env_rep, elements_count_env_rep.
  exists m, (Vptr be (Ptrofs.repr 0)), be, 0, bt, 0, nI. fin.
Qed.

Lemma elements_num_outputs_env_rep_constructible e : exists m env, elements_num_outputs_env_rep m env e.
Proof.
  rec_env e. unfold elements_num_outputs_env_rep, elements_count_env_rep.
  exists m, (Vptr be (Ptrofs.repr 0)), be, 0, bt, 0, nO. fin.
Qed.

Lemma elements_tx_is_final_env_rep_constructible e :
  exists m env fp, elements_tx_is_final_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  rec_env e. exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0. fin. }
  valid_fp.
Qed.

Lemma elements_lock_env_rep_constructible e :
  exists m env fp, elements_lock_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  rec_env e. exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0, lt. fin. }
  valid_fp.
Qed.

Lemma elements_check_lock_env_rep_constructible e : exists m env, elements_check_lock_env_rep m env e.
Proof.
  destruct (elements_lock_env_rep_constructible e) as (m & env & fp & H & _).
  exists m, env, fp. exact H.
Qed.

(** * The taproot record, the genesis hash and the transaction id *)
Lemma elements_taproot_built (key cmr : hash256) (path : list hash256) (lenv verv : Z) :
  0 <= lenv < 256 -> 0 <= verv < 256 ->
  exists m be bt bp,
    Mem.valid_block m be /\ Mem.valid_block m bt /\ Mem.valid_block m bp /\
    Mem.load Mptr m be 8 = Some (Vptr bt (Ptrofs.repr 0)) /\
    Mem.load Mptr m bt 0 = Some (Vptr bp (Ptrofs.repr 0)) /\
    Mem.load Mint8unsigned m bt 168 = Some (Vint (Int.repr lenv)) /\
    Mem.load Mint8unsigned m bt 169 = Some (Vint (Int.repr verv)) /\
    uint32_array_at m bt 104 (hash256_reg key) /\
    uint32_array_at m bt 136 (hash256_reg cmr) /\
    forall j h, nth_error path j = Some h -> hash_elem_rep m bp (0 + 32 * Z.of_nat j) h.
Proof.
  intros Hlen Hver.
  destruct (three_blocks Mem.empty 88 176 (32 * Z.of_nat (length path)))
    as (m & be & bt & bp & Net & Nep & Ntp & Ve & Vt & Vp & Pe & Pt & Pp).
  destruct (built_store_ptr m be 8 bt (Ptrofs.repr 0) 8 16 eq_refl) as (m1 & B1 & L1);
    [intros o Ho; apply Pe; lia|divides|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 176 Cur Writable B1 Pt) as Pt1.
  pose proof (built_range_perm _ _ _ _ _ bp 0 _ Cur Writable B1 Pp) as Pp1.
  destruct (built_store_ptr m1 bt 0 bp (Ptrofs.repr 0) 0 8 eq_refl) as (m2 & B2 & L2);
    [intros o Ho; apply Pt1; lia|apply Z.divide_0_r|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 176 Cur Writable B2 Pt1) as Pt2.
  pose proof (built_range_perm _ _ _ _ _ bp 0 _ Cur Writable B2 Pp1) as Pp2.
  destruct (built_store m2 bt Mint8unsigned 168 (Vint (Int.repr lenv)) 168 169) as (m3 & B3 & L3);
    [intros o Ho; apply Pt2; cbn in Ho; lia|apply Z.divide_1_l|lia|cbn; lia|].
  rewrite (byte_load_result lenv Hlen) in L3.
  pose proof (built_range_perm _ _ _ _ _ bt 0 176 Cur Writable B3 Pt2) as Pt3.
  pose proof (built_range_perm _ _ _ _ _ bp 0 _ Cur Writable B3 Pp2) as Pp3.
  destruct (built_store m3 bt Mint8unsigned 169 (Vint (Int.repr verv)) 169 170) as (m4 & B4 & L4);
    [intros o Ho; apply Pt3; cbn in Ho; lia|apply Z.divide_1_l|lia|cbn; lia|].
  rewrite (byte_load_result verv Hver) in L4.
  pose proof (built_range_perm _ _ _ _ _ bt 0 176 Cur Writable B4 Pt3) as Pt4.
  pose proof (built_range_perm _ _ _ _ _ bp 0 _ Cur Writable B4 Pp3) as Pp4.
  destruct (built_uint32_array (hash256_reg key) m4 bt 104) as (m5 & B5 & L5);
    [rewrite hlen; intros o Ho; apply Pt4; lia|divides|].
  rewrite hlen in B5.
  pose proof (built_range_perm _ _ _ _ _ bt 0 176 Cur Writable B5 Pt4) as Pt5.
  pose proof (built_range_perm _ _ _ _ _ bp 0 _ Cur Writable B5 Pp4) as Pp5.
  destruct (built_uint32_array (hash256_reg cmr) m5 bt 136) as (m6 & B6 & L6);
    [rewrite hlen; intros o Ho; apply Pt5; lia|divides|].
  rewrite hlen in B6.
  pose proof (built_range_perm _ _ _ _ _ bp 0 _ Cur Writable B6 Pp5) as Pp6.
  destruct (array_buildable hash_elem_rep 32 ltac:(lia) ltac:(divides) hash_elem_local
    (elem_buildable_align 4 8 _ _ ltac:(divides) hash_elem_buildable) path m6 bp 0 Pp6
    (Z.divide_0_r 8)) as (m7 & B7 & HR).
  exists m7, be, bt, bp.
  split; [valid_through Ve|]. split; [valid_through Vt|]. split; [valid_through Vp|].
  split. { keepe B7. keepe B6. keepe B5. keepe B4. keepe B3. keepe B2. exact L1. }
  split. { keepe B7. keepe B6. keepe B5. keepe B4. keepe B3. exact L2. }
  split. { keepe B7. keepe B6. keepe B5. keepe B4. exact L3. }
  split. { keepe B7. keepe B6. keepe B5. exact L4. }
  split.
  { eapply arr_keep; [exact B7|left; exact Ntp|].
    eapply arr_keep; [exact B6|right; left; lia|exact L5]. }
  split; [eapply arr_keep; [exact B7|left; exact Ntp|exact L6]|exact HR].
Qed.

Ltac close HR :=
  rewrite ?ptrofs_max; repeat (first [exact HR | split]);
  first [reflexivity | lia | assumption | exact HR].

Ltac tap key cmr path lenv verv :=
  destruct (elements_taproot_built key cmr path lenv verv)
    as (m & be & bt & bp & Ve & Vt & Vp & L1 & L2 & L3 & L4 & L5 & L6 & HR).

Lemma elements_script_cmr_env_rep_constructible (e : Elements.env) :
  exists m env fp, elements_script_cmr_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  tap (tapScriptCMR (Elements.envTap e)) (tapScriptCMR (Elements.envTap e)) (@nil hash256) 0 0; try lia.
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0. close HR. }
  valid_fp.
Qed.

Lemma elements_internal_key_rep_constructible (e : Elements.env) :
  exists m env fp, hash_getter_rep (fun e => tapInternalKey (Elements.envTap e)) 8 104 176 m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  tap (tapInternalKey (Elements.envTap e)) (tapInternalKey (Elements.envTap e)) (@nil hash256) 0 0; try lia.
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0. close HR. }
  valid_fp.
Qed.

Lemma elements_tapleaf_version_env_rep_constructible (e : Elements.env) :
  exists m env fp, elements_tapleaf_version_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  pose proof (Byte.unsigned_range (tapleafVersion (Elements.envTap e))) as Hb.
  change Byte.modulus with 256 in Hb.
  tap (tapInternalKey (Elements.envTap e)) (tapInternalKey (Elements.envTap e)) (@nil hash256) 0
    (Byte.unsigned (tapleafVersion (Elements.envTap e))); try lia.
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0. close HR. }
  valid_fp.
Qed.

Lemma elements_tappath_env_rep_constructible (e : Elements.env) :
  (length (tappath (Elements.envTap e)) <= 128)%nat ->
  exists m env fp, elements_tappath_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  intros Hl.
  tap (tapInternalKey (Elements.envTap e)) (tapInternalKey (Elements.envTap e))
    (tappath (Elements.envTap e)) (Z.of_nat (length (tappath (Elements.envTap e)))) 0; try lia.
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0, bp, 0. close HR. }
  valid_fp.
Qed.

Lemma elements_genesis_hash_env_rep_constructible (e : Elements.env) :
  exists m env fp, elements_genesis_hash_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  destruct (three_blocks Mem.empty 88 0 0) as (m & be & bt & bp & _ & _ & _ & Ve & _ & _ & Pe & _ & _).
  destruct (built_uint32_array (hash256_reg (Elements.envGenesisBlock e)) m be 16) as (m1 & B1 & L1);
    [rewrite hlen; intros o Ho; apply Pe; lia|divides|].
  exists m1, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0. rewrite ?ptrofs_max. repeat split; first [reflexivity | lia | exact L1]. }
  repeat constructor; valid_through Ve.
Qed.

Lemma elements_txid_rep_constructible (e : Elements.env) :
  exists m env fp, hash_getter_rep (fun e => txid (Elements.envTx e)) 0 664 760 m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  destruct (three_blocks Mem.empty 88 760 0)
    as (m & be & bt & bp & Net & _ & _ & Ve & Vt & _ & Pe & Pt & _).
  destruct (built_store_ptr m be 0 bt (Ptrofs.repr 0) 0 8 eq_refl) as (m1 & B1 & L1);
    [intros o Ho; apply Pe; lia|apply Z.divide_0_r|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 760 Cur Writable B1 Pt) as Pt1.
  destruct (built_uint32_array (hash256_reg (txid (Elements.envTx e))) m1 bt 664) as (m2 & B2 & L2);
    [rewrite hlen; intros o Ho; apply Pt1; lia|divides|].
  rewrite hlen in B2.
  exists m2, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0. rewrite ?ptrofs_max. repeat split; try first [reflexivity | lia | assumption].
    keepe B2. exact L1. }
  repeat constructor; [valid_through Ve|valid_through Vt].
Qed.

(** * Scalar input relations *)
Lemma elements_env_array {X : Type} (e : Elements.env) (xs : list X)
    (R : mem -> block -> Z -> X -> Prop) :
  elem_local R 544 -> elem_buildable 8 R 544 ->
  length xs = length (sigTxIn (Elements.envTx e)) ->
  exists m be bt bin nI ixv,
    Mem.valid_block m be /\ Mem.valid_block m bt /\ Mem.valid_block m bin /\
    Mem.load Mptr m be 0 = Some (Vptr bt (Ptrofs.repr 0)) /\
    Mem.load Mint64 m be 80 = Some (Vlong ixv) /\
    Mem.load Mptr m bt 0 = Some (Vptr bin (Ptrofs.repr 0)) /\
    Mem.load Mint64 m bt 696 = Some (Vlong nI) /\
    Int64.unsigned nI = Z.of_nat (length xs) /\
    Int64.unsigned ixv = Z.of_nat (Elements.envIx e) /\
    544 * Z.of_nat (length xs) <= 18446744073709551615 /\
    forall j x, nth_error xs j = Some x -> R m bin (0 + 544 * Z.of_nat j) x.
Proof.
  intros HL HB Hlen.
  pose proof (sigTxInBounds (Elements.envTx e)) as Hn. rewrite Zlength_correct in Hn.
  change Int.modulus with 4294967296 in Hn. rewrite <- Hlen in Hn.
  pose proof (Elements.envIxWord32 e) as Hix.
  destruct (env_array_built xs R 88 760 80 544 0 696
    (Int64.repr (Z.of_nat (Elements.envIx e))) Mem.empty
    ltac:(lia) ltac:(lia) ltac:(divides) ltac:(lia) ltac:(divides) HL HB
    ltac:(lia) ltac:(lia) ltac:(divides) ltac:(lia) ltac:(lia) ltac:(divides) ltac:(left; lia))
    as (m & be & bt & bin & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HR).
  exists m, be, bt, bin, (Int64.repr (Z.of_nat (length xs))), (Int64.repr (Z.of_nat (Elements.envIx e))).
  repeat (split; [assumption|]).
  split; [apply repr_small; lia|]. split; [apply repr_small; lia|].
  split; [lia|exact HR].
Qed.

Definition seq_R (m : mem) (b : block) (ofs : Z) (txi : sigTxInput) : Prop :=
  Mem.load Mint64 m b (ofs + 248) = Some (Vlong (Int64.repr (Int.unsigned (sigTxiSequence txi)))).

Lemma seq_R_local : elem_local seq_R 544.
Proof.
  intros m1 m2 b ofs x Hr Hl.
  apply (Hl Mint64 (ofs + 248) _); [lia|change (size_chunk Mint64) with 8; lia|exact Hr].
Qed.

Lemma seq_R_buildable : elem_buildable 8 seq_R 544.
Proof.
  eapply elem_buildable_larger;
    [|apply (elem_buildable_shift 8 (fun m b ofs (x : sigTxInput) =>
        Mem.load Mint64 m b ofs = Some (Vlong (Int64.repr (Int.unsigned (sigTxiSequence x))))) 8 248
        ltac:(lia) ltac:(divides));
      apply (int64_buildable (fun x : sigTxInput => Int64.repr (Int.unsigned (sigTxiSequence x))))]. lia.
Qed.

Lemma elements_input_sequence_rep_constructible (e : Elements.env) :
  exists m env fp,
    indexed_scalar_rep (fun e => sigTxIn (Elements.envTx e))
      (fun txi => Int.unsigned (sigTxiSequence txi)) 544 248 0 696 m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  destruct (elements_env_array e (sigTxIn (Elements.envTx e)) seq_R seq_R_local seq_R_buildable eq_refl)
    as (m & be & bt & bin & nI & ixv & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HnI & Hixv & Hs & HR).
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0, bin, 0, nI. close HR. }
  valid_fp.
Qed.

Lemma elements_current_sequence_rep_constructible (e : Elements.env) :
  exists m env,
    current_scalar_rep (fun e => sigTxIn (Elements.envTx e))
      (fun txi => Int.unsigned (sigTxiSequence txi)) 544 248 0 696 m env e.
Proof.
  destruct (elements_env_array e (sigTxIn (Elements.envTx e)) seq_R seq_R_local seq_R_buildable eq_refl)
    as (m & be & bt & bin & nI & ixv & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HnI & Hixv & Hs & HR).
  exists m, (Vptr be (Ptrofs.repr 0)).
  exists be, 0, bt, 0, bin, 0, nI, ixv. close HR.
Qed.

(** * Annex and pegin arrays: a flag byte and an optional hash per input *)
Lemma flag_opt_buildable (foff hoff : Z) (R : mem -> block -> Z -> option hash256 -> Prop) :
  0 <= hoff -> (4 | hoff) -> hoff + 32 <= foff -> foff + 1 <= 544 ->
  (forall m b ofs o,
    Mem.load Mint8unsigned m b (ofs + foff) =
      Some (Vint (if (match o with Some _ => true | None => false end) then Int.one else Int.zero)) ->
    (forall h, o = Some h -> hash_elem_rep m b (ofs + hoff) h) -> R m b ofs o) ->
  elem_buildable 8 R 544.
Proof.
  intros H0 Ha Hd Hin HI o m b ofs HP HA.
  assert (HO : exists m1, built m m1 b (ofs + hoff) (ofs + hoff + 32) /\
    forall h, o = Some h -> hash_elem_rep m1 b (ofs + hoff) h).
  { destruct o as [h|].
    - destruct (hash_elem_buildable h m b (ofs + hoff)) as (m1 & B1 & L1);
        [intros o' Ho; apply HP; lia
        |apply Z.divide_add_r; [eapply Z.divide_trans; [|exact HA]; divides|exact Ha]|].
      exists m1. split; [exact B1|]. intros h' Hh. inversion Hh; subst h'. exact L1.
    - exists m. split; [apply built_refl|]. intros h Hh. discriminate. }
  destruct HO as (m1 & B1 & L1).
  destruct (built_store_bool m1 b (ofs + foff) (match o with Some _ => true | None => false end)
    (ofs + foff) (ofs + foff + 1)) as (m2 & B2 & L2);
    [eapply built_range_perm; [exact B1|]; intros o' Ho; apply HP; lia|lia|lia|].
  exists m2. split.
  - eapply built_trans; (eapply built_weaken; [| |eassumption]; lia).
  - apply HI; [exact L2|]. intros h Hh. eapply hash_elem_local; [exact (L1 h Hh)|].
    intros c o' v Hx Hy Hl. eapply built_load_some; [exact B2| |exact Hl]. right; left. lia.
Qed.

Lemma annex_elem_local : elem_local jet_elements_annex_local.annex_elem_rep 544.
Proof.
  intros m1 m2 b ofs o [Hf Hh] Hl. split.
  - apply (Hl Mint8unsigned (ofs + 536) _); [lia|change (size_chunk Mint8unsigned) with 1; lia|exact Hf].
  - intros h Ho. eapply hash_elem_local; [exact (Hh h Ho)|]. intros c o' v Ha Hb. apply Hl; lia.
Qed.

Lemma annex_elem_buildable : elem_buildable 8 jet_elements_annex_local.annex_elem_rep 544.
Proof.
  apply (flag_opt_buildable 536 0); try lia; try divides.
  intros m b ofs o Hf Hh. split.
  - destruct o; exact Hf.
  - intros h Ho. pose proof (Hh h Ho) as H. rewrite Z.add_0_r in H. exact H.
Qed.

Lemma pegin_elem_local : elem_local jet_elements_pegin_local.pegin_elem_rep 544.
Proof.
  intros m1 m2 b ofs o [Hf Hh] Hl. split.
  - apply (Hl Mint8unsigned (ofs + 537) _); [lia|change (size_chunk Mint8unsigned) with 1; lia|exact Hf].
  - intros h Ho. eapply hash_elem_local; [exact (Hh h Ho)|]. intros c o' v Ha Hb. apply Hl; lia.
Qed.

Lemma pegin_elem_buildable : elem_buildable 8 jet_elements_pegin_local.pegin_elem_rep 544.
Proof.
  apply (flag_opt_buildable 537 32); try lia; try divides.
  intros m b ofs o Hf Hh. split; [destruct o; exact Hf|exact Hh].
Qed.

Lemma elements_input_annex_rep_constructible (e : Elements.env) :
  exists m env fp, jet_elements_annex_local.elements_input_annex_hash_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  destruct (elements_env_array e (jet_elements_annex_local.elements_annex_hashes e) _
    annex_elem_local annex_elem_buildable ltac:(apply map_length))
    as (m & be & bt & bin & nI & ixv & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HnI & Hixv & Hs & HR).
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0, bin, 0, nI. close HR. }
  valid_fp.
Qed.

Lemma elements_input_pegin_rep_constructible (e : Elements.env) :
  exists m env fp, jet_elements_pegin_local.elements_input_pegin_hash_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  destruct (elements_env_array e (jet_elements_pegin_local.elements_pegin_hashes e) _
    pegin_elem_local pegin_elem_buildable ltac:(apply map_length))
    as (m & be & bt & bin & nI & ixv & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HnI & Hixv & Hs & HR).
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0, bin, 0, nI. close HR. }
  valid_fp.
Qed.

(** * No-premise statements *)

Definition partial_runs_everywhere (f : function) (A B : Ty)
    (spec : A -> Elements.env -> option B) : Prop :=
  forall (a : A) (e : Elements.env),
  exists m bd bs bw env mf,
    Clight2.eval_funcall elements_ge m (Internal f)
      [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf
      (jet_partial_return (spec a e)) /\
    match spec a e with
    | Some b => frame_output_cells_at mf bw 0 (Z.of_nat (bitSize B)) (encode b)
    | None => True
    end.

Lemma plain_runs_everywhere f A B rep spec :
  application_runs_on_fresh_frames f elements_ge Elements.env A B rep spec ->
  (forall e, exists m env, rep m env e) -> runs_everywhere f A B spec.
Proof.
  intros HRun HRep a e. destruct (HRep e) as (m0 & env & Hr).
  destruct (HRun a e env m0 Hr) as (m & bd & bs & bw & mf & value & H1 & H2 & H3).
  exists m, bd, bs, bw, env, mf, value. repeat split; assumption.
Qed.

Lemma partial_runs_everywhere_intro f A B rep spec :
  application_partial_runs_on_fresh_frames f elements_ge Elements.env A B rep spec ->
  (forall e, exists m env, rep m env e) -> partial_runs_everywhere f A B spec.
Proof.
  intros HRun HRep a e. destruct (HRep e) as (m0 & env & Hr).
  destruct (HRun a e env m0 Hr) as (m & bd & bs & bw & mf & H1 & H2).
  exists m, bd, bs, bw, env, mf. split; assumption.
Qed.

Ltac statement' H :=
  lazymatch type of H with
  | application_runs_on_fresh_frames ?f _ _ ?A ?B _ ?s => exact (runs_everywhere f A B s)
  | application_sep_runs_on_fresh_frames ?f _ _ ?A ?B _ ?s => exact (runs_everywhere f A B s)
  | application_partial_runs_on_fresh_frames ?f _ _ ?A ?B _ ?s => exact (partial_runs_everywhere f A B s)
  end.

Theorem elements_version_runs_everywhere : ltac:(statement' elements_version_local_spec_executable).
Proof. exact (plain_runs_everywhere _ _ _ _ _ elements_version_local_spec_executable elements_version_env_rep_constructible). Qed.

Theorem elements_locktime_runs_everywhere : ltac:(statement' elements_locktime_local_spec_executable).
Proof. exact (plain_runs_everywhere _ _ _ _ _ elements_locktime_local_spec_executable elements_locktime_env_rep_constructible). Qed.

Theorem elements_current_index_runs_everywhere : ltac:(statement' elements_current_index_local_spec_executable).
Proof. exact (plain_runs_everywhere _ _ _ _ _ elements_current_index_local_spec_executable elements_current_index_env_rep_constructible). Qed.

Theorem elements_num_inputs_runs_everywhere : ltac:(statement' elements_num_inputs_local_spec_executable).
Proof. exact (plain_runs_everywhere _ _ _ _ _ elements_num_inputs_local_spec_executable elements_num_inputs_env_rep_constructible). Qed.

Theorem elements_num_outputs_runs_everywhere : ltac:(statement' elements_num_outputs_local_spec_executable).
Proof. exact (plain_runs_everywhere _ _ _ _ _ elements_num_outputs_local_spec_executable elements_num_outputs_env_rep_constructible). Qed.

Theorem elements_current_sequence_runs_everywhere :
  ltac:(statement' elements_current_sequence_local_spec_executable).
Proof. exact (plain_runs_everywhere _ _ _ _ _ elements_current_sequence_local_spec_executable elements_current_sequence_rep_constructible). Qed.

Theorem elements_tx_is_final_runs_everywhere : ltac:(statement' elements_tx_is_final_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ elements_tx_is_final_local_spec_executable elements_tx_is_final_env_rep_constructible). Qed.

Theorem elements_tx_lock_height_runs_everywhere : ltac:(statement' elements_tx_lock_height_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ elements_tx_lock_height_local_spec_executable elements_lock_env_rep_constructible). Qed.

Theorem elements_tx_lock_time_runs_everywhere : ltac:(statement' elements_tx_lock_time_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ elements_tx_lock_time_local_spec_executable elements_lock_env_rep_constructible). Qed.

Theorem elements_check_lock_height_runs_everywhere :
  ltac:(statement' elements_check_lock_height_local_spec_executable).
Proof. exact (partial_runs_everywhere_intro _ _ _ _ _ elements_check_lock_height_local_spec_executable elements_check_lock_env_rep_constructible). Qed.

Theorem elements_check_lock_time_runs_everywhere :
  ltac:(statement' elements_check_lock_time_local_spec_executable).
Proof. exact (partial_runs_everywhere_intro _ _ _ _ _ elements_check_lock_time_local_spec_executable elements_check_lock_env_rep_constructible). Qed.

Theorem elements_script_cmr_runs_everywhere : ltac:(statement' elements_script_cmr_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ elements_script_cmr_local_spec_executable elements_script_cmr_env_rep_constructible). Qed.

Theorem elements_internal_key_runs_everywhere : ltac:(statement' elements_internal_key_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ elements_internal_key_local_spec_executable elements_internal_key_rep_constructible). Qed.

Theorem elements_tapleaf_version_runs_everywhere :
  ltac:(statement' elements_tapleaf_version_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ elements_tapleaf_version_local_spec_executable elements_tapleaf_version_env_rep_constructible). Qed.

Theorem elements_genesis_block_hash_runs_everywhere :
  ltac:(statement' elements_genesis_block_hash_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ elements_genesis_block_hash_local_spec_executable elements_genesis_hash_env_rep_constructible). Qed.

Theorem elements_transaction_id_runs_everywhere :
  ltac:(statement' elements_transaction_id_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ elements_transaction_id_local_spec_executable elements_txid_rep_constructible). Qed.

Theorem elements_input_sequence_runs_everywhere :
  ltac:(statement' elements_input_sequence_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ elements_input_sequence_local_spec_executable elements_input_sequence_rep_constructible). Qed.

Theorem elements_input_annex_hash_runs_everywhere :
  ltac:(statement' elements_input_annex_hash_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ elements_input_annex_hash_local_spec_executable elements_input_annex_rep_constructible). Qed.

Theorem elements_input_pegin_hash_runs_everywhere :
  ltac:(statement' elements_input_pegin_hash_local_spec_executable).
Proof. exact (sep_runs_everywhere _ _ _ _ _ elements_input_pegin_hash_local_spec_executable elements_input_pegin_rep_constructible). Qed.

(** [tappath]: for every environment whose tap path has at most 128 elements. *)
Theorem elements_tappath_runs_for_bounded_paths :
  forall a (e : Elements.env), (length (tappath (Elements.envTap e)) <= 128)%nat ->
  ltac:(lazymatch type of elements_tappath_local_spec_executable with
        | application_sep_runs_on_fresh_frames ?f _ _ ?A ?B _ ?s =>
            exact (exists m bd bs bw env mf value,
              s a e = Some value /\
              Clight2.eval_funcall elements_ge m (Internal f)
                [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf (Vint Int.one) /\
              frame_output_cells_at mf bw 0 (Z.of_nat (bitSize B)) (encode value))
        end).
Proof.
  intros a e Hl. destruct (elements_tappath_env_rep_constructible e Hl) as (m0 & env & fp & Hr & Hv).
  destruct (elements_tappath_local_spec_executable a e env m0 fp Hr Hv)
    as (m & bd & bs & bw & mf & value & H1 & H2 & H3).
  exists m, bd, bs, bw, env, mf, value. repeat split; assumption.
Qed.
