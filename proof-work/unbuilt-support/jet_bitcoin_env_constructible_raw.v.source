(** Representing memories for the remaining registered Bitcoin application
    relations: the taproot record (script CMR, internal key, leaf version,
    tap path), the transaction id, and the per-input hash and annex arrays
    of the extended environment.  With these, script_cmr and the ten
    raw-environment jets run with no memory, frame or environment premise;
    for raw environments the only requirement left is the one the accepted
    contracts state on the input itself: a tap path of at most 128 elements. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Import Simplicity.Ty Simplicity.Digest Simplicity.BitMachine Simplicity.Translate.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_uint32_array_init C.jet_frame_layout C.jet_input_layout C.jet_write_layout.
Require Import C.jet_output_layout C.jet_encoding.
Require Import C.jet_application_contract C.jet_application_sep C.jet_application_partial.
Require Import C.jet_frame_constructible_app C.jet_env_constructible C.jet_env_constructible_array.
Require Import C.jet_bitcoin_linkage C.jet_bitcoin_env_constructible C.jet_bitcoin_env_constructible_indexed.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_ext_current_spec C.jet_bitcoin_ext_ptr_jets.
Require Import C.jet_bitcoin_indexed_ptr C.jet_bitcoin_current_ptr_jets C.jet_bitcoin_hash_getter_local.
Require Import C.jet_bitcoin_script_cmr_local C.jet_bitcoin_tapleaf_version_local C.jet_bitcoin_tappath_local.
Require Import C.jet_bitcoin_annex_local C.jet_bitcoin_current_annex_local.
Require Import C.jet_bitcoin_raw_env C.jet_bitcoin_raw_jets C.jet_app_executable_registry.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

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

Ltac keepr B :=
  rewrite (proj1 B) by
    (first [left; assumption | left; apply not_eq_sym; assumption
           | right; try change (size_chunk Mptr) with 8; cbn [size_chunk]; lia]).

(** * The taproot record *)
Lemma taproot_built (key cmr : hash256) (path : list hash256) (lenv verv : Z) :
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
  destruct (three_blocks Mem.empty 56 176 (32 * Z.of_nat (length path)))
    as (m & be & bt & bp & Net & Nep & Ntp & Ve & Vt & Vp & Pe & Pt & Pp).
  destruct (built_store_ptr m be 8 bt (Ptrofs.repr 0) 8 16 eq_refl) as (m1 & B1 & L1);
    [intros o Ho; apply Pe; lia|exists 1; reflexivity|lia|lia|].
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
    [rewrite hlen; intros o Ho; apply Pt4; lia|exists 26; reflexivity|].
  rewrite hlen in B5.
  pose proof (built_range_perm _ _ _ _ _ bt 0 176 Cur Writable B5 Pt4) as Pt5.
  pose proof (built_range_perm _ _ _ _ _ bp 0 _ Cur Writable B5 Pp4) as Pp5.
  destruct (built_uint32_array (hash256_reg cmr) m5 bt 136) as (m6 & B6 & L6);
    [rewrite hlen; intros o Ho; apply Pt5; lia|exists 34; reflexivity|].
  rewrite hlen in B6.
  pose proof (built_range_perm _ _ _ _ _ bp 0 _ Cur Writable B6 Pp5) as Pp6.
  destruct (array_buildable hash_elem_rep 32 ltac:(lia) ltac:(exists 4; reflexivity) hash_elem_local
    (elem_buildable_align 4 8 _ _ ltac:(exists 2; reflexivity) hash_elem_buildable) path m6 bp 0 Pp6
    (Z.divide_0_r 8)) as (m7 & B7 & HR).
  exists m7, be, bt, bp.
  split; [repeat match goal with B : built _ _ _ _ _ |- _ => apply (proj1 (proj2 (proj2 B))) end; exact Ve|].
  split; [repeat match goal with B : built _ _ _ _ _ |- _ => apply (proj1 (proj2 (proj2 B))) end; exact Vt|].
  split; [repeat match goal with B : built _ _ _ _ _ |- _ => apply (proj1 (proj2 (proj2 B))) end; exact Vp|].
  split. { keepr B7. keepr B6. keepr B5. keepr B4. keepr B3. keepr B2. exact L1. }
  split. { keepr B7. keepr B6. keepr B5. keepr B4. keepr B3. exact L2. }
  split. { keepr B7. keepr B6. keepr B5. keepr B4. exact L3. }
  split. { keepr B7. keepr B6. keepr B5. exact L4. }
  split.
  { eapply arr_keep; [exact B7|left; exact Ntp|].
    eapply arr_keep; [exact B6|right; left; lia|exact L5]. }
  split; [eapply arr_keep; [exact B7|left; exact Ntp|exact L6]|exact HR].
Qed.

Ltac close HR :=
  rewrite ?ptrofs_max; repeat (first [exact HR | split]);
  first [reflexivity | lia | assumption | exact HR].

Lemma bitcoin_script_cmr_env_rep_constructible (e : Bitcoin.env) :
  exists m env fp, bitcoin_script_cmr_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  destruct (taproot_built (Bitcoin.envScriptCMR e) (Bitcoin.envScriptCMR e) [] 0 0 ltac:(lia) ltac:(lia))
    as (m & be & bt & bp & Ve & Vt & Vp & L1 & L2 & L3 & L4 & L5 & L6 & HR).
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0. close HR. }
  repeat constructor; assumption.
Qed.

Lemma internal_key_rep_constructible (e : ext_environment) :
  exists m env fp, hash_getter_rep extInternalKey 8 104 176 m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  destruct (taproot_built (extInternalKey e) (extInternalKey e) [] 0 0 ltac:(lia) ltac:(lia))
    as (m & be & bt & bp & Ve & Vt & Vp & L1 & L2 & L3 & L4 & L5 & L6 & HR).
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0. close HR. }
  repeat constructor; assumption.
Qed.

Lemma tapleaf_version_rep_constructible (e : ext_environment) :
  exists m env fp, bitcoin_tapleaf_version_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  destruct (taproot_built (extInternalKey e) (extInternalKey e) [] 0 (extTapleafVersion e) ltac:(lia)
    (extTapleafVersion_range e))
    as (m & be & bt & bp & Ve & Vt & Vp & L1 & L2 & L3 & L4 & L5 & L6 & HR).
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0. close HR. }
  repeat constructor; assumption.
Qed.

Lemma tappath_rep_constructible (e : ext_environment) :
  exists m env fp, bitcoin_tappath_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  pose proof (extTappath_len e) as Hl.
  destruct (taproot_built (extInternalKey e) (extInternalKey e) (extTappath e)
    (Z.of_nat (length (extTappath e))) 0 ltac:(lia) ltac:(lia))
    as (m & be & bt & bp & Ve & Vt & Vp & L1 & L2 & L3 & L4 & L5 & L6 & HR).
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0, bp, 0. close HR. }
  repeat constructor; assumption.
Qed.

(** * The transaction id *)
Lemma txid_rep_constructible (e : ext_environment) :
  exists m env fp, hash_getter_rep extTxid 0 400 432 m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  destruct (three_blocks Mem.empty 56 432 0)
    as (m & be & bt & bp & Net & _ & _ & Ve & Vt & _ & Pe & Pt & _).
  destruct (built_store_ptr m be 0 bt (Ptrofs.repr 0) 0 8 eq_refl) as (m1 & B1 & L1);
    [intros o Ho; apply Pe; lia|apply Z.divide_0_r|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 432 Cur Writable B1 Pt) as Pt1.
  destruct (built_uint32_array (hash256_reg (extTxid e)) m1 bt 400) as (m2 & B2 & L2);
    [rewrite hlen; intros o Ho; apply Pt1; lia|exists 100; reflexivity|].
  rewrite hlen in B2.
  exists m2, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0. rewrite ?ptrofs_max. repeat split; try first [reflexivity | lia | assumption].
    keepr B2. exact L1. }
  repeat constructor;
    repeat match goal with B : built _ _ _ _ _ |- _ => apply (proj1 (proj2 (proj2 B))) end; assumption.
Qed.

(** * Per-input arrays of the extended environment *)
Lemma ext_inputs_fit (e : ext_environment) :
  0 <= Z.of_nat (length (sigTxIn (Bitcoin.envTx (extBase e)))) < 4294967296.
Proof.
  pose proof (sigTxInBounds (Bitcoin.envTx (extBase e))) as Hb. rewrite Zlength_correct in Hb.
  change Int.modulus with 4294967296 in Hb. lia.
Qed.

Lemma ext_env_array {X : Type} (e : ext_environment) (xs : list X)
    (R : mem -> block -> Z -> X -> Prop) :
  elem_local R 160 -> elem_buildable 8 R 160 ->
  length xs = length (sigTxIn (Bitcoin.envTx (extBase e))) ->
  exists m be bt bin nI ixv,
    Mem.valid_block m be /\ Mem.valid_block m bt /\ Mem.valid_block m bin /\
    Mem.load Mptr m be 0 = Some (Vptr bt (Ptrofs.repr 0)) /\
    Mem.load Mint64 m be 48 = Some (Vlong ixv) /\
    Mem.load Mptr m bt 0 = Some (Vptr bin (Ptrofs.repr 0)) /\
    Mem.load Mint64 m bt 448 = Some (Vlong nI) /\
    Int64.unsigned nI = Z.of_nat (length xs) /\
    Int64.unsigned ixv = Z.of_nat (ext_ix e) /\
    160 * Z.of_nat (length xs) <= 18446744073709551615 /\
    forall j x, nth_error xs j = Some x -> R m bin (0 + 160 * Z.of_nat j) x.
Proof.
  intros HL HB Hlen. pose proof (ext_inputs_fit e) as Hn. rewrite <- Hlen in Hn.
  pose proof (Bitcoin.envIxBounded (extBase e)) as Hix. rewrite <- Hlen in Hix.
  destruct (env_array_built xs R 56 488 48 160 0 448
    (Int64.repr (Z.of_nat (ext_ix e))) Mem.empty
    ltac:(lia) ltac:(lia) ltac:(divides) ltac:(lia) ltac:(divides) HL HB
    ltac:(lia) ltac:(lia) ltac:(divides) ltac:(lia) ltac:(lia) ltac:(divides) ltac:(left; lia))
    as (m & be & bt & bin & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HR).
  exists m, be, bt, bin, (Int64.repr (Z.of_nat (length xs))), (Int64.repr (Z.of_nat (ext_ix e))).
  repeat (split; [assumption|]).
  split; [apply repr_small; lia|]. split; [apply repr_small; unfold ext_ix; lia|].
  split; [lia|exact HR].
Qed.

Lemma hash_at_local off : 0 <= off -> off + 32 <= 160 ->
  elem_local (fun m b ofs (h : hash256) => hash_elem_rep m b (ofs + off) h) 160.
Proof.
  intros. eapply elem_local_larger; [|apply (elem_local_shift hash_elem_rep 32 off); [lia|exact hash_elem_local]]. lia.
Qed.

Lemma hash_at_buildable off : 0 <= off -> (8 | off) -> off + 32 <= 160 ->
  elem_buildable 8 (fun m b ofs (h : hash256) => hash_elem_rep m b (ofs + off) h) 160.
Proof.
  intros H0 Ha H1. eapply elem_buildable_larger;
    [|apply (elem_buildable_shift 8 hash_elem_rep 32 off H0 Ha);
      eapply elem_buildable_align; [|exact hash_elem_buildable]; divides]. lia.
Qed.

Section ExtHash.
Variables (elems_of : ext_environment -> list hash256) (off : Z).
Hypothesis Hlen : forall e, length (elems_of e) = length (sigTxIn (Bitcoin.envTx (extBase e))).
Hypothesis H0 : 0 <= off.
Hypothesis Ha : (8 | off).
Hypothesis H1 : off + 32 <= 160.

Lemma ext_indexed_hash_rep_constructible (e : ext_environment) :
  exists m env fp, indexed_ptr_rep elems_of hash_elem_rep 160 off 0 448 m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  destruct (ext_env_array e (elems_of e) _ (hash_at_local off H0 H1) (hash_at_buildable off H0 Ha H1)
    (Hlen e)) as (m & be & bt & bin & nI & ixv & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HnI & Hixv & Hs & HR).
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0, bin, 0, nI. close HR. }
  repeat constructor; assumption.
Qed.

Lemma ext_current_hash_rep_constructible (e : ext_environment) :
  exists m env fp, current_ptr_rep elems_of ext_ix hash_elem_rep 160 off 0 448 m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  destruct (ext_env_array e (elems_of e) _ (hash_at_local off H0 H1) (hash_at_buildable off H0 Ha H1)
    (Hlen e)) as (m & be & bt & bin & nI & ixv & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HnI & Hixv & Hs & HR).
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0, bin, 0, nI, ixv. close HR. }
  repeat constructor; assumption.
Qed.
End ExtHash.

Lemma annex_elem_local : elem_local annex_elem_rep 160.
Proof.
  intros m1 m2 b ofs o [Hf Hh] Hl. split.
  - apply (Hl Mint8unsigned (ofs + 152) _); [lia|change (size_chunk Mint8unsigned) with 1; lia|exact Hf].
  - intros h Ho. eapply hash_elem_local; [exact (Hh h Ho)|]. intros c o' v Ha Hb. apply Hl; lia.
Qed.

Lemma annex_elem_buildable : elem_buildable 8 annex_elem_rep 160.
Proof.
  intros o m b ofs HP HA. unfold annex_elem_rep.
  assert (HO : exists m1, built m1 m1 b ofs ofs /\ built m m1 b ofs (ofs + 32) /\
    forall h, o = Some h -> hash_elem_rep m1 b ofs h).
  { destruct o as [h|].
    - destruct (hash_elem_buildable h m b ofs) as (m1 & B1 & L1);
        [intros o' Ho; apply HP; lia|eapply Z.divide_trans; [|exact HA]; divides|].
      exists m1. split; [apply built_refl|]. split; [exact B1|].
      intros h' Hh. inversion Hh; subst h'. exact L1.
    - exists m. split; [apply built_refl|]. split; [apply built_refl|]. intros h Hh. discriminate. }
  destruct HO as (m1 & _ & B1 & L1).
  destruct (built_store_bool m1 b (ofs + 152) (is_some o) (ofs + 152) (ofs + 153)) as (m2 & B2 & L2);
    [eapply built_range_perm; [exact B1|]; intros o' Ho; apply HP; lia|lia|lia|].
  exists m2. split; [|split; [exact L2|]].
  - eapply built_trans; (eapply built_weaken; [| |eassumption]; lia).
  - intros h Hh. eapply hash_elem_local; [exact (L1 h Hh)|].
    intros c o' v Ha Hb Hl. eapply built_load_some; [exact B2| |exact Hl]. right; left. lia.
Qed.

Lemma input_annex_rep_constructible (e : ext_environment) :
  exists m env fp, bitcoin_input_annex_hash_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  destruct (ext_env_array e (extInAnnexHash e) annex_elem_rep annex_elem_local annex_elem_buildable
    (extInAnnexHash_len e))
    as (m & be & bt & bin & nI & ixv & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HnI & Hixv & Hs & HR).
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0, bin, 0, nI. close HR. }
  repeat constructor; assumption.
Qed.

Lemma current_annex_rep_constructible (e : ext_environment) :
  exists m env fp, bitcoin_current_annex_hash_env_rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp.
Proof.
  destruct (ext_env_array e (extInAnnexHash e) annex_elem_rep annex_elem_local annex_elem_buildable
    (extInAnnexHash_len e))
    as (m & be & bt & bin & nI & ixv & Ve & Vt & Vi & L1 & L2 & L3 & L4 & HnI & Hixv & Hs & HR).
  exists m, (Vptr be (Ptrofs.repr 0)). eexists. split.
  { exists be, 0, bt, 0, bin, 0, nI, ixv. close HR. }
  repeat constructor; assumption.
Qed.

(** * No-premise statements *)

Theorem bitcoin_script_cmr_runs_everywhere : ltac:(statement bitcoin_script_cmr_local_spec_executable).
Proof.
  exact (sep_runs_everywhere _ _ _ _ _ bitcoin_script_cmr_local_spec_executable
    bitcoin_script_cmr_env_rep_constructible).
Qed.

(** Raw environments: the tap path bound is the input requirement of the
    accepted raw contracts (the C leaf record stores the path length in one
    byte); nothing else is assumed. *)
Definition raw_runs_everywhere (f : function) (A B : Ty)
    (spec : A -> raw_bitcoin_environment -> option B) : Prop :=
  forall (a : A) (logical : raw_bitcoin_environment),
  (length (raw_tap_path logical) <= 128)%nat ->
  exists m bd bs bw env mf value,
    spec a logical = Some value /\
    Clight2.eval_funcall bitcoin_ge m (Internal f)
      [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw 0 (Z.of_nat (bitSize B)) (encode value).

Lemma raw_sep_runs_everywhere f A B rep spec :
  application_sep_runs_on_fresh_frames f bitcoin_ge raw_bitcoin_environment A B (raw_env_rep rep) spec ->
  (forall e : ext_environment, exists m env fp, rep m env e fp /\
    Forall (fun '(b, _, _) => Mem.valid_block m b) fp) ->
  raw_runs_everywhere f A B spec.
Proof.
  intros HRun HRep a logical Hpath.
  destruct (HRep (project_raw_environment logical Hpath)) as (m0 & env & fp & Hr & Hv).
  destruct (HRun a logical env m0 fp (ex_intro _ Hpath Hr) Hv)
    as (m & bd & bs & bw & mf & value & H1 & H2 & H3).
  exists m, bd, bs, bw, env, mf, value. repeat split; assumption.
Qed.

Ltac raw_statement H :=
  lazymatch type of H with
  | application_sep_runs_on_fresh_frames ?f _ _ ?A ?B _ ?s => exact (raw_runs_everywhere f A B s)
  end.

Theorem bitcoin_transaction_id_raw_runs_everywhere :
  ltac:(raw_statement bitcoin_transaction_id_raw_local_spec_executable).
Proof. exact (raw_sep_runs_everywhere _ _ _ _ _ bitcoin_transaction_id_raw_local_spec_executable txid_rep_constructible). Qed.

Theorem bitcoin_internal_key_raw_runs_everywhere :
  ltac:(raw_statement bitcoin_internal_key_raw_local_spec_executable).
Proof. exact (raw_sep_runs_everywhere _ _ _ _ _ bitcoin_internal_key_raw_local_spec_executable internal_key_rep_constructible). Qed.

Theorem bitcoin_tapleaf_version_raw_runs_everywhere :
  ltac:(raw_statement bitcoin_tapleaf_version_raw_local_spec_executable).
Proof. exact (raw_sep_runs_everywhere _ _ _ _ _ bitcoin_tapleaf_version_raw_local_spec_executable tapleaf_version_rep_constructible). Qed.

Theorem bitcoin_tappath_raw_runs_everywhere :
  ltac:(raw_statement bitcoin_tappath_raw_local_spec_executable).
Proof. exact (raw_sep_runs_everywhere _ _ _ _ _ bitcoin_tappath_raw_local_spec_executable tappath_rep_constructible). Qed.

Theorem bitcoin_input_script_hash_raw_runs_everywhere :
  ltac:(raw_statement bitcoin_input_script_hash_raw_local_spec_executable).
Proof.
  exact (raw_sep_runs_everywhere _ _ _ _ _ bitcoin_input_script_hash_raw_local_spec_executable
    (ext_indexed_hash_rep_constructible extInScriptHash 112 extInScriptHash_len ltac:(lia) ltac:(divides) ltac:(lia))).
Qed.

Theorem bitcoin_input_script_sig_hash_raw_runs_everywhere :
  ltac:(raw_statement bitcoin_input_script_sig_hash_raw_local_spec_executable).
Proof.
  exact (raw_sep_runs_everywhere _ _ _ _ _ bitcoin_input_script_sig_hash_raw_local_spec_executable
    (ext_indexed_hash_rep_constructible extInScriptSigHash 32 extInScriptSigHash_len ltac:(lia) ltac:(divides) ltac:(lia))).
Qed.

Theorem bitcoin_current_script_hash_raw_runs_everywhere :
  ltac:(raw_statement bitcoin_current_script_hash_raw_local_spec_executable).
Proof.
  exact (raw_sep_runs_everywhere _ _ _ _ _ bitcoin_current_script_hash_raw_local_spec_executable
    (ext_current_hash_rep_constructible extInScriptHash 112 extInScriptHash_len ltac:(lia) ltac:(divides) ltac:(lia))).
Qed.

Theorem bitcoin_current_script_sig_hash_raw_runs_everywhere :
  ltac:(raw_statement bitcoin_current_script_sig_hash_raw_local_spec_executable).
Proof.
  exact (raw_sep_runs_everywhere _ _ _ _ _ bitcoin_current_script_sig_hash_raw_local_spec_executable
    (ext_current_hash_rep_constructible extInScriptSigHash 32 extInScriptSigHash_len ltac:(lia) ltac:(divides) ltac:(lia))).
Qed.

Theorem bitcoin_input_annex_hash_raw_runs_everywhere :
  ltac:(raw_statement bitcoin_input_annex_hash_raw_local_spec_executable).
Proof. exact (raw_sep_runs_everywhere _ _ _ _ _ bitcoin_input_annex_hash_raw_local_spec_executable input_annex_rep_constructible). Qed.

Theorem bitcoin_current_annex_hash_raw_runs_everywhere :
  ltac:(raw_statement bitcoin_current_annex_hash_raw_local_spec_executable).
Proof. exact (raw_sep_runs_everywhere _ _ _ _ _ bitcoin_current_annex_hash_raw_local_spec_executable current_annex_rep_constructible). Qed.
