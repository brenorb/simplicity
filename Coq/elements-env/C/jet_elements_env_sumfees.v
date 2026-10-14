(** Execution of [sumFees(feeOutputs, numFees)] (elements/env.c): the tally
    of a sorted array of pointers to fee outputs.  Outputs with the same
    asset are adjacent; the first of each bunch stays in the array (compacted
    to the front) and its [assetFee] accumulates the explicit amounts of the
    bunch.  The C loop is related step by step to a functional model
    ([sf_step]) on the pair (array of output indices, fee of each output).

    The call of the external [memcmp] is covered by the explicit premise
    [memcmp_model] (C/jet_memcmp_model.v).  The array must be sorted for the
    byte order of the asset midstates ([Hsorted]): this is the precondition
    the C code states and checks with [simplicity_assert]; the failing branch
    of that assertion is never taken. *)
From Coq Require Import ZArith List Lia PeanoNat Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcmp_model C.jet_memcmp_words.
Require Import C.jets_sha C.jet_sha_linkage.
Require Import C.jet_elements_env_field_eval C.jet_elements_env_copyrawamt C.jet_elements_env_copyrawconf.
Require Import C.jet_elements_env_countfee.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Local Notation SOUT := (Tstruct _sigOutput noattr).
Local Notation PSOUT := (tptr (Tstruct _sigOutput noattr)).
Local Notation PP := (tptr (tptr (Tstruct _sigOutput noattr))).
Local Notation CONF := (Tstruct _confidential noattr).
Local Notation CAMT := (Tstruct _confAmount noattr).
Local Notation SMID := (Tstruct _sha256_midstate noattr).
Local Notation SA8 := (tarray tuint 8).
Local Notation amt_union := (18727075383868559167%positive) (only parsing).

Lemma sha_memcmp_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _memcmp = Some (sha_symbol_block _memcmp).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_memcmp_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _memcmp) Ptrofs.zero) =
    Some (External (EF_external "memcmp" memcmp_sig)
      (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) tint cc_default).
Proof. vm_compute; reflexivity. Qed.

Lemma envu_sigOutput_asset : envu_field_at _sigOutput _asset 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sigOutput_amt : envu_field_at _sigOutput _amt 104.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sigOutput_assetFee : envu_field_at _sigOutput _assetFee 216.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.

Definition sf_s1 : statement :=
  ltac:(let b := eval cbv delta [f_sumFees fn_body] beta iota in (fn_body f_sumFees) in
        lazymatch b with
        | Ssequence _ (Ssequence _ (Ssequence (Ssequence _ (Sloop ?s1 _)) _)) => exact s1
        end).
Definition sf_s2 : statement :=
  ltac:(let b := eval cbv delta [f_sumFees fn_body] beta iota in (fn_body f_sumFees) in
        lazymatch b with
        | Ssequence _ (Ssequence _ (Ssequence (Ssequence _ (Sloop _ ?s2)) _)) => exact s2
        end).
Definition sf_cmp : statement :=
  ltac:(let b := eval cbv delta [sf_s1] beta iota in sf_s1 in
        lazymatch b with Ssequence _ (Ssequence ?c _) => exact c end).
Definition sf_assert : statement :=
  ltac:(let b := eval cbv delta [sf_s1] beta iota in sf_s1 in
        lazymatch b with Ssequence _ (Ssequence _ (Ssequence ?c _)) => exact c end).
Definition sf_bump : statement :=
  ltac:(let b := eval cbv delta [sf_s1] beta iota in sf_s1 in
        lazymatch b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?c _))) => exact c end).
Definition sf_add : statement :=
  ltac:(let b := eval cbv delta [sf_s1] beta iota in sf_s1 in
        lazymatch b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ ?c))) => exact c end).

Lemma sf_s1_shape :
  sf_s1 = Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _numFees tulong) tint) Sskip Sbreak)
    (Ssequence sf_cmp (Ssequence sf_assert (Ssequence sf_bump sf_add))).
Proof. reflexivity. Qed.

Lemma sf_body_shape :
  fn_body f_sumFees =
    Ssequence (Sset _result (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _numFees tulong) (Econst_int (Int.repr 1) tint) tint)
           (Sreturn (Some (Etempvar _result tulong))) Sskip)
        (Ssequence
          (Ssequence (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong)) (Sloop sf_s1 sf_s2))
          (Sreturn (Some (Ebinop Oadd (Etempvar _result tulong) (Econst_int (Int.repr 1) tint) tulong))))).
Proof. reflexivity. Qed.

Local Opaque sha_ge.

Definition upd {A} (f : nat -> A) (k : nat) (v : A) : nat -> A :=
  fun j => if Nat.eqb j k then v else f j.

Lemma upd_same {A} (f : nat -> A) k v : upd f k v k = v.
Proof. unfold upd. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma upd_other {A} (f : nat -> A) k v j : j <> k -> upd f k v j = f j.
Proof. intros H. unfold upd. destruct (Nat.eqb_spec j k); [contradiction|reflexivity]. Qed.

Lemma sf_i64_add a b : Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof.
  unfold Int64.add. apply Int64.eqm_samerepr.
  apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma sf_add0 (o : ptrofs) : Ptrofs.add o (Ptrofs.repr 0) = o.
Proof. change (Ptrofs.repr 0) with Ptrofs.zero. apply Ptrofs.add_zero. Qed.

Section SumFees.
Variable Hmodel : memcmp_model.
Variables (bF : block) (oF N : Z).
Variables (pb : nat -> block) (po : nat -> Z) (W : nat -> list int) (E : nat -> int64).
Hypothesis HN : 1 <= N <= 4294967295.
Hypothesis HoF : 0 <= oF /\ oF + 8 * N <= Ptrofs.max_unsigned.

Let Nn : nat := Z.to_nat N.
Let arrv := Vptr bF (Ptrofs.repr oF).

Hypothesis Hpo : forall j, (j < Nn)%nat -> 0 <= po j /\ po j + 248 <= Ptrofs.max_unsigned.
Hypothesis HsepF : forall j, (j < Nn)%nat -> pb j <> bF.
Hypothesis Hsep : forall j k, (j < Nn)%nat -> (k < Nn)%nat -> j <> k ->
  pb j <> pb k \/ po j + 248 <= po k \/ po k + 248 <= po j.
Hypothesis HWlen : forall j, (j < Nn)%nat -> length (W j) = 8%nat.

Definition sf_A (j : nat) : list int := words_bytes (W j).

Hypothesis Hsorted : forall i j, (i <= j)%nat -> (j < Nn)%nat -> bytes_cmp (sf_A j) (sf_A i) <> Lt.

Lemma sf_Nn : Z.of_nat Nn = N.
Proof. unfold Nn. apply Z2Nat.id. lia. Qed.

(** The functional model. *)
Record sf_st : Type := { sf_r : nat; sf_arr : nat -> nat; sf_fee : nat -> int64 }.

Definition sf_step (i : nat) (st : sf_st) : sf_st :=
  let ai := sf_arr st i in
  match bytes_cmp (sf_A ai) (sf_A (sf_arr st (sf_r st))) with
  | Gt => {| sf_r := S (sf_r st); sf_arr := upd (sf_arr st) (S (sf_r st)) ai;
             sf_fee := upd (sf_fee st) ai (Int64.add (sf_fee st ai) (E ai)) |}
  | _ => {| sf_r := sf_r st; sf_arr := sf_arr st;
            sf_fee := upd (sf_fee st) (sf_arr st (sf_r st))
                        (Int64.add (sf_fee st (sf_arr st (sf_r st))) (E ai)) |}
  end.

Fixpoint sf_iter (k : nat) (st : sf_st) : sf_st :=
  match k with
  | O => st
  | S k' => sf_step k' (sf_iter k' st)
  end.

Definition sf_init (fee0 : nat -> int64) : sf_st := {| sf_r := 0; sf_arr := fun j => j; sf_fee := fee0 |}.

(** Index facts kept by the model. *)
Definition sf_pure (k : nat) (st : sf_st) : Prop :=
  (sf_r st < Nat.max k 1)%nat /\
  (forall s, (sf_r st < s)%nat -> sf_arr st s = s) /\
  (forall s, (s <= sf_r st)%nat -> (sf_arr st s < Nat.max k 1)%nat).

Lemma sf_pure_init fee0 : sf_pure 0 (sf_init fee0).
Proof. unfold sf_pure, sf_init; cbn. repeat split; intros; lia. Qed.

Lemma sf_pure_cmp k st : sf_pure k st -> (k < Nn)%nat ->
  bytes_cmp (sf_A (sf_arr st k)) (sf_A (sf_arr st (sf_r st))) <> Lt /\
  (bytes_cmp (sf_A (sf_arr st k)) (sf_A (sf_arr st (sf_r st))) = Gt -> (sf_r st < k)%nat /\ sf_arr st k = k).
Proof.
  intros (P1 & P2 & P3) Hk.
  destruct (lt_dec (sf_r st) k) as [Hlt|Hge].
  - rewrite (P2 k Hlt). pose proof (P3 (sf_r st) ltac:(lia)) as H3. split.
    + apply Hsorted; lia.
    + intros _. split; [exact Hlt|reflexivity].
  - assert (HE : sf_r st = k) by lia. rewrite HE. rewrite bytes_cmp_refl. split; [discriminate|discriminate].
Qed.

Lemma sf_pure_step k st : sf_pure k st -> (k < Nn)%nat -> sf_pure (S k) (sf_step k st).
Proof.
  intros HP Hk. destruct (sf_pure_cmp k st HP Hk) as [_ HG]. destruct HP as (P1 & P2 & P3).
  unfold sf_step.
  destruct (bytes_cmp (sf_A (sf_arr st k)) (sf_A (sf_arr st (sf_r st)))) eqn:EC.
  - unfold sf_pure; cbn. repeat split; [lia|exact P2|intros s Hs; pose proof (P3 s Hs); lia].
  - unfold sf_pure; cbn. repeat split; [lia|exact P2|intros s Hs; pose proof (P3 s Hs); lia].
  - destruct (HG eq_refl) as [Hlt Hak]. rewrite Hak.
    unfold sf_pure; cbn. repeat split.
    + lia.
    + intros s Hs. rewrite upd_other by lia. apply P2. lia.
    + intros s Hs. destruct (Nat.eq_dec s (S (sf_r st))) as [->|Hne].
      * rewrite upd_same. lia.
      * rewrite upd_other by exact Hne. pose proof (P3 s ltac:(lia)). lia.
Qed.

Lemma sf_pure_iter fee0 k : (k <= Nn)%nat -> sf_pure k (sf_iter k (sf_init fee0)).
Proof.
  induction k as [|k IH]; intros Hk; [apply sf_pure_init|].
  cbn [sf_iter]. apply sf_pure_step; [apply IH; lia|lia].
Qed.

(** The memory: the pointer array, the fees, and what never changes. *)
Definition sf_static (m : mem) : Prop :=
  (forall j, (j < Nn)%nat -> forall i x, nth_error (W j) i = Some x ->
     Mem.load Mint32 m (pb j) (po j + 4 * Z.of_nat i) = Some (Vint x)) /\
  (forall j, (j < Nn)%nat -> Mem.load Mint64 m (pb j) (po j + 104) = Some (Vlong (E j))) /\
  (forall j, (j < Nn)%nat -> Mem.valid_access m Mint64 (pb j) (po j + 216) Writable) /\
  (forall s, (s < Nn)%nat -> Mem.valid_access m Mptr bF (oF + 8 * Z.of_nat s) Writable).

Definition sf_mem (m : mem) (arr : nat -> nat) (fee : nat -> int64) : Prop :=
  (forall s, (s < Nn)%nat ->
     Mem.load Mptr m bF (oF + 8 * Z.of_nat s) = Some (Vptr (pb (arr s)) (Ptrofs.repr (po (arr s))))) /\
  (forall j, (j < Nn)%nat -> Mem.load Mint64 m (pb j) (po j + 216) = Some (Vlong (fee j))) /\
  sf_static m.

(** Locations the function never writes. *)
Definition sf_outside (ch : memory_chunk) (b : block) (ofs : Z) : Prop :=
  (b <> bF \/ ofs + size_chunk ch <= oF \/ oF + 8 * N <= ofs) /\
  (forall j, (j < Nn)%nat -> b <> pb j \/ ofs + size_chunk ch <= po j + 216 \/ po j + 224 <= ofs).

Definition sf_frame (m0 m : mem) : Prop :=
  (forall ch b ofs, sf_outside ch b ofs -> Mem.load ch m b ofs = Mem.load ch m0 b ofs) /\
  (forall b ofs k p, Mem.perm m b ofs k p <-> Mem.perm m0 b ofs k p) /\
  Mem.nextblock m = Mem.nextblock m0.

Lemma sf_frame_refl m : sf_frame m m.
Proof. repeat split; auto. Qed.

Lemma sf_static_store m ch b ofs v m' :
  Mem.store ch m b ofs v = Some m' -> sf_static m ->
  ((b = bF /\ exists s, (s < Nn)%nat /\ ofs = oF + 8 * Z.of_nat s /\ ch = Mptr) \/
   (exists j, (j < Nn)%nat /\ b = pb j /\ ofs = po j + 216 /\ ch = Mint64)) ->
  sf_static m'.
Proof.
  intros HS (HW & HE & HVf & HVs) Hwhere.
  assert (HO : forall j, (j < Nn)%nat -> forall ch' o', po j <= o' -> o' + size_chunk ch' <= po j + 216 ->
    Mem.load ch' m' (pb j) o' = Mem.load ch' m (pb j) o').
  { intros j Hj ch' o' Hlo Hhi. eapply Mem.load_store_other; [exact HS|].
    destruct Hwhere as [(-> & _)|(j0 & Hj0 & -> & -> & ->)].
    - left. apply HsepF. exact Hj.
    - destruct (Nat.eq_dec j j0) as [->|Hne].
      + right. left. exact Hhi.
      + destruct (Hsep j j0 Hj Hj0 Hne) as [H|[H|H]]; [left; exact H|right; left; lia|right; right; change (size_chunk Mint64) with 8; lia]. }
  split; [|split; [|split]].
  - intros j Hj i x Hi.
    assert (Hi8 : (i < 8)%nat) by (rewrite <- (HWlen j Hj); apply nth_error_Some; rewrite Hi; discriminate).
    rewrite HO by (try exact Hj; change (size_chunk Mint32) with 4; lia). exact (HW j Hj i x Hi).
  - intros j Hj. rewrite HO by (try exact Hj; change (size_chunk Mint64) with 8; lia). exact (HE j Hj).
  - intros j Hj. eapply Mem.store_valid_access_1; [exact HS|exact (HVf j Hj)].
  - intros s Hs. eapply Mem.store_valid_access_1; [exact HS|exact (HVs s Hs)].
Qed.

Lemma sf_frame_store m0 m ch b ofs v m' :
  Mem.store ch m b ofs v = Some m' -> sf_frame m0 m ->
  ((b = bF /\ exists s, (s < Nn)%nat /\ ofs = oF + 8 * Z.of_nat s /\ ch = Mptr) \/
   (exists j, (j < Nn)%nat /\ b = pb j /\ ofs = po j + 216 /\ ch = Mint64)) ->
  sf_frame m0 m'.
Proof.
  intros HS (HL & HP & HNb) Hwhere. pose proof sf_Nn as HNn. split; [|split].
  - intros ch' b' o' (Out1 & Out2). rewrite <- (HL ch' b' o' (conj Out1 Out2)).
    eapply Mem.load_store_other; [exact HS|].
    destruct Hwhere as [(-> & s & Hs & -> & ->)|(j0 & Hj0 & -> & -> & ->)].
    + destruct Out1 as [H|[H|H]]; [left; exact H|right; left; lia|right; right; change (size_chunk Mptr) with 8; lia].
    + destruct (Out2 j0 Hj0) as [H|[H|H]]; [left; exact H|right; left; exact H|right; right; change (size_chunk Mint64) with 8; lia].
  - intros b' o' k p. rewrite <- HP. split; intros H.
    + eapply Mem.perm_store_2; [exact HS|exact H].
    + eapply Mem.perm_store_1; [exact HS|exact H].
  - rewrite (Mem.nextblock_store _ _ _ _ _ _ HS). exact HNb.
Qed.

(** [feeOutputs[s] = feeOutputs[..]] *)
Lemma sf_mem_slot m arr fee s0 j0 :
  sf_mem m arr fee -> (s0 < Nn)%nat -> (j0 < Nn)%nat ->
  exists m',
    Mem.store Mptr m bF (oF + 8 * Z.of_nat s0) (Vptr (pb j0) (Ptrofs.repr (po j0))) = Some m' /\
    sf_mem m' (upd arr s0 j0) fee /\ (forall m0, sf_frame m0 m -> sf_frame m0 m').
Proof.
  intros (HSl & HFe & HSt) Hs0 Hj0. pose proof HSt as (_ & _ & _ & HVs).
  destruct (Mem.valid_access_store m Mptr bF (oF + 8 * Z.of_nat s0) (Vptr (pb j0) (Ptrofs.repr (po j0)))
    (HVs s0 Hs0)) as [m' HS].
  assert (Hwhere : (bF = bF /\ exists s, (s < Nn)%nat /\ oF + 8 * Z.of_nat s0 = oF + 8 * Z.of_nat s /\ Mptr = Mptr) \/
    (exists j, (j < Nn)%nat /\ bF = pb j /\ oF + 8 * Z.of_nat s0 = po j + 216 /\ Mptr = Mint64)).
  { left. split; [reflexivity|]. exists s0. repeat split; assumption. }
  exists m'. split; [exact HS|]. split; [|intros m0 HF; exact (sf_frame_store _ _ _ _ _ _ _ HS HF Hwhere)].
  split; [|split; [|exact (sf_static_store _ _ _ _ _ _ HS HSt Hwhere)]].
  - intros s Hs. destruct (Nat.eq_dec s s0) as [->|Hne].
    + rewrite upd_same. rewrite (Mem.load_store_same _ _ _ _ _ _ HS). reflexivity.
    + rewrite upd_other by exact Hne.
      rewrite (Mem.load_store_other _ _ _ _ _ _ HS) by (right; change (size_chunk Mptr) with 8; lia).
      exact (HSl s Hs).
  - intros j Hj. rewrite (Mem.load_store_other _ _ _ _ _ _ HS) by (left; apply HsepF; exact Hj).
    exact (HFe j Hj).
Qed.

(** [feeOutputs[..]->assetFee = v] *)
Lemma sf_mem_fee m arr fee j0 v :
  sf_mem m arr fee -> (j0 < Nn)%nat ->
  exists m',
    Mem.store Mint64 m (pb j0) (po j0 + 216) (Vlong v) = Some m' /\
    sf_mem m' arr (upd fee j0 v) /\ (forall m0, sf_frame m0 m -> sf_frame m0 m').
Proof.
  intros (HSl & HFe & HSt) Hj0. pose proof HSt as (_ & _ & HVf & _).
  destruct (Mem.valid_access_store m Mint64 (pb j0) (po j0 + 216) (Vlong v) (HVf j0 Hj0)) as [m' HS].
  assert (Hwhere : (pb j0 = bF /\ exists s, (s < Nn)%nat /\ po j0 + 216 = oF + 8 * Z.of_nat s /\ Mint64 = Mptr) \/
    (exists j, (j < Nn)%nat /\ pb j0 = pb j /\ po j0 + 216 = po j + 216 /\ Mint64 = Mint64)).
  { right. exists j0. repeat split; assumption. }
  exists m'. split; [exact HS|]. split; [|intros m0 HF; exact (sf_frame_store _ _ _ _ _ _ _ HS HF Hwhere)].
  split; [|split; [|exact (sf_static_store _ _ _ _ _ _ HS HSt Hwhere)]].
  - intros s Hs. rewrite (Mem.load_store_other _ _ _ _ _ _ HS)
      by (left; apply not_eq_sym, HsepF; exact Hj0). exact (HSl s Hs).
  - intros j Hj. destruct (Nat.eq_dec j j0) as [->|Hne].
    + rewrite upd_same. rewrite (Mem.load_store_same _ _ _ _ _ _ HS). reflexivity.
    + rewrite upd_other by exact Hne.
      rewrite (Mem.load_store_other _ _ _ _ _ _ HS); [exact (HFe j Hj)|].
      destruct (Hsep j j0 Hj Hj0 Hne) as [H|[H|H]];
        [left; exact H|right; left; change (size_chunk Mint64) with 8; lia
        |right; right; change (size_chunk Mint64) with 8; lia].
Qed.

(** Expressions. *)
Definition sf_le (le : temp_env) (k r : nat) : Prop :=
  le!_i = Some (Vlong (Int64.repr (Z.of_nat k))) /\
  le!_result = Some (Vlong (Int64.repr (Z.of_nat r))) /\
  le!_feeOutputs = Some arrv /\ le!_numFees = Some (Vlong (Int64.repr N)).

Lemma sf_slot_lvalue le m id s :
  le!_feeOutputs = Some arrv -> le!id = Some (Vlong (Int64.repr (Z.of_nat s))) -> (s < Nn)%nat ->
  eval_lvalue sha_ge empty_env le m
    (Ederef (Ebinop Oadd (Etempvar _feeOutputs PP) (Etempvar id tulong) PP) PSOUT)
    bF (Ptrofs.repr (oF + 8 * Z.of_nat s)) Full.
Proof.
  intros HF Hid Hs. pose proof sf_Nn as HNn.
  apply eval_Ederef. eapply eval_Ebinop; [apply eval_Etempvar; exact HF|apply eval_Etempvar; exact Hid|].
  rewrite <- (cf_ptr_index oF 8 (Z.of_nat s))
    by (change Ptrofs.max_unsigned with 18446744073709551615 in *; lia).
  reflexivity.
Qed.

Lemma sf_slot_value le m id s v :
  le!_feeOutputs = Some arrv -> le!id = Some (Vlong (Int64.repr (Z.of_nat s))) -> (s < Nn)%nat ->
  Mem.load Mptr m bF (oF + 8 * Z.of_nat s) = Some v ->
  eval_expr sha_ge empty_env le m
    (Ederef (Ebinop Oadd (Etempvar _feeOutputs PP) (Etempvar id tulong) PP) PSOUT) v.
Proof.
  intros HF Hid Hs HL. pose proof sf_Nn as HNn.
  eapply eval_Elvalue; [apply sf_slot_lvalue; eassumption|].
  eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv.
  rewrite Ptrofs.unsigned_repr by lia. exact HL.
Qed.

Lemma sf_asset_value le m t b o :
  le!t = Some (Vptr b (Ptrofs.repr o)) ->
  eval_expr sha_ge empty_env le m
    (Efield (Ederef (Etempvar t PSOUT) SOUT) _asset CONF) (Vptr b (Ptrofs.repr o)).
Proof.
  intros Ht. rewrite <- (sf_add0 (Ptrofs.repr o)).
  eapply eval_envu_field_struct;
    [reflexivity|exact envu_sigOutput_asset|apply eval_envu_deref_struct; exact Ht].
Qed.

Lemma sf_asset_data_value le m t b o :
  le!t = Some (Vptr b (Ptrofs.repr o)) ->
  eval_expr sha_ge empty_env le m
    (Efield (Efield (Ederef (Etempvar t PSOUT) SOUT) _asset CONF) _data SMID) (Vptr b (Ptrofs.repr o)).
Proof.
  intros Ht. rewrite <- (sf_add0 (Ptrofs.repr o)).
  eapply eval_envu_field_struct;
    [reflexivity|exact envu_confidential_data|apply sf_asset_value; exact Ht].
Qed.

Lemma sf_asset_s_value le m t b o :
  le!t = Some (Vptr b (Ptrofs.repr o)) ->
  eval_expr sha_ge empty_env le m
    (Efield (Efield (Efield (Ederef (Etempvar t PSOUT) SOUT) _asset CONF) _data SMID) _s SA8)
    (Vptr b (Ptrofs.repr o)).
Proof.
  intros Ht. rewrite <- (sf_add0 (Ptrofs.repr o)).
  eapply eval_envu_field_array;
    [reflexivity|exact envu_sha256_midstate_s|intros ch; discriminate|reflexivity
    |apply sf_asset_data_value; exact Ht].
Qed.

Lemma sf_fee_lvalue le m t b o :
  le!t = Some (Vptr b (Ptrofs.repr o)) -> 0 <= o -> o + 248 <= Ptrofs.max_unsigned ->
  eval_lvalue sha_ge empty_env le m
    (Efield (Ederef (Etempvar t PSOUT) SOUT) _assetFee tulong) b (Ptrofs.repr (o + 216)) Full.
Proof.
  intros Ht Ho0 HoM. rewrite <- (envu_ptr_add_repr o 216) by lia.
  eapply eval_envu_field_lvalue;
    [reflexivity|exact envu_sigOutput_assetFee|apply eval_envu_deref_struct; exact Ht].
Qed.

Lemma sf_explicit_value le m t b o v :
  le!t = Some (Vptr b (Ptrofs.repr o)) -> 0 <= o -> o + 248 <= Ptrofs.max_unsigned ->
  Mem.load Mint64 m b (o + 104) = Some v ->
  eval_expr sha_ge empty_env le m
    (Efield (Efield (Efield (Ederef (Etempvar t PSOUT) SOUT) _amt CAMT) amt_union (Tunion __4799 noattr))
       _explicit tulong) v.
Proof.
  intros Ht Ho0 HoM HL.
  eapply eval_Elvalue.
  - eapply eval_envu_union_lvalue; [reflexivity|exact envu_amt_explicit|].
    eapply eval_Elvalue; [|apply deref_loc_copy; reflexivity].
    eapply eval_envu_field_lvalue; [reflexivity|exact envu_confAmount_union|].
    eapply eval_envu_field_struct;
      [reflexivity|exact envu_sigOutput_amt|apply eval_envu_deref_struct; exact Ht].
  - eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv.
    rewrite !sf_add0, envu_ptr_add_repr by lia. rewrite Ptrofs.unsigned_repr by lia. exact HL.
Qed.

Lemma sf_le_set le k r id v :
  id <> _i -> id <> _result -> id <> _feeOutputs -> id <> _numFees ->
  sf_le le k r -> sf_le (PTree.set id v le) k r.
Proof.
  intros N1 N2 N3 N4 (H1 & H2 & H3 & H4). unfold sf_le.
  rewrite !PTree.gso by (apply not_eq_sym; assumption). repeat split; assumption.
Qed.
(** The comparison: memory unchanged, [_cmp] holds the result of [memcmp]. *)
Lemma sf_cmp_exec le m arr fee k r :
  sf_le le k r -> sf_mem m arr fee -> (k < Nn)%nat -> (r < Nn)%nat ->
  (arr k < Nn)%nat -> (arr r < Nn)%nat ->
  exists rv le',
    Clight2.exec_stmt sha_ge empty_env le m sf_cmp E0 le' m Out_normal /\
    sf_le le' k r /\ le'!_cmp = Some (Vint rv) /\
    memcmp_sign (bytes_cmp (sf_A (arr k)) (sf_A (arr r))) rv.
Proof.
  intros HLe (HSl & HFe & (HW & HEx & HVf & HVs)) Hk Hr Hak Har. pose proof HLe as (Hi & Hres & HF & HNf).
  set (ai := arr k) in *. set (aq := arr r) in *.
  destruct (Hpo ai Hak) as [Hpi0 HpiM]. destruct (Hpo aq Har) as [Hpq0 HpqM].
  assert (HLa : length (sf_A ai) = 32%nat) by (unfold sf_A; rewrite words_bytes_length, (HWlen ai Hak); reflexivity).
  assert (HLq : length (sf_A aq) = 32%nat) by (unfold sf_A; rewrite words_bytes_length, (HWlen aq Har); reflexivity).
  destruct (Hmodel (Clight.genv_genv sha_ge) m (pb ai) (Ptrofs.repr (po ai)) (pb aq) (Ptrofs.repr (po aq))
    (sf_A ai) (sf_A aq)) as (rv & HX & HSg).
  { rewrite HLa, HLq. reflexivity. }
  { rewrite HLa. change (Z.of_nat 32) with 32. change Int64.max_unsigned with 18446744073709551615. lia. }
  { rewrite HLa, Ptrofs.unsigned_repr by lia. change (Z.of_nat 32) with 32. lia. }
  { rewrite HLa, Ptrofs.unsigned_repr by lia. change (Z.of_nat 32) with 32. lia. }
  { rewrite Ptrofs.unsigned_repr by lia. apply words_bytes_at. exact (HW ai Hak). }
  { rewrite Ptrofs.unsigned_repr by lia. apply words_bytes_at. exact (HW aq Har). }
  rewrite HLa in HX. change (Z.of_nat 32) with 32 in HX.
  set (le8 := PTree.set _t'8 (Vptr (pb ai) (Ptrofs.repr (po ai))) le).
  set (le9 := PTree.set _t'9 (Vptr (pb aq) (Ptrofs.repr (po aq))) le8).
  set (le1 := PTree.set _t'1 (Vint rv) le9).
  exists rv, (PTree.set _cmp (Vint rv) le1). split; [|split; [|split; [apply PTree.gss|exact HSg]]].
  - cbv delta [sf_cmp] beta iota.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le8) (m1 := m).
      { apply exec_Sset. apply sf_slot_value with (s := k); [exact HF|exact Hi|exact Hk|exact (HSl k Hk)]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le9) (m1 := m).
      { apply exec_Sset. apply sf_slot_value with (s := r);
          [unfold le8; rewrite PTree.gso by discriminate; exact HF
          |unfold le8; rewrite PTree.gso by discriminate; exact Hres|exact Hr|exact (HSl r Hr)]. }
      change le1 with (set_opttemp (Some _t'1) (Vint rv) le9).
      eapply exec_Scall with (vf := Vptr (sha_symbol_block _memcmp) Ptrofs.zero)
        (vargs := [Vptr (pb ai) (Ptrofs.repr (po ai)); Vptr (pb aq) (Ptrofs.repr (po aq)); Vlong (Int64.repr 32)]).
      * reflexivity.
      * eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_memcmp_symbol]|].
        apply deref_loc_reference; reflexivity.
      * eapply eval_Econs;
          [apply sf_asset_s_value; unfold le9; rewrite PTree.gso by discriminate; apply PTree.gss|reflexivity|].
        eapply eval_Econs; [apply sf_asset_s_value; apply PTree.gss|reflexivity|].
        eapply eval_Econs; [apply eval_Esizeof|reflexivity|apply eval_Enil].
      * exact sha_memcmp_funct.
      * reflexivity.
      * apply eval_funcall_external. exact HX.
    + apply exec_Sset. apply eval_Etempvar. apply PTree.gss.
  - unfold sf_le, le1, le9, le8. rewrite !PTree.gso by discriminate. exact HLe.
Qed.

(** [simplicity_assert(0 <= cmp)]: the failing branch is not taken. *)
Lemma sf_assert_exec le m rv :
  le!_cmp = Some (Vint rv) -> 0 <= Int.signed rv ->
  Clight2.exec_stmt sha_ge empty_env le m sf_assert E0 le m Out_normal.
Proof.
  intros Hc Hs. cbv delta [sf_assert] beta iota.
  eapply exec_Sifthenelse with (v1 := Vtrue) (b := true); [|reflexivity|apply exec_Sskip].
  eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; exact Hc|].
  change (Some (Val.of_bool (negb (Int.lt rv (Int.repr 0)))) = Some Vtrue).
  unfold Int.lt. change (Int.signed (Int.repr 0)) with 0. rewrite zlt_false by lia. reflexivity.
Qed.

(** [if (0 < cmp) { result++; feeOutputs[result] = feeOutputs[i]; }] *)
Lemma sf_bump_exec le m m0 arr fee k r rv (c : Datatypes.comparison) :
  sf_le le k r -> le!_cmp = Some (Vint rv) -> memcmp_sign c rv -> c <> Lt ->
  sf_mem m arr fee -> sf_frame m0 m -> (k < Nn)%nat -> (c = Gt -> (S r < Nn)%nat) -> (arr k < Nn)%nat ->
  exists le' m',
    Clight2.exec_stmt sha_ge empty_env le m sf_bump E0 le' m' Out_normal /\
    sf_le le' k (match c with Gt => S r | _ => r end) /\
    sf_mem m' (match c with Gt => upd arr (S r) (arr k) | _ => arr end) fee /\ sf_frame m0 m'.
Proof.
  intros HLe Hc HSg HnLt HM HFr Hk HSr Hak. pose proof HLe as (Hi & Hres & HF & HNf).
  destruct c; [|contradiction|].
  - cbn in HSg. subst rv. exists le, m. split; [|split; [exact HLe|split; assumption]].
    cbv delta [sf_bump] beta iota.
    eapply exec_Sifthenelse with (v1 := Vfalse) (b := false); [|reflexivity|apply exec_Sskip].
    eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; exact Hc|reflexivity].
  - cbn in HSg. specialize (HSr eq_refl).
    set (pk := Vptr (pb (arr k)) (Ptrofs.repr (po (arr k)))).
    set (leR := PTree.set _result (Vlong (Int64.repr (Z.of_nat (S r)))) le).
    set (le7 := PTree.set _t'7 pk leR).
    destruct (sf_mem_slot m arr fee (S r) (arr k) HM HSr Hak) as (m' & HS & HM' & HFr').
    pose proof sf_Nn as HNn.
    exists le7, m'. split; [|split; [|split; [exact HM'|exact (HFr' m0 HFr)]]].
    + cbv delta [sf_bump] beta iota.
      eapply exec_Sifthenelse with (v1 := Vtrue) (b := true); [|reflexivity|].
      { eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; exact Hc|].
        change (Some (Val.of_bool (Int.lt (Int.repr 0) rv)) = Some Vtrue).
        unfold Int.lt. change (Int.signed (Int.repr 0)) with 0. rewrite zlt_true by lia. reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leR) (m1 := m).
      { apply exec_Sset. eapply eval_Ebinop; [apply eval_Etempvar; exact Hres|apply eval_Econst_int|].
        replace (Z.of_nat (S r)) with (Z.of_nat r + 1) by lia. rewrite <- sf_i64_add. reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le7) (m1 := m).
      { apply exec_Sset. apply sf_slot_value with (s := k);
          [unfold leR; rewrite PTree.gso by discriminate; exact HF
          |unfold leR; rewrite PTree.gso by discriminate; exact Hi|exact Hk|].
        destruct HM as (HSl & _). exact (HSl k Hk). }
      eapply exec_Sassign with (v2 := pk) (v := pk).
      * apply sf_slot_lvalue with (s := S r);
          [unfold le7, leR; rewrite !PTree.gso by discriminate; exact HF
          |unfold le7; rewrite PTree.gso by discriminate; apply PTree.gss|exact HSr].
      * apply eval_Etempvar. apply PTree.gss.
      * reflexivity.
      * eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
        rewrite Ptrofs.unsigned_repr by lia. exact HS.
    + unfold sf_le, le7, leR. rewrite (PTree.gso _ _ (i := _i)) by discriminate.
      rewrite (PTree.gso _ _ (i := _i)) by discriminate.
      rewrite (PTree.gso _ _ (i := _result)) by discriminate. rewrite PTree.gss.
      rewrite !PTree.gso by discriminate. repeat split; assumption.
Qed.

(** [feeOutputs[result]->assetFee += feeOutputs[i]->amt.explicit;] *)
Lemma sf_add_exec le m m0 arr fee k r :
  sf_le le k r -> sf_mem m arr fee -> sf_frame m0 m ->
  (k < Nn)%nat -> (r < Nn)%nat -> (arr k < Nn)%nat -> (arr r < Nn)%nat ->
  exists le' m',
    Clight2.exec_stmt sha_ge empty_env le m sf_add E0 le' m' Out_normal /\
    sf_le le' k r /\
    sf_mem m' arr (upd fee (arr r) (Int64.add (fee (arr r)) (E (arr k)))) /\ sf_frame m0 m'.
Proof.
  intros HLe HM HFr Hk Hr Hak Har. pose proof HLe as (Hi & Hres & HF & HNf).
  pose proof HM as (HSl & HFe & (HW & HEx & HVf & HVs)).
  destruct (Hpo (arr k) Hak) as [Hpk0 HpkM]. destruct (Hpo (arr r) Har) as [Hpr0 HprM].
  set (pk := Vptr (pb (arr k)) (Ptrofs.repr (po (arr k)))).
  set (pr := Vptr (pb (arr r)) (Ptrofs.repr (po (arr r)))).
  set (le2 := PTree.set _t'2 pr le).
  set (le3 := PTree.set _t'3 pr le2).
  set (le4 := PTree.set _t'4 (Vlong (fee (arr r))) le3).
  set (le5 := PTree.set _t'5 pk le4).
  set (le6 := PTree.set _t'6 (Vlong (E (arr k))) le5).
  destruct (sf_mem_fee m arr fee (arr r) (Int64.add (fee (arr r)) (E (arr k))) HM Har) as (m' & HS & HM' & HFr').
  exists le6, m'. split; [|split; [|split; [exact HM'|exact (HFr' m0 HFr)]]].
  - cbv delta [sf_add] beta iota.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m).
    { apply exec_Sset. apply sf_slot_value with (s := r); [exact HF|exact Hres|exact Hr|exact (HSl r Hr)]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m).
    { apply exec_Sset. apply sf_slot_value with (s := r);
        [unfold le2; rewrite PTree.gso by discriminate; exact HF
        |unfold le2; rewrite PTree.gso by discriminate; exact Hres|exact Hr|exact (HSl r Hr)]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m).
    { apply exec_Sset. eapply eval_Elvalue.
      - apply sf_fee_lvalue with (b := pb (arr r)) (o := po (arr r)); [apply PTree.gss|lia|lia].
      - eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv.
        rewrite Ptrofs.unsigned_repr by lia. exact (HFe (arr r) Har). }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le5) (m1 := m).
    { apply exec_Sset. apply sf_slot_value with (s := k);
        [unfold le4, le3, le2; rewrite !PTree.gso by discriminate; exact HF
        |unfold le4, le3, le2; rewrite !PTree.gso by discriminate; exact Hi|exact Hk|exact (HSl k Hk)]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le6) (m1 := m).
    { apply exec_Sset. apply sf_explicit_value with (b := pb (arr k)) (o := po (arr k));
        [apply PTree.gss|lia|lia|exact (HEx (arr k) Hak)]. }
    eapply exec_Sassign with (v2 := Vlong (Int64.add (fee (arr r)) (E (arr k))))
      (v := Vlong (Int64.add (fee (arr r)) (E (arr k)))).
    + apply sf_fee_lvalue with (b := pb (arr r)) (o := po (arr r)); [|lia|lia].
      unfold le6, le5, le4, le3. rewrite !PTree.gso by discriminate. apply PTree.gss.
    + eapply eval_Ebinop;
        [apply eval_Etempvar; unfold le6, le5; rewrite !PTree.gso by discriminate; apply PTree.gss
        |apply eval_Etempvar; apply PTree.gss|reflexivity].
    + reflexivity.
    + eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
      rewrite Ptrofs.unsigned_repr by lia. exact HS.
  - unfold sf_le, le6, le5, le4, le3, le2. rewrite !PTree.gso by discriminate. exact HLe.
Qed.

(** One iteration. *)
Lemma sf_iter_step le m m0 st k :
  sf_le le k (sf_r st) -> sf_mem m (sf_arr st) (sf_fee st) -> sf_frame m0 m -> sf_pure k st -> (k < Nn)%nat ->
  exists le1 le2 m',
    Clight2.exec_stmt sha_ge empty_env le m sf_s1 E0 le1 m' Out_normal /\
    Clight2.exec_stmt sha_ge empty_env le1 m' sf_s2 E0 le2 m' Out_normal /\
    sf_le le2 (S k) (sf_r (sf_step k st)) /\
    sf_mem m' (sf_arr (sf_step k st)) (sf_fee (sf_step k st)) /\ sf_frame m0 m'.
Proof.
  intros HLe HM HFr HP Hk. destruct (sf_pure_cmp k st HP Hk) as [HnLt HGt]. pose proof HP as (P1 & P2 & P3).
  pose proof sf_Nn as HNn.
  assert (Hr : (sf_r st < Nn)%nat) by lia.
  assert (Har : (sf_arr st (sf_r st) < Nn)%nat) by (pose proof (P3 (sf_r st) ltac:(lia)); lia).
  assert (Hak : (sf_arr st k < Nn)%nat).
  { destruct (lt_dec (sf_r st) k) as [Hlt|Hge]; [rewrite (P2 k Hlt); exact Hk|].
    pose proof (P3 k ltac:(lia)). lia. }
  destruct (sf_cmp_exec le m (sf_arr st) (sf_fee st) k (sf_r st) HLe HM Hk Hr Hak Har)
    as (rv & leC & XC & LeC & HcC & HSg).
  unfold sf_step.
  remember (bytes_cmp (sf_A (sf_arr st k)) (sf_A (sf_arr st (sf_r st)))) as c eqn:EC.
  assert (Hrv : 0 <= Int.signed rv).
  { destruct c; cbn in HSg; [subst rv; reflexivity|contradiction|lia]. }
  destruct (sf_bump_exec leC m m0 (sf_arr st) (sf_fee st) k (sf_r st) rv c LeC HcC HSg HnLt HM HFr Hk
    ltac:(intros HG; destruct (HGt HG); lia) Hak) as (leB & m1 & XB & LeB & HM1 & HFr1).
  set (r1 := match c with Gt => S (sf_r st) | _ => sf_r st end) in *.
  set (arr1 := match c with Gt => upd (sf_arr st) (S (sf_r st)) (sf_arr st k) | _ => sf_arr st end) in *.
  assert (Hr1 : (r1 < Nn)%nat) by (unfold r1; destruct c; try exact Hr; destruct (HGt eq_refl); lia).
  assert (Hak1 : arr1 k = sf_arr st k).
  { unfold arr1. destruct c; try reflexivity. unfold upd. destruct (Nat.eqb k (S (sf_r st))); reflexivity. }
  assert (Har1 : arr1 r1 = match c with Gt => sf_arr st k | _ => sf_arr st (sf_r st) end).
  { unfold arr1, r1. destruct c; try reflexivity. apply upd_same. }
  destruct (sf_add_exec leB m1 m0 arr1 (sf_fee st) k r1 LeB HM1 HFr1 Hk Hr1
    ltac:(rewrite Hak1; exact Hak) ltac:(rewrite Har1; destruct c; assumption))
    as (leA & m2 & XA & LeA & HM2 & HFr2).
  set (le2 := PTree.set _i (Vlong (Int64.repr (Z.of_nat (S k)))) leA).
  exists leA, le2, m2. split; [|split; [|split; [|split; [|exact HFr2]]]].
  - rewrite sf_s1_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m).
    { eapply exec_Sifthenelse with (v1 := Vtrue) (b := true); [|reflexivity|apply exec_Sskip].
      destruct HLe as (Hi & _ & _ & HNf).
      eapply eval_Ebinop; [apply eval_Etempvar; exact Hi|apply eval_Etempvar; exact HNf|].
      change (Some (Val.of_bool (Int64.ltu (Int64.repr (Z.of_nat k)) (Int64.repr N))) = Some Vtrue).
      unfold Int64.ltu.
      rewrite !Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
      rewrite zlt_true by lia. reflexivity. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leC) (m1 := m); [exact XC|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leC) (m1 := m);
      [exact (sf_assert_exec leC m rv HcC Hrv)|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leB) (m1 := m1); [exact XB|exact XA].
  - cbv delta [sf_s2] beta iota. apply exec_Sset. destruct LeA as (Hi & _).
    eapply eval_Ebinop; [apply eval_Etempvar; exact Hi|apply eval_Econst_int|].
    replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia. rewrite <- sf_i64_add. reflexivity.
  - destruct LeA as (Hi & Hres & HF & HNf).
    assert (HR : sf_r (match c with
                       | Gt => {| sf_r := S (sf_r st); sf_arr := upd (sf_arr st) (S (sf_r st)) (sf_arr st k);
                                  sf_fee := upd (sf_fee st) (sf_arr st k)
                                              (Int64.add (sf_fee st (sf_arr st k)) (E (sf_arr st k))) |}
                       | _ => {| sf_r := sf_r st; sf_arr := sf_arr st;
                                 sf_fee := upd (sf_fee st) (sf_arr st (sf_r st))
                                             (Int64.add (sf_fee st (sf_arr st (sf_r st))) (E (sf_arr st k))) |}
                       end) = r1) by (unfold r1; destruct c; reflexivity).
    rewrite HR. unfold sf_le, le2. rewrite PTree.gss. rewrite !PTree.gso by discriminate.
    repeat split; assumption.
  - rewrite Har1, Hak1 in HM2. unfold arr1 in HM2. destruct c; exact HM2.
Qed.

Section Run.
Variables (m0 : mem) (fee0 : nat -> int64).
Let st0 := sf_init fee0.

Lemma sf_loop d : forall k le m, (k + d = Nn)%nat ->
  sf_le le k (sf_r (sf_iter k st0)) ->
  sf_mem m (sf_arr (sf_iter k st0)) (sf_fee (sf_iter k st0)) -> sf_frame m0 m ->
  exists le' m',
    Clight2.exec_stmt sha_ge empty_env le m (Sloop sf_s1 sf_s2) E0 le' m' Out_normal /\
    sf_le le' Nn (sf_r (sf_iter Nn st0)) /\
    sf_mem m' (sf_arr (sf_iter Nn st0)) (sf_fee (sf_iter Nn st0)) /\ sf_frame m0 m'.
Proof.
  pose proof sf_Nn as HNn.
  induction d as [|d IH]; intros k le m Hkd HLe HM HFr.
  - replace k with Nn in * by lia. exists le, m. split; [|split; [exact HLe|split; assumption]].
    eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
    rewrite sf_s1_shape. eapply exec_Sseq_2; [|discriminate].
    eapply exec_Sifthenelse with (v1 := Vfalse) (b := false); [|reflexivity|apply exec_Sbreak].
    destruct HLe as (Hi & _ & _ & HNf).
    eapply eval_Ebinop; [apply eval_Etempvar; exact Hi|apply eval_Etempvar; exact HNf|].
    change (Some (Val.of_bool (Int64.ltu (Int64.repr (Z.of_nat Nn)) (Int64.repr N))) = Some Vfalse).
    rewrite HNn. unfold Int64.ltu. rewrite zlt_false by lia. reflexivity.
  - destruct (sf_iter_step le m m0 (sf_iter k st0) k HLe HM HFr (sf_pure_iter fee0 k ltac:(lia)) ltac:(lia))
      as (le1 & le2 & m' & X1 & X2 & Le2 & HM' & HFr').
    destruct (IH (S k) le2 m' ltac:(lia) Le2 HM' HFr') as (le' & mf & XL & LeF & HMf & HFrf).
    exists le', mf. split; [|split; [exact LeF|split; assumption]].
    change E0 with (E0 ** E0 ** E0).
    eapply exec_Sloop_loop; [exact X1|constructor|exact X2|exact XL].
Qed.

Theorem eval_sumFees :
  sf_mem m0 (fun j => j) fee0 ->
  exists m',
    Clight2.eval_funcall sha_ge m0 (Internal f_sumFees) [arrv; Vlong (Int64.repr N)] E0 m'
      (Vlong (Int64.repr (Z.of_nat (sf_r (sf_iter Nn st0)) + 1))) /\
    sf_mem m' (sf_arr (sf_iter Nn st0)) (sf_fee (sf_iter Nn st0)) /\ sf_frame m0 m'.
Proof.
  intros HM.
  set (le0 := PTree.set _numFees (Vlong (Int64.repr N))
    (PTree.set _feeOutputs arrv (create_undef_temps (fn_temps f_sumFees)))).
  set (leR := PTree.set _result (Vlong (Int64.repr 0)) le0).
  set (leI := PTree.set _i (Vlong (Int64.repr 0)) leR).
  destruct (sf_loop Nn 0%nat leI m0 eq_refl) as (le' & m' & XL & (Hi & Hres & HF & HNf) & HM' & HFr').
  { unfold sf_le. cbn [sf_iter sf_r st0 sf_init]. repeat split; reflexivity. }
  { exact HM. }
  { apply sf_frame_refl. }
  exists m'. split; [|split; assumption].
  eapply eval_funcall_internal with (e := empty_env) (le1 := le0) (m1 := m0) (m2 := m') (le2 := le')
    (out := Out_return (Some (Vlong (Int64.repr (Z.of_nat (sf_r (sf_iter Nn st0)) + 1)), tulong))).
  - apply function_entry2_intro.
    + apply list_norepet_nil.
    + repeat constructor; simpl; intuition discriminate.
    + intros x0 y0 HX HY; cbn in HX, HY; intuition (subst; discriminate).
    + apply alloc_variables_nil.
    + reflexivity.
  - rewrite sf_body_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leR) (m1 := m0).
    { apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leR) (m1 := m0).
    { eapply exec_Sifthenelse with (v1 := Vfalse) (b := false); [|reflexivity|apply exec_Sskip].
      eapply eval_Ebinop; [apply eval_Etempvar; unfold leR; rewrite PTree.gso by discriminate; apply PTree.gss
                          |apply eval_Econst_int|].
      change (Some (Val.of_bool (Int64.ltu (Int64.repr N) (Int64.repr (Int.signed (Int.repr 1))))) = Some Vfalse).
      unfold Int64.ltu. rewrite (Int64.unsigned_repr N) by (change Int64.max_unsigned with 18446744073709551615; lia).
      change (Int64.unsigned (Int64.repr (Int.signed (Int.repr 1)))) with 1. rewrite zlt_false by lia. reflexivity. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le') (m1 := m').
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leI) (m1 := m0); [|exact XL].
      apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
    + apply exec_Sreturn_some.
      eapply eval_Ebinop; [apply eval_Etempvar; exact Hres|apply eval_Econst_int|].
      rewrite <- sf_i64_add. reflexivity.
  - cbn. split; [discriminate|reflexivity].
  - reflexivity.
Qed.
End Run.
End SumFees.

(** No fee output: nothing is read or written. *)
Theorem eval_sumFees_zero m (v : val) :
  Clight2.eval_funcall sha_ge m (Internal f_sumFees) [v; Vlong (Int64.repr 0)] E0 m (Vlong (Int64.repr 0)).
Proof.
  set (le0 := PTree.set _numFees (Vlong (Int64.repr 0))
    (PTree.set _feeOutputs v (create_undef_temps (fn_temps f_sumFees)))).
  set (leR := PTree.set _result (Vlong (Int64.repr 0)) le0).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le0) (m1 := m) (m2 := m) (le2 := leR)
    (out := Out_return (Some (Vlong (Int64.repr 0), tulong))).
  - apply function_entry2_intro.
    + apply list_norepet_nil.
    + repeat constructor; simpl; intuition discriminate.
    + intros x0 y0 HX HY; cbn in HX, HY; intuition (subst; discriminate).
    + apply alloc_variables_nil.
    + reflexivity.
  - rewrite sf_body_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leR) (m1 := m).
    { apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity]. }
    eapply exec_Sseq_2; [|discriminate].
    eapply exec_Sifthenelse with (v1 := Vtrue) (b := true); [|reflexivity|].
    + eapply eval_Ebinop; [apply eval_Etempvar; reflexivity|apply eval_Econst_int|reflexivity].
    + apply exec_Sreturn_some. apply eval_Etempvar. apply PTree.gss.
  - cbn. split; [discriminate|reflexivity].
  - reflexivity.
Qed.
