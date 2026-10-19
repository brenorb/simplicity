(** Execution of [copyRawConfidential(conf, rawConf)] (elements/env.c), the
    reader of every asset and nonce of a raw Elements transaction:
      rawConf == NULL   *conf = (confidential){0}
      otherwise         *conf = (confidential){ .prefix = EXPLICIT, ODD_Y or
                          EVEN_Y by rawConf[0] }, then the midstate of
                          rawConf[1..32] is stored in conf->data.
    Both branches build a compound literal in a stack block, copy it to
    [*conf] and free the stack blocks on return. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_uint32_array_init C.jet_struct_copy_loads.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_be32_exec C.jet_sha_compress_call.
Require Import C.jet_env_store_words C.jet_elements_env_field_eval C.jet_elements_env_tomidstate.
Require Import C.jet_elements_env_tapenv_key C.jet_elements_env_copyrawamt.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Local Notation CONF := (Tstruct _confidential noattr).
Local Notation RMID := (Tstruct _sha256_midstate noattr).
Local Notation RA8 := (tarray tuint 8).

(** Zeroing the eight words of a midstate designated by an expression. *)
Definition rc_zero_g (a : expr) (k : nat) : statement :=
  Sassign (Ederef (Ebinop Oadd (Efield a _s RA8)
    (Econst_int (Int.repr (Z.of_nat k)) tint) (tptr tuint)) tuint) (Econst_int (Int.repr 0) tint).

Fixpoint rc_zsr (acc : statement) (a : expr) (lo n : nat) : statement :=
  match n with
  | O => acc
  | S k => Ssequence (rc_zsr acc a lo k) (rc_zero_g a (lo + k))
  end.

Definition rc_data (cid : ident) : expr := Efield (Evar cid CONF) _data RMID.
Definition rc_zeros (cid : ident) : statement := rc_zsr (rc_zero_g (rc_data cid) 0) (rc_data cid) 1 7.
Definition rc_prefix_assign (cid : ident) (rhs : expr) : statement :=
  Sassign (Efield (Evar cid CONF) _prefix tint) rhs.
Definition rc_copy (cid : ident) : statement :=
  Sassign (Ederef (Etempvar _conf (tptr CONF)) CONF) (Evar cid CONF).

Definition rc_compute : statement :=
  ltac:(let b := eval cbv delta [f_copyRawConfidential fn_body] beta iota in (fn_body f_copyRawConfidential) in
        lazymatch b with
        | Sifthenelse _ (Ssequence (Ssequence (Ssequence (Ssequence _ ?c) _) _) _) _ => exact c
        end).
Definition rc_call : statement :=
  ltac:(let b := eval cbv delta [f_copyRawConfidential fn_body] beta iota in (fn_body f_copyRawConfidential) in
        lazymatch b with Sifthenelse _ (Ssequence _ ?c) _ => exact c end).

Lemma rc_body_shape :
  fn_body f_copyRawConfidential =
    Sifthenelse (Etempvar _rawConf (tptr tuchar))
      (Ssequence
        (Ssequence
          (Ssequence (Ssequence (rc_zeros ___compound) rc_compute)
                     (rc_prefix_assign ___compound (Etempvar _t'1 tint)))
          (rc_copy ___compound))
        rc_call)
      (Ssequence
        (Ssequence (rc_zeros ___compound__1) (rc_prefix_assign ___compound__1 (Econst_int (Int.repr 0) tint)))
        (rc_copy ___compound__1)).
Proof. reflexivity. Qed.

Definition rc_env (bC1 bC2 : block) : env :=
  PTree.set ___compound__1 (bC2, CONF) (PTree.set ___compound (bC1, CONF) empty_env).

Lemma rc_sizeof : sizeof sha_ge CONF = 36.
Proof. vm_compute; reflexivity. Qed.
Lemma rc_blockcopy : alignof_blockcopy sha_ge CONF = 4.
Proof. vm_compute; reflexivity. Qed.
Lemma rc_blocks bC1 bC2 : blocks_of_env sha_ge (rc_env bC1 bC2) = [(bC2, 0, 36); (bC1, 0, 36)].
Proof. vm_compute. reflexivity. Qed.

Lemma envu_confidential_data : envu_field_at _confidential _data 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_confidential_prefix : envu_field_at _confidential _prefix 32.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.

Lemma rc_entry m m0a m0 bC1 bC2 vconf vraw :
  Mem.alloc m 0 36 = (m0a, bC1) -> Mem.alloc m0a 0 36 = (m0, bC2) ->
  function_entry2 sha_ge f_copyRawConfidential [vconf; vraw] m (rc_env bC1 bC2)
    (PTree.set _rawConf vraw (PTree.set _conf vconf (create_undef_temps (fn_temps f_copyRawConfidential)))) m0.
Proof.
  intros A1 A2. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst; try contradiction; discriminate.
  - eapply alloc_variables_cons with (m1 := m0a) (b1 := bC1); [rewrite rc_sizeof; exact A1|].
    eapply alloc_variables_cons with (m1 := m0) (b1 := bC2); [rewrite rc_sizeof; exact A2|].
    constructor.
  - reflexivity.
Qed.

Local Opaque sha_ge.

(** Zero runs through an arbitrary midstate-typed expression. *)
Section ZeroRun.
Variables (e : env) (b : block) (a : expr) (delta : Z).
Hypothesis Ha : forall le m, eval_expr sha_ge e le m a (Vptr b (Ptrofs.repr delta)).
Hypothesis Hty : typeof a = RMID.
Hypothesis Hd : 0 <= delta <= 4000.

Lemma rc_exec_zero_g le m m' k :
  (k < 8)%nat ->
  Mem.store Mint32 m b (delta + 4 * Z.of_nat k) (Vint Int.zero) = Some m' ->
  Clight2.exec_stmt sha_ge e le m (rc_zero_g a k) E0 le m' Out_normal.
Proof.
  intros Hk HS.
  eapply exec_Sassign with (v2 := Vint Int.zero) (v := Vint Int.zero).
  - pose proof (eval_envu_field_array e le m a _sha256_midstate _s 0 RA8 b (Ptrofs.repr delta)
      Hty envu_sha256_midstate_s ltac:(intros chunk; discriminate) eq_refl (Ha le m)) as HE.
    rewrite Ptrofs.add_zero in HE.
    eapply eval_Ederef. eapply eval_Ebinop; [exact HE|apply eval_Econst_int|reflexivity].
  - apply eval_Econst_int.
  - reflexivity.
  - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
    assert (HU : Ptrofs.unsigned (Ptrofs.repr delta) = delta)
      by (apply Ptrofs.unsigned_repr; change Ptrofs.max_unsigned with 18446744073709551615; lia).
    rewrite ptr_word_offset_from by (rewrite ?HU; change Ptrofs.max_unsigned with 18446744073709551615; lia).
    rewrite HU. exact HS.
Qed.

Lemma rc_zsr_exec n : forall lo, (lo + n <= 8)%nat ->
  forall acc le0 le m0 m1 m2,
  Clight2.exec_stmt sha_ge e le0 m0 acc E0 le m1 Out_normal ->
  store_words m1 b (delta + 4 * Z.of_nat lo) (repeat Int.zero n) = Some m2 ->
  Clight2.exec_stmt sha_ge e le0 m0 (rc_zsr acc a lo n) E0 le m2 Out_normal.
Proof.
  induction n as [|n IH]; intros lo Hn acc le0 le m0 m1 m2 HA HS.
  - cbn in HS. injection HS as <-. exact HA.
  - rewrite repeat_snoc in HS. destruct (store_words_app_inv _ _ _ _ _ _ HS) as (mm & H1 & H2).
    rewrite repeat_length in H2. cbn [store_words] in H2.
    destruct (Mem.store Mint32 mm b (delta + 4 * Z.of_nat lo + 4 * Z.of_nat n) (Vint Int.zero)) as [mx|] eqn:HSt;
      [|discriminate].
    injection H2 as <-.
    cbn [rc_zsr]. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply IH; [lia|exact HA|exact H1].
    + eapply rc_exec_zero_g; [lia|].
      replace (delta + 4 * Z.of_nat (lo + n)) with (delta + 4 * Z.of_nat lo + 4 * Z.of_nat n) by lia. exact HSt.
Qed.
End ZeroRun.

(** The prefix of a non-null raw value (elements/txEnv.h). *)
Definition conf_prefix (x0 : int) : int :=
  if Int.eq (Int.repr 1) x0 then Int.repr 1 else amt_parity x0.

Section CopyRawConfidential.
Variables (bconf : block) (oconf : Z).
Hypothesis Ho0 : 0 <= oconf.
Hypothesis HoM : oconf + 36 <= Ptrofs.max_unsigned.
Hypothesis HoA : (4 | oconf).

Let confv := Vptr bconf (Ptrofs.repr oconf).

(** Filling a compound literal and copying it to [*conf]. *)
Section Compound.
Variables (e : env) (cid : ident) (bC : block).
Hypothesis HeC : e!cid = Some (bC, CONF).
Hypothesis NCc : bC <> bconf.

Lemma rc_ev_c le m : eval_expr sha_ge e le m (Evar cid CONF) (Vptr bC Ptrofs.zero).
Proof. eapply eval_Elvalue; [apply eval_Evar_local; exact HeC|apply deref_loc_copy; reflexivity]. Qed.

Lemma rc_ev_data le m : eval_expr sha_ge e le m (rc_data cid) (Vptr bC (Ptrofs.repr 0)).
Proof.
  pose proof (eval_envu_field_struct e le m (Evar cid CONF) _confidential _data 0 _sha256_midstate
    bC Ptrofs.zero eq_refl envu_confidential_data (rc_ev_c le m)) as HE.
  rewrite Ptrofs.add_zero_l in HE. exact HE.
Qed.

Lemma rc_zeros_exec le m :
  Mem.range_perm m bC 0 36 Cur Writable ->
  exists mW,
    store_words m bC 0 (repeat Int.zero 8) = Some mW /\
    Clight2.exec_stmt sha_ge e le m (rc_zeros cid) E0 le mW Out_normal.
Proof.
  intros PC.
  destruct (store_words_exists (repeat Int.zero 8) m bC 0) as [mW SW].
  { intros o Ho. rewrite repeat_length in Ho. apply PC. lia. } { exists 0. reflexivity. }
  exists mW. split; [exact SW|].
  change (repeat Int.zero 8) with ([Int.zero] ++ repeat Int.zero 7) in SW.
  destruct (store_words_app_inv _ _ _ _ _ _ SW) as (ma & H1 & H2).
  cbn [store_words] in H1.
  destruct (Mem.store Mint32 m bC 0 (Vint Int.zero)) as [mx|] eqn:SA; [|discriminate].
  injection H1 as ->.
  unfold rc_zeros.
  eapply (rc_zsr_exec e bC (rc_data cid) 0 rc_ev_data eq_refl ltac:(lia) 7 1 ltac:(lia)) with (m1 := ma).
  - eapply (rc_exec_zero_g e bC (rc_data cid) 0 rc_ev_data eq_refl ltac:(lia)); [lia|exact SA].
  - exact H2.
Qed.

(** After the zero run: the prefix store and the copy. *)
Lemma rc_tail_exec le m mW (rhs : expr) (pfx : int) :
  store_words m bC 0 (repeat Int.zero 8) = Some mW ->
  Mem.range_perm m bC 0 36 Cur Writable ->
  Mem.range_perm m bconf oconf (oconf + 36) Cur Writable ->
  le!_conf = Some confv ->
  typeof rhs = tint ->
  (forall m', eval_expr sha_ge e le m' rhs (Vint pfx)) ->
  exists mF m',
    Clight2.exec_stmt sha_ge e le mW (rc_prefix_assign cid rhs) E0 le mF Out_normal /\
    Clight2.exec_stmt sha_ge e le mF (rc_copy cid) E0 le m' Out_normal /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 m' bconf (oconf + 4 * Z.of_nat j) = Some (Vint Int.zero)) /\
    Mem.load Mint32 m' bconf (oconf + 32) = Some (Vint pfx) /\
    (forall ch b ofs, b <> bC -> (b <> bconf \/ ofs + size_chunk ch <= oconf \/ oconf + 36 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros SW PC PR HlC Hty Hrhs.
  assert (PW : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mW b ofs k p).
  { intros b ofs k p Hp. apply (store_words_perm _ _ _ _ _ SW), Hp. }
  destruct (Mem.valid_access_store mW Mint32 bC 32 (Vint pfx)) as [mF SF].
  { split; [|exists 8; reflexivity]. intros o Ho. change (size_chunk Mint32) with 4 in Ho. apply PW, PC. lia. }
  assert (PF : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mF b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact SF|apply PW, Hp]. }
  destruct (Mem.range_perm_loadbytes mF bC 0 36) as (bytes & HCB).
  { intros o Ho. eapply Mem.perm_implies; [apply PF, PC, Ho|constructor]. }
  pose proof (Mem.loadbytes_length _ _ _ _ _ HCB) as HCBL.
  destruct (Mem.range_perm_storebytes mF bconf oconf bytes) as (mG & SG).
  { rewrite HCBL. intros o Ho. change (Z.of_nat (Z.to_nat 36)) with 36 in Ho. apply PF, PR. lia. }
  assert (HGB : Mem.loadbytes mG bconf oconf 36 = Some bytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ SG) as H. rewrite HCBL in H. exact H. }
  exists mF, mG. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - unfold rc_prefix_assign. eapply exec_Sassign with (v2 := Vint pfx) (v := Vint pfx).
    + eapply eval_envu_field_lvalue; [reflexivity|exact envu_confidential_prefix|apply rc_ev_c].
    + apply Hrhs.
    + rewrite Hty. reflexivity.
    + eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
      rewrite Ptrofs.add_zero_l.
      rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
      exact SF.
  - unfold rc_copy.
    eapply exec_Sassign with (v2 := Vptr bC Ptrofs.zero) (v := Vptr bC Ptrofs.zero).
    + eapply eval_Ederef. apply eval_Etempvar. exact HlC.
    + apply rc_ev_c.
    + reflexivity.
    + eapply assign_loc_copy with (bytes := bytes); cbn [typeof].
      * reflexivity.
      * intros _. rewrite rc_blockcopy. exists 0. reflexivity.
      * intros _. rewrite rc_blockcopy, Ptrofs.unsigned_repr by lia. exact HoA.
      * left. exact NCc.
      * rewrite rc_sizeof. exact HCB.
      * rewrite Ptrofs.unsigned_repr by lia. exact SG.
  - intros j Hj.
    apply (equal_loadbytes_field Mint32 mF mG bC bconf 0 oconf 36 (4 * Z.of_nat j) bytes);
      [lia|change (size_chunk Mint32) with 4; lia|exact HCB|exact HGB| |].
    + change (align_chunk Mint32) with 4. destruct HoA as [k ->]. exists (k + Z.of_nat j). lia.
    + rewrite (Mem.load_store_other _ _ _ _ _ _ SF)
        by (right; left; change (size_chunk Mint32) with 4; lia).
      apply (store_words_loads _ _ _ _ _ SW).
      apply nth_error_repeat. exact Hj.
  - apply (equal_loadbytes_field Mint32 mF mG bC bconf 0 oconf 36 32 bytes);
      [lia|change (size_chunk Mint32) with 4; lia|exact HCB|exact HGB| |].
    + change (align_chunk Mint32) with 4. destruct HoA as [k ->]. exists (k + 8). lia.
    + change (0 + 32) with 32. rewrite (Mem.load_store_same _ _ _ _ _ _ SF). reflexivity.
  - intros ch b ofs Hb Hr. rewrite (Mem.load_storebytes_other _ _ _ _ _ SG).
    + rewrite (Mem.load_store_other _ _ _ _ _ _ SF) by (left; exact Hb).
      apply (store_words_load_other _ _ _ _ _ SW). left. exact Hb.
    + rewrite HCBL. change (Z.of_nat (Z.to_nat 36)) with 36.
      destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; exact Hr|right; right; exact Hr].
  - intros b ofs k p Hp. eapply Mem.perm_storebytes_1; [exact SG|apply PF, Hp].
  - intros b Hb. eapply Mem.storebytes_valid_block_1; [exact SG|].
    eapply Mem.store_valid_block_1; [exact SF|].
    unfold Mem.valid_block. rewrite (store_words_nextblock _ _ _ _ _ SW). exact Hb.
Qed.
End Compound.

Section Frame.
Variables (m m0a m0 : mem) (bC1 bC2 : block).
Hypothesis A1 : Mem.alloc m 0 36 = (m0a, bC1).
Hypothesis A2 : Mem.alloc m0a 0 36 = (m0, bC2).

Lemma rc_fresh1 b : Mem.valid_block m b -> b <> bC1.
Proof. intros Hb E. subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ A1 Hb). Qed.
Lemma rc_fresh2 b : Mem.valid_block m b -> b <> bC2.
Proof.
  intros Hb E. subst b. apply (Mem.fresh_block_alloc _ _ _ _ _ A2).
  eapply Mem.valid_block_alloc; [exact A1|exact Hb].
Qed.
Lemma rc_fresh12 : bC1 <> bC2.
Proof.
  intros E. apply (Mem.fresh_block_alloc _ _ _ _ _ A2). rewrite <- E.
  eapply Mem.valid_new_block. exact A1.
Qed.
Lemma rc_load0 ch b ofs : Mem.valid_block m b -> Mem.load ch m0 b ofs = Mem.load ch m b ofs.
Proof.
  intros Hb. rewrite (Mem.load_alloc_unchanged _ _ _ _ _ A2) by (eapply Mem.valid_block_alloc; [exact A1|exact Hb]).
  eapply Mem.load_alloc_unchanged; [exact A1|exact Hb].
Qed.
Lemma rc_perm0 b ofs k p : Mem.perm m b ofs k p -> Mem.perm m0 b ofs k p.
Proof. intros Hp. eapply Mem.perm_alloc_1; [exact A2|]. eapply Mem.perm_alloc_1; [exact A1|exact Hp]. Qed.
Lemma rc_valid0 b : Mem.valid_block m b -> Mem.valid_block m0 b.
Proof. intros Hb. eapply Mem.valid_block_alloc; [exact A2|]. eapply Mem.valid_block_alloc; [exact A1|exact Hb]. Qed.
Lemma rc_permC1 : Mem.range_perm m0 bC1 0 36 Cur Freeable.
Proof. intros o Ho. eapply Mem.perm_alloc_1; [exact A2|]. eapply Mem.perm_alloc_2; [exact A1|exact Ho]. Qed.
Lemma rc_permC2 : Mem.range_perm m0 bC2 0 36 Cur Freeable.
Proof. intros o Ho. eapply Mem.perm_alloc_2; [exact A2|exact Ho]. Qed.

(** Leaving the function: the two stack blocks are freed. *)
Lemma rc_leave m5 :
  (forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m5 b ofs k p) ->
  exists mf,
    Mem.free_list m5 (blocks_of_env sha_ge (rc_env bC1 bC2)) = Some mf /\
    (forall ch b ofs, Mem.valid_block m b -> Mem.load ch mf b ofs = Mem.load ch m5 b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m5 b ofs k p -> Mem.perm mf b ofs k p) /\
    (forall b, Mem.valid_block m5 b -> Mem.valid_block mf b).
Proof.
  intros P5. rewrite rc_blocks.
  destruct (free_list_blocks [(bC2, 0, 36); (bC1, 0, 36)] m5) as (mf & HFL & HLf & HPf & HVf).
  { intros b lo hi HIn ofs Hr. destruct HIn as [E|[E|[]]]; injection E as <- <- <-.
    - apply P5, rc_permC2, Hr.
    - apply P5, rc_permC1, Hr. }
  { cbn [map fst]. apply NoDup_cons; [intros [E|[]]; exact (rc_fresh12 E)|].
    apply NoDup_cons; [intros []|apply NoDup_nil]. }
  cbn [map fst] in HLf, HPf.
  assert (NIn : forall b, Mem.valid_block m b -> ~ In b [bC2; bC1]).
  { intros b Hb [E|[E|[]]]; [exact (rc_fresh2 b Hb (eq_sym E))|exact (rc_fresh1 b Hb (eq_sym E))]. }
  exists mf. split; [exact HFL|]. split; [|split].
  - intros ch b ofs Hb. apply HLf, NIn, Hb.
  - intros b ofs k p Hb Hp. apply HPf; [apply NIn, Hb|exact Hp].
  - exact HVf.
Qed.
End Frame.

Definition rc_post (m m' : mem) (pfx : int) (ws : list int) : Prop :=
  uint32_array_at m' bconf oconf ws /\
  Mem.load Mint32 m' bconf (oconf + 32) = Some (Vint pfx) /\
  (forall ch b ofs, Mem.valid_block m b ->
     (b <> bconf \/ ofs + size_chunk ch <= oconf \/ oconf + 36 <= ofs) ->
     Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
  (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
  (forall b, Mem.valid_block m b -> Mem.valid_block m' b).

(** [rawConf == NULL]: the all-zero value (prefix NONE). *)
Theorem eval_copyRawConfidential_null m :
  Mem.range_perm m bconf oconf (oconf + 36) Cur Writable ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_copyRawConfidential) [confv; Vlong Int64.zero] E0 m' Vundef /\
    rc_post m m' Int.zero (repeat Int.zero 8).
Proof.
  intros PR.
  assert (Vc : Mem.valid_block m bconf) by (eapply Mem.perm_valid_block; apply (PR oconf); lia).
  destruct (Mem.alloc m 0 36) as [m0a bC1] eqn:A1.
  destruct (Mem.alloc m0a 0 36) as [m0 bC2] eqn:A2.
  set (e := rc_env bC1 bC2).
  set (le := PTree.set _rawConf (Vlong Int64.zero)
    (PTree.set _conf confv (create_undef_temps (fn_temps f_copyRawConfidential)))).
  assert (HeC : e!___compound__1 = Some (bC2, CONF)) by reflexivity.
  assert (NCc : bC2 <> bconf) by (apply not_eq_sym, (rc_fresh2 _ _ _ _ _ A1 A2), Vc).
  assert (PC : Mem.range_perm m0 bC2 0 36 Cur Writable).
  { intros o Ho. eapply Mem.perm_implies; [apply (rc_permC2 _ _ _ A2), Ho|constructor]. }
  assert (PR0 : Mem.range_perm m0 bconf oconf (oconf + 36) Cur Writable).
  { intros o Ho. apply (rc_perm0 _ _ _ _ _ A1 A2), PR, Ho. }
  destruct rc_zeros_exec with (e := e) (cid := ___compound__1) (bC := bC2) (le := le) (m := m0)
    as (mW & SW & HZ); try assumption.
  destruct rc_tail_exec with (e := e) (cid := ___compound__1) (bC := bC2) (le := le) (m := m0) (mW := mW)
    (rhs := Econst_int (Int.repr 0) tint) (pfx := Int.zero)
    as (mF & m5 & HPa & HCp & HW5 & HP5 & HL5 & HPm5 & HV5);
    try assumption; try reflexivity; [intros; apply eval_Econst_int|].
  destruct (rc_leave m m0a m0 bC1 bC2 A1 A2 m5 HPm5) as (mf & HFL & HLf & HPf & HVf).
  exists mf. split.
  - eapply eval_funcall_internal with (e := e) (le1 := le) (m1 := m0) (le2 := le) (m2 := m5) (out := Out_normal).
    + eapply rc_entry; [exact A1|exact A2].
    + rewrite rc_body_shape.
      eapply exec_Sifthenelse with (v1 := Vlong Int64.zero) (b := false).
      * apply eval_Etempvar. reflexivity.
      * reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mF); [|exact HCp].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mW); [exact HZ|exact HPa].
    + cbn. reflexivity.
    + exact HFL.
  - split; [|split; [|split; [|split]]].
    + intros i x Hi.
      assert (Hlt : (i < 8)%nat).
      { rewrite <- (repeat_length Int.zero 8). apply nth_error_Some. rewrite Hi. discriminate. }
      apply nth_error_In in Hi. apply repeat_spec in Hi. subst x.
      rewrite HLf by exact Vc. apply HW5, Hlt.
    + rewrite HLf by exact Vc. exact HP5.
    + intros ch b ofs Hb Hr. rewrite HLf by exact Hb.
      rewrite HL5 by (exact Hr || apply (rc_fresh2 _ _ _ _ _ A1 A2), Hb).
      apply (rc_load0 _ _ _ _ _ A1 A2). exact Hb.
    + intros b ofs k p Hb Hp. apply HPf; [exact Hb|]. apply HPm5, (rc_perm0 _ _ _ _ _ A1 A2), Hp.
    + intros b Hb. apply HVf, HV5, (rc_valid0 _ _ _ _ _ A1 A2), Hb.
Qed.
Section Raw.
Variables (braw : block) (oraw : ptrofs) (bs : list int).
Hypothesis Hdiff : braw <> bconf.

Let rawv := Vptr braw oraw.
Let o1 := Ptrofs.add oraw (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1))).

Lemma rc_raw0 e le m x :
  le!_rawConf = Some rawv ->
  Mem.load Mint8unsigned m braw (Ptrofs.unsigned oraw) = Some (Vint x) ->
  eval_expr sha_ge e le m
    (Ederef (Ebinop Oadd (Etempvar _rawConf (tptr tuchar)) (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
    (Vint x).
Proof.
  intros HR HL. pose proof (Ptrofs.unsigned_range_2 oraw) as HO. eapply eval_Elvalue.
  - eapply eval_Ederef. eapply eval_Ebinop; [apply eval_Etempvar; exact HR|apply eval_Econst_int|reflexivity].
  - eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv.
    rewrite ptr_byte_offset by lia. rewrite Z.add_0_r. exact HL.
Qed.

(** The prefix computation: no memory effect, [_t'1] holds the prefix. *)
Lemma rc_compute_exec e le m x0 :
  le!_rawConf = Some rawv ->
  Mem.load Mint8unsigned m braw (Ptrofs.unsigned oraw) = Some (Vint x0) ->
  exists le1,
    Clight2.exec_stmt sha_ge e le m rc_compute E0 le1 m Out_normal /\
    le1!_t'1 = Some (Vint (conf_prefix x0)) /\ le1!_conf = le!_conf /\ le1!_rawConf = le!_rawConf.
Proof.
  intros HR HL. unfold rc_compute, conf_prefix, amt_parity.
  set (le2 := PTree.set _t'2 (Vint x0) le).
  assert (HR2 : le2!_rawConf = Some rawv) by (unfold le2; rewrite PTree.gso by discriminate; exact HR).
  destruct (Int.eq (Int.repr 1) x0) eqn:H1.
  - exists (PTree.set _t'1 (Vint (Int.repr 1)) le2). split; [|split; [|split]].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m).
      { apply exec_Sset. apply rc_raw0; assumption. }
      eapply exec_Sifthenelse with (v1 := Vtrue) (b := true).
      * eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; apply PTree.gss|].
        cbn. unfold Cop.sem_cmp, Cop.sem_binarith. cbn. rewrite H1. reflexivity.
      * reflexivity.
      * apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
    + apply PTree.gss.
    + unfold le2. rewrite !PTree.gso by discriminate. reflexivity.
    + unfold le2. rewrite !PTree.gso by discriminate. reflexivity.
  - set (le3 := PTree.set _t'3 (Vint x0) le2).
    assert (HIf1 : forall s1 s2 le' ,
      Clight2.exec_stmt sha_ge e le2 m s2 E0 le' m Out_normal ->
      Clight2.exec_stmt sha_ge e le2 m
        (Sifthenelse (Ebinop Oeq (Econst_int (Int.repr 1) tint) (Etempvar _t'2 tuchar) tint) s1 s2)
        E0 le' m Out_normal).
    { intros s1 s2 le' HE. eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
      - eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; apply PTree.gss|].
        cbn. unfold Cop.sem_cmp, Cop.sem_binarith. cbn. rewrite H1. reflexivity.
      - reflexivity.
      - exact HE. }
    destruct (Int.eq (Int.repr 1) (Int.and (Int.repr 1) x0)) eqn:H2.
    + exists (PTree.set _t'1 (Vint (Int.repr 3)) (PTree.set _t'1 (Vint (Int.repr 3)) le3)).
      split; [|split; [|split]].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m).
        { apply exec_Sset. apply rc_raw0; assumption. }
        apply HIf1.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m).
        { apply exec_Sset. apply rc_raw0; assumption. }
        eapply exec_Sifthenelse with (v1 := Vtrue) (b := true).
        -- eapply eval_Ebinop; [apply eval_Econst_int| |].
           ++ eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; apply PTree.gss|reflexivity].
           ++ cbn. unfold Cop.sem_cmp, Cop.sem_binarith. cbn. rewrite H2. reflexivity.
        -- reflexivity.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
           ++ apply exec_Sset. eapply eval_Ecast; [apply eval_Etempvar; apply PTree.gss|reflexivity].
      * apply PTree.gss.
      * unfold le3, le2. rewrite !PTree.gso by discriminate. reflexivity.
      * unfold le3, le2. rewrite !PTree.gso by discriminate. reflexivity.
    + exists (PTree.set _t'1 (Vint (Int.repr 2)) (PTree.set _t'1 (Vint (Int.repr 2)) le3)).
      split; [|split; [|split]].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m).
        { apply exec_Sset. apply rc_raw0; assumption. }
        apply HIf1.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m).
        { apply exec_Sset. apply rc_raw0; assumption. }
        eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
        -- eapply eval_Ebinop; [apply eval_Econst_int| |].
           ++ eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; apply PTree.gss|reflexivity].
           ++ cbn. unfold Cop.sem_cmp, Cop.sem_binarith. cbn. rewrite H2. reflexivity.
        -- reflexivity.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
           ++ apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
           ++ apply exec_Sset. eapply eval_Ecast; [apply eval_Etempvar; apply PTree.gss|reflexivity].
      * apply PTree.gss.
      * unfold le3, le2. rewrite !PTree.gso by discriminate. reflexivity.
      * unfold le3, le2. rewrite !PTree.gso by discriminate. reflexivity.
Qed.

Lemma rc_add0 (o : ptrofs) : Ptrofs.add o (Ptrofs.repr 0) = o.
Proof. change (Ptrofs.repr 0) with Ptrofs.zero. apply Ptrofs.add_zero. Qed.

Lemma rc_conf_data_value e le m :
  le!_conf = Some confv ->
  eval_expr sha_ge e le m (Efield (Ederef (Etempvar _conf (tptr CONF)) CONF) _data RMID) confv.
Proof.
  intros HC. unfold confv. rewrite <- (rc_add0 (Ptrofs.repr oconf)).
  eapply eval_envu_field_struct;
    [reflexivity|exact envu_confidential_data|apply eval_envu_deref_struct; exact HC].
Qed.

Lemma rc_conf_mid_value e le m :
  le!_conf = Some confv ->
  eval_expr sha_ge e le m
    (Efield (Efield (Ederef (Etempvar _conf (tptr CONF)) CONF) _data RMID) _s RA8) confv.
Proof.
  intros HC. unfold confv. rewrite <- (rc_add0 (Ptrofs.repr oconf)).
  eapply eval_envu_field_array;
    [reflexivity|exact envu_sha256_midstate_s|intros ch; discriminate|reflexivity
    |apply rc_conf_data_value; exact HC].
Qed.

(** [rawConf != NULL]: the prefix by the first byte and the midstate of the
    32 bytes after it. *)
Theorem eval_copyRawConfidential_raw m :
  Mem.range_perm m bconf oconf (oconf + 36) Cur Writable ->
  Ptrofs.unsigned oraw + 33 <= Ptrofs.max_unsigned ->
  (forall i, (i < 33)%nat ->
     Mem.load Mint8unsigned m braw (Ptrofs.unsigned oraw + Z.of_nat i) = Some (Vint (nth i bs Int.zero))) ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_copyRawConfidential) [confv; rawv] E0 m' Vundef /\
    rc_post m m' (conf_prefix (nth 0 bs Int.zero)) (tm_words (tl bs)).
Proof.
  intros PR HrM HB.
  set (x0 := nth 0 bs Int.zero) in *.
  assert (Vc : Mem.valid_block m bconf) by (eapply Mem.perm_valid_block; apply (PR oconf); lia).
  assert (Vr : Mem.valid_block m braw).
  { pose proof (Mem.load_valid_access _ _ _ _ _ (HB 0%nat ltac:(lia))) as [HRg _].
    eapply Mem.perm_valid_block. apply (HRg (Ptrofs.unsigned oraw + Z.of_nat 0)). cbn. lia. }
  assert (Ho1 : Ptrofs.unsigned o1 = Ptrofs.unsigned oraw + 1) by (unfold o1; apply ptr_byte_offset; lia).
  destruct (Mem.alloc m 0 36) as [m0a bC1] eqn:A1.
  destruct (Mem.alloc m0a 0 36) as [m0 bC2] eqn:A2.
  set (e := rc_env bC1 bC2).
  set (le0 := PTree.set _rawConf rawv
    (PTree.set _conf confv (create_undef_temps (fn_temps f_copyRawConfidential)))).
  assert (HeC : e!___compound = Some (bC1, CONF)) by reflexivity.
  assert (NCc : bC1 <> bconf) by (apply not_eq_sym, (rc_fresh1 _ _ _ A1), Vc).
  assert (Nr1 : braw <> bC1) by (apply (rc_fresh1 _ _ _ A1), Vr).
  assert (PC : Mem.range_perm m0 bC1 0 36 Cur Writable).
  { intros o Ho. eapply Mem.perm_implies; [apply (rc_permC1 _ _ _ _ _ A1 A2), Ho|constructor]. }
  assert (PR0 : Mem.range_perm m0 bconf oconf (oconf + 36) Cur Writable).
  { intros o Ho. apply (rc_perm0 _ _ _ _ _ A1 A2), PR, Ho. }
  assert (HB0 : forall i, (i < 33)%nat ->
    Mem.load Mint8unsigned m0 braw (Ptrofs.unsigned oraw + Z.of_nat i) = Some (Vint (nth i bs Int.zero))).
  { intros i Hi. rewrite (rc_load0 _ _ _ _ _ A1 A2) by exact Vr. exact (HB i Hi). }
  pose proof (HB0 0%nat ltac:(lia)) as HL0. rewrite Z.add_0_r in HL0. fold x0 in HL0.
  destruct rc_zeros_exec with (e := e) (cid := ___compound) (bC := bC1) (le := le0) (m := m0)
    as (mW & SW & HZ); try assumption.
  assert (HL0W : Mem.load Mint8unsigned mW braw (Ptrofs.unsigned oraw) = Some (Vint x0)).
  { rewrite (store_words_load_other _ _ _ _ _ SW) by (left; exact Nr1). exact HL0. }
  destruct (rc_compute_exec e le0 mW x0 eq_refl HL0W) as (le1 & HC & Ht1 & Hc1 & Hr1).
  destruct rc_tail_exec with (e := e) (cid := ___compound) (bC := bC1) (le := le1) (m := m0) (mW := mW)
    (rhs := Etempvar _t'1 tint) (pfx := conf_prefix x0)
    as (mF & mG & HPa & HCp & HW & HP & HL & HPm & HV);
    try assumption; try reflexivity; [intros; apply eval_Etempvar; exact Ht1|].
  destruct (eval_sha256_toMidstate bconf braw (Ptrofs.repr oconf) o1 (tl bs) (not_eq_sym Hdiff))
    with (m := mG) as (mT & HSt & HCall).
  { rewrite Ho1. lia. }
  { rewrite Ptrofs.unsigned_repr by lia. lia. }
  { rewrite Ptrofs.unsigned_repr by lia. exact HoA. }
  { intros i Hi. rewrite Ho1, nth_tl.
    rewrite HL by (exact Nr1 || (left; exact Hdiff)).
    replace (Ptrofs.unsigned oraw + 1 + Z.of_nat i) with (Ptrofs.unsigned oraw + Z.of_nat (S i)) by lia.
    apply HB0. lia. }
  { rewrite Ptrofs.unsigned_repr by lia. intros o Ho. apply HPm, PR0. lia. }
  rewrite Ptrofs.unsigned_repr in HSt by lia.
  assert (HLen : Z.of_nat (length (tm_words (tl bs))) = 8).
  { unfold tm_words. rewrite map_length, seq_length. reflexivity. }
  destruct (rc_leave m m0a m0 bC1 bC2 A1 A2 mT) as (mf & HFL & HLf & HPf & HVf).
  { intros b ofs k p Hp. apply (store_words_perm _ _ _ _ _ HSt), HPm, Hp. }
  exists mf. split.
  - eapply eval_funcall_internal with (e := e) (le1 := le0) (m1 := m0) (le2 := le1) (m2 := mT) (out := Out_normal).
    + eapply rc_entry; [exact A1|exact A2].
    + rewrite rc_body_shape.
      eapply exec_Sifthenelse with (v1 := rawv) (b := true).
      * apply eval_Etempvar. reflexivity.
      * change (Cop.bool_val rawv (typeof (Etempvar _rawConf (tptr tuchar))) m0) with
          (if Mem.weak_valid_pointer m0 braw (Ptrofs.unsigned oraw) then Some true else None).
        rewrite (load_weak_valid _ _ _ _ HL0). reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mG).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mF); [|exact HCp].
           eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mW); [|exact HPa].
           eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := mW); [exact HZ|exact HC].
        -- unfold rc_call.
           eapply te_call_toMidstate with (bm := bconf) (om := Ptrofs.repr oconf) (bh := braw) (oh := o1);
             [reflexivity|apply rc_conf_mid_value; rewrite Hc1; reflexivity|reflexivity| |reflexivity|exact HCall].
           eapply eval_Ebinop; [apply eval_Etempvar; rewrite Hr1; reflexivity|apply eval_Econst_int|reflexivity].
    + cbn. reflexivity.
    + exact HFL.
  - split; [|split; [|split; [|split]]].
    + intros i x Hi. rewrite HLf by exact Vc. exact (store_words_loads _ _ _ _ _ HSt i x Hi).
    + rewrite HLf by exact Vc.
      rewrite (store_words_load_other _ _ _ _ _ HSt) by (right; right; lia). exact HP.
    + intros ch b ofs Hb Hr. rewrite HLf by exact Hb.
      rewrite (store_words_load_other _ _ _ _ _ HSt)
        by (destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; exact Hr|right; right; lia]).
      rewrite HL by (exact Hr || apply (rc_fresh1 _ _ _ A1), Hb).
      apply (rc_load0 _ _ _ _ _ A1 A2). exact Hb.
    + intros b ofs k p Hb Hp. apply HPf; [exact Hb|].
      apply (store_words_perm _ _ _ _ _ HSt), HPm, (rc_perm0 _ _ _ _ _ A1 A2), Hp.
    + intros b Hb. apply HVf. unfold Mem.valid_block. rewrite (store_words_nextblock _ _ _ _ _ HSt).
      apply HV, (rc_valid0 _ _ _ _ _ A1 A2), Hb.
Qed.
End Raw.
End CopyRawConfidential.
