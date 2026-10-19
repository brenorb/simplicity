(** Execution of [copyRawAmt(amt, rawAmt)] (elements/env.c), the reader of
    every amount of a raw Elements transaction:
      rawAmt == NULL          amt = { EXPLICIT, 0 }
      rawAmt[0] == 0x01       amt = { EXPLICIT, ReadBE64(rawAmt + 1) }
      otherwise               amt = { ODD_Y or EVEN_Y by the low bit of
                                      rawAmt[0], midstate of rawAmt[1..32] }
    First step towards [simplicity_elements_mallocTransaction]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_uint32_array_init.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_be32_exec.
Require Import C.jet_env_store_words C.jet_elements_env_field_eval C.jet_elements_env_tomidstate.
Require Import C.jet_elements_env_tapenv_key C.jet_elements_env_readbe64.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Notation CAMT := (Tstruct _confAmount noattr).
Notation amt_union := (18727075383868559167%positive) (only parsing).

(** A member of a union of the unit, at its (zero) offset. *)
Definition envu_union_at (uid field : ident) (delta : Z) : Prop :=
  match (Clight.genv_cenv sha_ge)!uid with
  | Some co => union_field_offset (Clight.genv_cenv sha_ge) field (co_members co) = OK (delta, Full)
  | None => False
  end.

Lemma envu_confAmount_union : envu_field_at _confAmount amt_union 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_confAmount_prefix : envu_field_at _confAmount _prefix 32.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_amt_explicit : envu_union_at __4799 _explicit 0.
Proof. vm_compute; reflexivity. Qed.
Lemma envu_amt_confidential : envu_union_at __4799 _confidential 0.
Proof. vm_compute; reflexivity. Qed.

Lemma sha_ReadBE64_call_type :
  classify_fun (Tfunction (Tcons (tptr tuchar) Tnil) tulong cc_default) =
    fun_case_f (Tcons (tptr tuchar) Tnil) tulong cc_default.
Proof. reflexivity. Qed.

Local Opaque sha_ge.

Lemma eval_envu_union_lvalue e le m a uid field delta ty b ofs :
  typeof a = Tunion uid noattr -> envu_union_at uid field delta ->
  eval_expr sha_ge e le m a (Vptr b ofs) ->
  eval_lvalue sha_ge e le m (Efield a field ty) b (Ptrofs.add ofs (Ptrofs.repr delta)) Full.
Proof.
  intros HT HF HA. unfold envu_union_at in HF.
  destruct ((Clight.genv_cenv sha_ge)!uid) as [co|] eqn:HCo; [|contradiction].
  eapply eval_Efield_union with (co := co) (delta := delta); eauto.
Qed.

Lemma nth_tl {A} (l : list A) i d : nth i (tl l) d = nth (S i) l d.
Proof. destruct l; destruct i; reflexivity. Qed.

Lemma load_weak_valid m b ofs v :
  Mem.load Mint8unsigned m b ofs = Some v -> Mem.weak_valid_pointer m b ofs = true.
Proof.
  intros HL. unfold Mem.weak_valid_pointer. apply orb_true_iff. left.
  apply Mem.valid_pointer_nonempty_perm. eapply Mem.perm_implies; [|apply perm_any_N].
  apply (proj1 (Mem.load_valid_access _ _ _ _ _ HL)). cbn. lia.
Qed.

(** The prefix values (elements/txEnv.h). *)
Definition amt_parity (x0 : int) : int :=
  if Int.eq (Int.repr 1) (Int.and (Int.repr 1) x0) then Int.repr 3 else Int.repr 2.

Section CopyRawAmt.
Variables (bamt : block) (oamt : Z).
Hypothesis Ho0 : 0 <= oamt.
Hypothesis HoM : oamt + 40 <= Ptrofs.max_unsigned.
Hypothesis HoA : (8 | oamt).

Let amtv := Vptr bamt (Ptrofs.repr oamt).

Lemma amt_add0 (o : ptrofs) : Ptrofs.add o (Ptrofs.repr 0) = o.
Proof. change (Ptrofs.repr 0) with Ptrofs.zero. apply Ptrofs.add_zero. Qed.

Lemma amt_prefix_lvalue le m :
  le!_amt = Some amtv ->
  eval_lvalue sha_ge empty_env le m
    (Efield (Ederef (Etempvar _amt (tptr CAMT)) CAMT) _prefix tint)
    bamt (Ptrofs.repr (oamt + 32)) Full.
Proof.
  intros HA. rewrite <- (envu_ptr_add_repr oamt 32) by lia.
  eapply eval_envu_field_lvalue;
    [reflexivity|exact envu_confAmount_prefix|apply eval_envu_deref_struct; exact HA].
Qed.

Lemma amt_union_value le m :
  le!_amt = Some amtv ->
  eval_expr sha_ge empty_env le m
    (Efield (Ederef (Etempvar _amt (tptr CAMT)) CAMT) amt_union (Tunion __4799 noattr))
    amtv.
Proof.
  intros HA. unfold amtv. rewrite <- (amt_add0 (Ptrofs.repr oamt)).
  eapply eval_Elvalue.
  - eapply eval_envu_field_lvalue;
      [reflexivity|exact envu_confAmount_union|apply eval_envu_deref_struct; exact HA].
  - apply deref_loc_copy; reflexivity.
Qed.

Lemma amt_explicit_lvalue le m :
  le!_amt = Some amtv ->
  eval_lvalue sha_ge empty_env le m
    (Efield (Efield (Ederef (Etempvar _amt (tptr CAMT)) CAMT) amt_union (Tunion __4799 noattr))
       _explicit tulong)
    bamt (Ptrofs.repr oamt) Full.
Proof.
  intros HA. rewrite <- (amt_add0 (Ptrofs.repr oamt)).
  eapply eval_envu_union_lvalue; [reflexivity|exact envu_amt_explicit|apply amt_union_value; exact HA].
Qed.

Lemma amt_conf_value le m :
  le!_amt = Some amtv ->
  eval_expr sha_ge empty_env le m
    (Efield (Efield (Ederef (Etempvar _amt (tptr CAMT)) CAMT) amt_union (Tunion __4799 noattr))
       _confidential (Tstruct _sha256_midstate noattr))
    amtv.
Proof.
  intros HA. unfold amtv. rewrite <- (amt_add0 (Ptrofs.repr oamt)).
  eapply eval_Elvalue.
  - eapply eval_envu_union_lvalue;
      [reflexivity|exact envu_amt_confidential|apply amt_union_value; exact HA].
  - apply deref_loc_copy; reflexivity.
Qed.

Lemma amt_mid_value le m :
  le!_amt = Some amtv ->
  eval_expr sha_ge empty_env le m
    (Efield (Efield (Efield (Ederef (Etempvar _amt (tptr CAMT)) CAMT) amt_union (Tunion __4799 noattr))
       _confidential (Tstruct _sha256_midstate noattr)) _s (tarray tuint 8))
    amtv.
Proof.
  intros HA. unfold amtv. rewrite <- (amt_add0 (Ptrofs.repr oamt)).
  eapply eval_Elvalue.
  - eapply eval_envu_field_lvalue;
      [reflexivity|exact envu_sha256_midstate_s|apply amt_conf_value; exact HA].
  - apply deref_loc_reference; reflexivity.
Qed.

Definition amt_le (rawv : val) : temp_env :=
  PTree.set _rawAmt rawv (PTree.set _amt amtv (create_undef_temps (fn_temps f_copyRawAmt))).

Lemma amt_entry m rawv :
  function_entry2 sha_ge f_copyRawAmt [amtv; rawv] m empty_env (amt_le rawv) m.
Proof.
  apply function_entry2_intro.
  - apply list_norepet_nil.
  - repeat constructor; simpl; intuition discriminate.
  - intros x0 y0 HX HY; cbn in HX, HY; intuition (subst; discriminate).
  - apply alloc_variables_nil.
  - reflexivity.
Qed.

Lemma amt_align32 : (4 | oamt + 32).
Proof. destruct HoA as [k ->]. exists (2 * k + 8). lia. Qed.

(** The two stores of an explicit amount. *)
Lemma amt_explicit_stores m (v : int64) :
  Mem.range_perm m bamt oamt (oamt + 40) Cur Writable ->
  exists m1 m2,
    Mem.store Mint32 m bamt (oamt + 32) (Vint (Int.repr 1)) = Some m1 /\
    Mem.store Mint64 m1 bamt oamt (Vlong v) = Some m2.
Proof.
  intros PR.
  destruct (Mem.valid_access_store m Mint32 bamt (oamt + 32) (Vint (Int.repr 1))) as [m1 HS1].
  { split; [|exact amt_align32]. intros o Ho. change (size_chunk Mint32) with 4 in Ho. apply PR. lia. }
  destruct (Mem.valid_access_store m1 Mint64 bamt oamt (Vlong v)) as [m2 HS2].
  { split; [|exact HoA]. intros o Ho. change (size_chunk Mint64) with 8 in Ho.
    eapply Mem.perm_store_1; [exact HS1|]. apply PR. lia. }
  exists m1, m2. split; assumption.
Qed.

Definition amt_post_explicit (m m' : mem) (v : int64) : Prop :=
  Mem.load Mint32 m' bamt (oamt + 32) = Some (Vint (Int.repr 1)) /\
  Mem.load Mint64 m' bamt oamt = Some (Vlong v) /\
  (forall ch b ofs, b <> bamt \/ ofs + size_chunk ch <= oamt \/ oamt + 40 <= ofs ->
     Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
  (forall b ofs k p, Mem.perm m' b ofs k p <-> Mem.perm m b ofs k p) /\
  Mem.nextblock m' = Mem.nextblock m.

Lemma amt_explicit_post m m1 m2 v :
  Mem.store Mint32 m bamt (oamt + 32) (Vint (Int.repr 1)) = Some m1 ->
  Mem.store Mint64 m1 bamt oamt (Vlong v) = Some m2 ->
  amt_post_explicit m m2 v.
Proof.
  intros HS1 HS2. split; [|split; [|split; [|split]]].
  - rewrite (Mem.load_store_other _ _ _ _ _ _ HS2)
      by (right; right; change (size_chunk Mint64) with 8; lia).
    rewrite (Mem.load_store_same _ _ _ _ _ _ HS1). reflexivity.
  - rewrite (Mem.load_store_same _ _ _ _ _ _ HS2). reflexivity.
  - intros ch b ofs Hr.
    rewrite (Mem.load_store_other _ _ _ _ _ _ HS2)
      by (destruct Hr as [Hr|[Hr|Hr]];
          [left; exact Hr|right; left; exact Hr|right; right; change (size_chunk Mint64) with 8; lia]).
    apply (Mem.load_store_other _ _ _ _ _ _ HS1).
    destruct Hr as [Hr|[Hr|Hr]];
      [left; exact Hr|right; left; lia|right; right; change (size_chunk Mint32) with 4; lia].
  - intros b ofs k p. split; intros Hp.
    + eapply Mem.perm_store_2; [exact HS1|]. eapply Mem.perm_store_2; [exact HS2|exact Hp].
    + eapply Mem.perm_store_1; [exact HS2|]. eapply Mem.perm_store_1; [exact HS1|exact Hp].
  - rewrite (Mem.nextblock_store _ _ _ _ _ _ HS2). apply (Mem.nextblock_store _ _ _ _ _ _ HS1).
Qed.

(** [rawAmt == NULL]: the explicit amount zero. *)
Theorem eval_copyRawAmt_null m :
  Mem.range_perm m bamt oamt (oamt + 40) Cur Writable ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_copyRawAmt) [amtv; Vlong Int64.zero] E0 m' Vundef /\
    amt_post_explicit m m' Int64.zero.
Proof.
  intros PR. destruct (amt_explicit_stores m Int64.zero PR) as (m1 & m2 & HS1 & HS2).
  exists m2. split; [|exact (amt_explicit_post _ _ _ _ HS1 HS2)].
  set (le := amt_le (Vlong Int64.zero)).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le) (m1 := m) (m2 := m2)
    (le2 := le) (out := Out_normal).
  - apply amt_entry.
  - unfold f_copyRawAmt. cbn [fn_body].
    eapply exec_Sifthenelse with (v1 := Vlong Int64.zero) (b := false).
    + apply eval_Etempvar. reflexivity.
    + reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m1).
      * eapply exec_Sassign with (v2 := Vint (Int.repr 1)) (v := Vint (Int.repr 1)).
        -- apply amt_prefix_lvalue. reflexivity.
        -- apply eval_Econst_int.
        -- reflexivity.
        -- eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
           rewrite Ptrofs.unsigned_repr by lia. exact HS1.
      * eapply exec_Sassign with (v2 := Vint (Int.repr 0)) (v := Vlong Int64.zero).
        -- apply amt_explicit_lvalue. reflexivity.
        -- apply eval_Econst_int.
        -- reflexivity.
        -- eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
           rewrite Ptrofs.unsigned_repr by lia. exact HS2.
  - cbn. reflexivity.
  - reflexivity.
Qed.

Section Raw.
Variables (braw : block) (oraw : ptrofs) (bs : list int).
Hypothesis Hdiff : braw <> bamt.

Let rawv := Vptr braw oraw.
Let o1 := Ptrofs.add oraw (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1))).

Lemma amt_raw0 le m x :
  le!_rawAmt = Some rawv ->
  Mem.load Mint8unsigned m braw (Ptrofs.unsigned oraw) = Some (Vint x) ->
  eval_expr sha_ge empty_env le m
    (Ederef (Ebinop Oadd (Etempvar _rawAmt (tptr tuchar)) (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
    (Vint x).
Proof.
  intros HR HL. pose proof (Ptrofs.unsigned_range_2 oraw) as HO. eapply eval_Elvalue.
  - eapply eval_Ederef. eapply eval_Ebinop; [apply eval_Etempvar; exact HR|apply eval_Econst_int|reflexivity].
  - eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv.
    rewrite ptr_byte_offset by lia. rewrite Z.add_0_r. exact HL.
Qed.

Lemma amt_raw1 le m :
  le!_rawAmt = Some rawv ->
  eval_expr sha_ge empty_env le m
    (Ebinop Oadd (Etempvar _rawAmt (tptr tuchar)) (Econst_int (Int.repr 1) tint) (tptr tuchar))
    (Vptr braw o1).
Proof.
  intros HR. eapply eval_Ebinop; [apply eval_Etempvar; exact HR|apply eval_Econst_int|reflexivity].
Qed.

Lemma amt_o1 : Ptrofs.unsigned oraw + 1 <= Ptrofs.max_unsigned -> Ptrofs.unsigned o1 = Ptrofs.unsigned oraw + 1.
Proof. intros H. unfold o1. apply ptr_byte_offset; lia. Qed.

Lemma amt_if_raw m le s1 s2 t le' m' out x :
  le!_rawAmt = Some rawv ->
  Mem.load Mint8unsigned m braw (Ptrofs.unsigned oraw) = Some (Vint x) ->
  Clight2.exec_stmt sha_ge empty_env le m s1 t le' m' out ->
  Clight2.exec_stmt sha_ge empty_env le m (Sifthenelse (Etempvar _rawAmt (tptr tuchar)) s1 s2) t le' m' out.
Proof.
  intros HR HL HE. eapply exec_Sifthenelse with (v1 := rawv) (b := true).
  - apply eval_Etempvar. exact HR.
  - change (Cop.bool_val rawv (typeof (Etempvar _rawAmt (tptr tuchar))) m) with
      (if Mem.weak_valid_pointer m braw (Ptrofs.unsigned oraw) then Some true else None).
    rewrite (load_weak_valid _ _ _ _ HL). reflexivity.
  - exact HE.
Qed.

(** [rawAmt[0] == 0x01]: the explicit amount read from the next eight bytes. *)
Theorem eval_copyRawAmt_explicit m :
  Mem.range_perm m bamt oamt (oamt + 40) Cur Writable ->
  Ptrofs.unsigned oraw + 9 <= Ptrofs.max_unsigned ->
  (forall i, (i < 9)%nat ->
     Mem.load Mint8unsigned m braw (Ptrofs.unsigned oraw + Z.of_nat i) = Some (Vint (nth i bs Int.zero))) ->
  nth 0 bs Int.zero = Int.repr 1 ->
  let v := c_be64 (nth 1 bs Int.zero) (nth 2 bs Int.zero) (nth 3 bs Int.zero) (nth 4 bs Int.zero)
                  (nth 5 bs Int.zero) (nth 6 bs Int.zero) (nth 7 bs Int.zero) (nth 8 bs Int.zero) in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_copyRawAmt) [amtv; rawv] E0 m' Vundef /\
    amt_post_explicit m m' v.
Proof.
  intros PR HrM HB H0 v. destruct (amt_explicit_stores m v PR) as (m1 & m2 & HS1 & HS2).
  exists m2. split; [|exact (amt_explicit_post _ _ _ _ HS1 HS2)].
  pose proof (HB 0%nat ltac:(lia)) as HL0. rewrite Z.add_0_r, H0 in HL0.
  assert (HB1 : forall i, (i < 9)%nat ->
    Mem.load Mint8unsigned m1 braw (Ptrofs.unsigned oraw + Z.of_nat i) = Some (Vint (nth i bs Int.zero))).
  { intros i Hi. rewrite (Mem.load_store_other _ _ _ _ _ _ HS1) by (left; exact Hdiff). exact (HB i Hi). }
  pose proof (amt_o1 ltac:(lia)) as Ho1.
  set (le := amt_le rawv).
  set (le3 := PTree.set _t'3 (Vint (Int.repr 1)) le).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le) (m1 := m) (m2 := m2)
    (le2 := PTree.set _t'1 (Vlong v) le3) (out := Out_normal).
  - apply amt_entry.
  - unfold f_copyRawAmt. cbn [fn_body].
    eapply amt_if_raw; [reflexivity|exact HL0|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m).
    { apply exec_Sset. apply amt_raw0; [reflexivity|exact HL0]. }
    eapply exec_Sifthenelse with (v1 := Vtrue) (b := true).
    + eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; reflexivity|reflexivity].
    + reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m1).
      * eapply exec_Sassign with (v2 := Vint (Int.repr 1)) (v := Vint (Int.repr 1)).
        -- apply amt_prefix_lvalue. reflexivity.
        -- apply eval_Econst_int.
        -- reflexivity.
        -- eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
           rewrite Ptrofs.unsigned_repr by lia. exact HS1.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := PTree.set _t'1 (Vlong v) le3) (m1 := m1).
        -- change (PTree.set _t'1 (Vlong v) le3) with (set_opttemp (Some _t'1) (Vlong v) le3).
           eapply exec_Scall with (vf := Vptr (sha_symbol_block _ReadBE64) Ptrofs.zero)
             (vargs := [Vptr braw o1]) (f := Internal f_ReadBE64).
           ++ exact sha_ReadBE64_call_type.
           ++ eapply eval_Elvalue; [apply eval_Evar_global; [apply PTree.gempty|exact sha_ReadBE64_symbol]|].
              apply deref_loc_reference; reflexivity.
           ++ eapply eval_Econs; [apply amt_raw1; reflexivity|reflexivity|apply eval_Enil].
           ++ exact sha_ReadBE64_funct.
           ++ reflexivity.
           ++ unfold v. apply eval_sha_ReadBE64; rewrite Ho1; try lia.
              ** exact (HB1 1%nat ltac:(lia)).
              ** replace (Ptrofs.unsigned oraw + 1 + 1) with (Ptrofs.unsigned oraw + Z.of_nat 2) by lia. apply HB1; lia.
              ** replace (Ptrofs.unsigned oraw + 1 + 2) with (Ptrofs.unsigned oraw + Z.of_nat 3) by lia. apply HB1; lia.
              ** replace (Ptrofs.unsigned oraw + 1 + 3) with (Ptrofs.unsigned oraw + Z.of_nat 4) by lia. apply HB1; lia.
              ** replace (Ptrofs.unsigned oraw + 1 + 4) with (Ptrofs.unsigned oraw + Z.of_nat 5) by lia. apply HB1; lia.
              ** replace (Ptrofs.unsigned oraw + 1 + 5) with (Ptrofs.unsigned oraw + Z.of_nat 6) by lia. apply HB1; lia.
              ** replace (Ptrofs.unsigned oraw + 1 + 6) with (Ptrofs.unsigned oraw + Z.of_nat 7) by lia. apply HB1; lia.
              ** replace (Ptrofs.unsigned oraw + 1 + 7) with (Ptrofs.unsigned oraw + Z.of_nat 8) by lia. apply HB1; lia.
        -- eapply exec_Sassign with (v2 := Vlong v) (v := Vlong v).
           ++ apply amt_explicit_lvalue. reflexivity.
           ++ apply eval_Etempvar. apply PTree.gss.
           ++ reflexivity.
           ++ eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
              rewrite Ptrofs.unsigned_repr by lia. exact HS2.
  - cbn. reflexivity.
  - reflexivity.
Qed.

(** Otherwise: a confidential amount, its parity and the midstate of the
    32 bytes after the prefix byte. *)
Theorem eval_copyRawAmt_confidential m :
  Mem.range_perm m bamt oamt (oamt + 40) Cur Writable ->
  Ptrofs.unsigned oraw + 33 <= Ptrofs.max_unsigned ->
  (forall i, (i < 33)%nat ->
     Mem.load Mint8unsigned m braw (Ptrofs.unsigned oraw + Z.of_nat i) = Some (Vint (nth i bs Int.zero))) ->
  nth 0 bs Int.zero <> Int.repr 1 ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_copyRawAmt) [amtv; rawv] E0 m' Vundef /\
    Mem.load Mint32 m' bamt (oamt + 32) = Some (Vint (amt_parity (nth 0 bs Int.zero))) /\
    uint32_array_at m' bamt oamt (tm_words (tl bs)) /\
    (forall ch b ofs, b <> bamt \/ ofs + size_chunk ch <= oamt \/ oamt + 40 <= ofs ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m' b ofs k p <-> Mem.perm m b ofs k p) /\
    Mem.nextblock m' = Mem.nextblock m.
Proof.
  intros PR HrM HB H0.
  set (x0 := nth 0 bs Int.zero) in *.
  pose proof (HB 0%nat ltac:(lia)) as HL0. rewrite Z.add_0_r in HL0. fold x0 in HL0.
  pose proof (amt_o1 ltac:(lia)) as Ho1.
  destruct (Mem.valid_access_store m Mint32 bamt (oamt + 32) (Vint (amt_parity x0))) as [m1 HS1].
  { split; [|exact amt_align32]. intros o Ho. change (size_chunk Mint32) with 4 in Ho. apply PR. lia. }
  destruct (eval_sha256_toMidstate bamt braw (Ptrofs.repr oamt) o1 (tl bs) (not_eq_sym Hdiff))
    with (m := m1) as (m2 & HSt & HCall).
  { rewrite Ho1. lia. }
  { rewrite Ptrofs.unsigned_repr by lia. lia. }
  { rewrite Ptrofs.unsigned_repr by lia. destruct HoA as [k ->]. exists (2 * k). lia. }
  { intros i Hi. rewrite Ho1, nth_tl.
    rewrite (Mem.load_store_other _ _ _ _ _ _ HS1) by (left; exact Hdiff).
    replace (Ptrofs.unsigned oraw + 1 + Z.of_nat i) with (Ptrofs.unsigned oraw + Z.of_nat (S i)) by lia.
    apply HB. lia. }
  { rewrite Ptrofs.unsigned_repr by lia. intros o Ho.
    eapply Mem.perm_store_1; [exact HS1|]. apply PR. lia. }
  rewrite Ptrofs.unsigned_repr in HSt by lia.
  assert (HLen : Z.of_nat (length (tm_words (tl bs))) = 8).
  { unfold tm_words. rewrite map_length, seq_length. reflexivity. }
  exists m2. split; [|split; [|split; [|split; [|split]]]].
  - set (le := amt_le rawv).
    set (le3 := PTree.set _t'3 (Vint x0) le).
    set (le4 := PTree.set _t'4 (Vint x0) le3).
    set (le2 := PTree.set _t'2 (Vint (amt_parity x0)) le4).
    eapply eval_funcall_internal with (e := empty_env) (le1 := le) (m1 := m) (m2 := m2)
      (le2 := le2) (out := Out_normal).
    + apply amt_entry.
    + unfold f_copyRawAmt. cbn [fn_body].
      eapply amt_if_raw; [reflexivity|exact HL0|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m).
      { apply exec_Sset. apply amt_raw0; [reflexivity|exact HL0]. }
      eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
      * eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; reflexivity|].
        cbn. unfold Cop.sem_cmp, Cop.sem_binarith. cbn.
        rewrite Int.eq_false by (intro HE; apply H0; symmetry; exact HE). reflexivity.
      * reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m1).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m).
              { apply exec_Sset. apply amt_raw0; [reflexivity|exact HL0]. }
              unfold le2, amt_parity.
              destruct (Int.eq (Int.repr 1) (Int.and (Int.repr 1) x0)) eqn:HPar.
              ** eapply exec_Sifthenelse with (v1 := Vtrue) (b := true).
                 --- eapply eval_Ebinop; [apply eval_Econst_int| |].
                     +++ eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; reflexivity|reflexivity].
                     +++ cbn. unfold Cop.sem_cmp, Cop.sem_binarith. cbn. rewrite HPar. reflexivity.
                 --- reflexivity.
                 --- apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
              ** eapply exec_Sifthenelse with (v1 := Vfalse) (b := false).
                 --- eapply eval_Ebinop; [apply eval_Econst_int| |].
                     +++ eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; reflexivity|reflexivity].
                     +++ cbn. unfold Cop.sem_cmp, Cop.sem_binarith. cbn. rewrite HPar. reflexivity.
                 --- reflexivity.
                 --- apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
           ++ eapply exec_Sassign with (v2 := Vint (amt_parity x0)) (v := Vint (amt_parity x0)).
              ** apply amt_prefix_lvalue. reflexivity.
              ** apply eval_Etempvar. apply PTree.gss.
              ** reflexivity.
              ** eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
                 rewrite Ptrofs.unsigned_repr by lia. exact HS1.
        -- eapply te_call_toMidstate with (bm := bamt) (om := Ptrofs.repr oamt) (bh := braw) (oh := o1);
             [apply PTree.gempty|apply amt_mid_value; reflexivity|reflexivity
             |apply amt_raw1; reflexivity|reflexivity|exact HCall].
    + cbn. reflexivity.
    + reflexivity.
  - rewrite (store_words_load_other _ _ _ _ _ HSt) by (right; right; lia).
    rewrite (Mem.load_store_same _ _ _ _ _ _ HS1). reflexivity.
  - exact (store_words_loads _ _ _ _ _ HSt).
  - intros ch b ofs Hr.
    rewrite (store_words_load_other _ _ _ _ _ HSt)
      by (destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; exact Hr|right; right; lia]).
    apply (Mem.load_store_other _ _ _ _ _ _ HS1).
    destruct Hr as [Hr|[Hr|Hr]];
      [left; exact Hr|right; left; lia|right; right; change (size_chunk Mint32) with 4; lia].
  - intros b ofs k p. rewrite (store_words_perm _ _ _ _ _ HSt). split; intros Hp.
    + eapply Mem.perm_store_2; [exact HS1|exact Hp].
    + eapply Mem.perm_store_1; [exact HS1|exact Hp].
  - rewrite (store_words_nextblock _ _ _ _ _ HSt). apply (Mem.nextblock_store _ _ _ _ _ _ HS1).
Qed.
End Raw.
End CopyRawAmt.
