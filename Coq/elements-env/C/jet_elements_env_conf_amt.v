(** Execution of [simplicity_sha256_confAmt(ctx, amt)] (elements/ops.c) on
    a live SHA-256 context: the context absorbs [amt_bytes], 0x01 and the
    big-endian explicit amount, or 0x08/0x09 (even/odd) and the 32 bytes of
    the commitment.  The prefix NONE is excluded: the C code marks it
    unreachable. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_add_n_init C.jet_sha_hash_exec.
Require Import C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_uchars_prep.
Require Import C.jet_elements_env_field_eval C.jet_elements_env_ctxs_ops C.jet_elements_env_ctxs_core.
Require Import C.jet_elements_env_tx_calls C.jet_elements_env_copyrawamt C.jet_elements_env_conf_hash.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Local Notation CAMT := (Tstruct _confAmount noattr).
Local Notation amt_union := (18727075383868559167%positive) (only parsing).

Definition ca_switch : statement :=
  ltac:(let b := eval cbv delta [f_simplicity_sha256_confAmt fn_body] beta iota in
                 (fn_body f_simplicity_sha256_confAmt) in
        lazymatch b with Ssequence _ ?s => exact s end).

Lemma ca_body_shape :
  fn_body f_simplicity_sha256_confAmt =
    Ssequence (Sset _t'2 (Efield (Ederef (Etempvar _amt (tptr CAMT)) CAMT) _prefix tint)) ca_switch.
Proof. reflexivity. Qed.

Local Opaque sha_ge.

Definition amt_bytes (pfx : int) (v : int64) (ws : list int) : list int :=
  if Int.eq pfx (Int.repr 1) then Int.repr 1 :: c_be64_bytes v
  else (if Int.eq pfx (Int.repr 2) then Int.repr 8 else Int.repr 9) :: be_bytes ws.

Lemma ca_call_u64be le m m' (a2 : expr) bx (x : int64) vr :
  le!_ctx = Some (Vptr bx (Ptrofs.repr 0)) ->
  eval_expr sha_ge empty_env le m a2 (Vlong x) -> typeof a2 = tulong ->
  Clight2.eval_funcall sha_ge m (Internal f_sha256_u64be) [Vptr bx (Ptrofs.repr 0); Vlong x] E0 m' vr ->
  Clight2.exec_stmt sha_ge empty_env le m
    (Scall None (Evar _sha256_u64be (Tfunction (Tcons CTXP (Tcons tulong Tnil)) tbool cc_default))
       [Etempvar _ctx CTXP; a2]) E0 le m' Out_normal.
Proof.
  intros Hc H2 T2 HC. change le with (set_opttemp None vr le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_u64be) Ptrofs.zero)
    (vargs := [Vptr bx (Ptrofs.repr 0); Vlong x]) (f := Internal f_sha256_u64be).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_u64be_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [apply eval_Etempvar; exact Hc|reflexivity|].
    eapply eval_Econs; [exact H2|rewrite T2; reflexivity|apply eval_Enil].
  - exact sha_u64be_funct.
  - reflexivity.
  - exact HC.
Qed.

Section ConfAmt.
Variable Hmodel : memcpy_model.
Variables (bA : block) (cores : list ctx_core) (live : nat -> Prop) (k : nat).
Variables (bx : block) (ob : Z) (l regs : list int) (c : int64).
Hypothesis Hk : nth_error cores k = Some (bx, ob, l, regs, c).
Hypothesis Hlive : live k.

Variables (ba : block) (oa : Z) (ws : list int) (v : int64).
Hypothesis Hoa : 0 <= oa /\ oa + 40 <= Ptrofs.max_unsigned.
Hypothesis Hws : length ws = 8%nat.
Hypothesis Hax : ba <> bx.
Hypothesis Hsep : ba <> bA \/ oa + 40 <= ob \/ ob + 32 <= oa.

Let ctxv := Vptr bx (Ptrofs.repr 0).
Let amtv := Vptr ba (Ptrofs.repr oa).

Definition ca_le : temp_env :=
  PTree.set _amt amtv (PTree.set _ctx ctxv (create_undef_temps (fn_temps f_simplicity_sha256_confAmt))).

Lemma ca_entry m :
  function_entry2 sha_ge f_simplicity_sha256_confAmt [ctxv; amtv] m empty_env ca_le m.
Proof.
  apply function_entry2_intro.
  - apply list_norepet_nil.
  - repeat constructor; simpl; intuition discriminate.
  - intros x0 y0 HX HY; cbn in HX, HY; intuition (subst; discriminate).
  - apply alloc_variables_nil.
  - reflexivity.
Qed.

Lemma ca_prefix_value le m (pfx : int) :
  le!_amt = Some amtv -> Mem.load Mint32 m ba (oa + 32) = Some (Vint pfx) ->
  eval_expr sha_ge empty_env le m (Efield (Ederef (Etempvar _amt (tptr CAMT)) CAMT) _prefix tint) (Vint pfx).
Proof.
  intros HA HL. eapply eval_envu_field_value;
    [reflexivity|exact envu_confAmount_prefix|reflexivity|apply eval_envu_deref_struct; exact HA|].
  rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|exact HL].
Qed.

Lemma ca_add0 (o : ptrofs) : Ptrofs.add o (Ptrofs.repr 0) = o.
Proof. change (Ptrofs.repr 0) with Ptrofs.zero. apply Ptrofs.add_zero. Qed.

Lemma ca_union_value le m :
  le!_amt = Some amtv ->
  eval_expr sha_ge empty_env le m
    (Efield (Ederef (Etempvar _amt (tptr CAMT)) CAMT) amt_union (Tunion __4799 noattr)) amtv.
Proof.
  intros HA. unfold amtv. rewrite <- (ca_add0 (Ptrofs.repr oa)).
  eapply eval_Elvalue.
  - eapply eval_envu_field_lvalue;
      [reflexivity|exact envu_confAmount_union|apply eval_envu_deref_struct; exact HA].
  - apply deref_loc_copy; reflexivity.
Qed.

Lemma ca_explicit_value le m :
  le!_amt = Some amtv -> Mem.load Mint64 m ba oa = Some (Vlong v) ->
  eval_expr sha_ge empty_env le m
    (Efield (Efield (Ederef (Etempvar _amt (tptr CAMT)) CAMT) amt_union (Tunion __4799 noattr))
       _explicit tulong) (Vlong v).
Proof.
  intros HA HL. eapply eval_Elvalue.
  - eapply eval_envu_union_lvalue; [reflexivity|exact envu_amt_explicit|apply ca_union_value; exact HA].
  - eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv.
    rewrite ca_add0, Ptrofs.unsigned_repr by lia. exact HL.
Qed.

Lemma ca_conf_addr le m :
  le!_amt = Some amtv ->
  eval_expr sha_ge empty_env le m
    (Eaddrof
       (Efield (Efield (Ederef (Etempvar _amt (tptr CAMT)) CAMT) amt_union (Tunion __4799 noattr))
          _confidential MID) (tptr MID)) amtv.
Proof.
  intros HA. unfold amtv. rewrite <- (ca_add0 (Ptrofs.repr oa)).
  eapply eval_Eaddrof.
  eapply eval_envu_union_lvalue; [reflexivity|exact envu_amt_confidential|apply ca_union_value; exact HA].
Qed.

Theorem eval_sha256_confAmt m (pfx : int) :
  LS m bA cores live ->
  Mem.load Mint32 m ba (oa + 32) = Some (Vint pfx) ->
  (pfx = Int.repr 1 /\ Mem.load Mint64 m ba oa = Some (Vlong v)) \/
  ((pfx = Int.repr 2 \/ pfx = Int.repr 3) /\
   forall j, (j < 8)%nat -> Mem.load Mint32 m ba (oa + 4 * Z.of_nat j) = Some (Vint (nth j ws Int.zero))) ->
  let B := amt_bytes pfx v ws in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_sha256_confAmt) [ctxv; amtv] E0 m' Vundef /\
    LS m' bA (upd cores k (bx, ob, fst (absorb_i l regs B), snd (absorb_i l regs B),
                           Int64.add c (Int64.repr (Z.of_nat (length B))))) live /\
    mfrP (opP bA bx ob) m m'.
Proof.
  intros HLS HP Hcase B.
  assert (Va : Mem.valid_block m ba).
  { eapply Mem.perm_valid_block. apply (proj1 (Mem.load_valid_access _ _ _ _ _ HP) (oa + 32)). cbn. lia. }
  set (le2 := PTree.set _t'2 (Vint pfx) ca_le).
  assert (HPre : forall le' m' (outS : outcome),
    Clight2.exec_stmt sha_ge empty_env le2 m
      (seq_of_labeled_statement
         (select_switch (Int.unsigned pfx)
            (match ca_switch with Sswitch _ sl => sl | _ => LSnil end))) E0 le' m' outS ->
    Clight2.exec_stmt sha_ge empty_env ca_le m (fn_body f_simplicity_sha256_confAmt) E0 le' m' (outcome_switch outS)).
  { intros le' m' outS HX. rewrite ca_body_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m).
    - apply exec_Sset. apply ca_prefix_value; [reflexivity|exact HP].
    - cbv delta [ca_switch] beta iota.
      eapply exec_Sswitch with (v := Vint pfx) (n := Int.unsigned pfx);
        [apply eval_Etempvar; apply PTree.gss|reflexivity|exact HX]. }
  destruct Hcase as [(-> & HV)|(Hpfx & HW)].
  - (* explicit *)
    destruct (LS_uchar Hmodel bA cores live k bx ob l regs c Hk Hlive m (Int.repr 1) HLS eq_refl)
      as (m1 & vr1 & HC1 & LS1 & FR1).
    pose proof FR1 as (FL1 & _ & _).
    destruct (LS_u64be Hmodel bA _ live k bx ob _ _ _ (nth_error_upd_same cores k _ _ Hk) Hlive m1 v LS1)
      as (m2 & vr2 & HC2 & LS2 & FR2).
    assert (HV1 : Mem.load Mint64 m1 ba oa = Some (Vlong v)).
    { rewrite FL1; [exact HV|exact Va|]. split; [exact Hax|]. change (size_chunk Mint64) with 8.
      destruct Hsep as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]. }
    exists m2. split; [|split; [|exact (mfrP_trans _ _ _ _ FR1 FR2)]].
    + set (le4 := PTree.set _t'4 (Vlong v) le2).
      eapply eval_funcall_internal with (e := empty_env) (le1 := ca_le) (m1 := m) (m2 := m2) (le2 := le4)
        (out := Out_return None); [apply ca_entry| |reflexivity|reflexivity].
      change (Out_return None) with (outcome_switch (Out_return None)). apply HPre.
      cbn. eapply exec_Sseq_2; [|discriminate].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m1).
      { eapply cf_call_uchar; [reflexivity|apply eval_Econst_int|reflexivity|exact HC1]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m2); [|apply exec_Sreturn_none].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m1).
      { apply exec_Sset. apply ca_explicit_value; [reflexivity|exact HV1]. }
      eapply ca_call_u64be; [reflexivity|apply eval_Etempvar; apply PTree.gss|reflexivity|exact HC2].
    + rewrite upd_upd in LS2. unfold B, amt_bytes. cbn [Int.eq].
      change (Int.eq (Int.repr 1) (Int.repr 1)) with true. cbv iota.
      change (Int.repr 1 :: c_be64_bytes v) with ([Int.repr 1] ++ c_be64_bytes v). rewrite absorb_i_app.
      rewrite Int64.add_assoc in LS2. exact LS2.
  - (* confidential *)
    set (p := if Int.eq pfx (Int.repr 2) then Int.repr 8 else Int.repr 9).
    assert (Hp : Int.zero_ext 8 p = p) by (unfold p; destruct Hpfx as [-> | ->]; reflexivity).
    destruct (LS_uchar Hmodel bA cores live k bx ob l regs c Hk Hlive m p HLS Hp)
      as (m1 & vr1 & HC1 & LS1 & FR1).
    pose proof FR1 as (FL1 & _ & _).
    destruct (LS_hash Hmodel bA _ live k bx ob _ _ _ (nth_error_upd_same cores k _ _ Hk) Hlive m1 ba
      (Ptrofs.repr oa) ws LS1 Hws) as (m2 & HC2 & LS2 & FR2).
    { rewrite Ptrofs.unsigned_repr by lia. lia. }
    { intros j Hj. rewrite Ptrofs.unsigned_repr by lia.
      rewrite FL1; [exact (HW j Hj)|exact Va|].
      split; [exact Hax|]. change (size_chunk Mint32) with 4.
      destruct Hsep as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]. }
    assert (HLen8 : length (be_bytes ws) = 32%nat) by (rewrite be_bytes_length, Hws; reflexivity).
    assert (HB : B = p :: be_bytes ws).
    { unfold B, amt_bytes, p. destruct Hpfx as [-> | ->]; reflexivity. }
    exists m2. split; [|split; [|exact (mfrP_trans _ _ _ _ FR1 FR2)]].
    2: { rewrite upd_upd in LS2. rewrite HB. cbn [length]. rewrite HLen8.
         change (p :: be_bytes ws) with ([p] ++ be_bytes ws). rewrite absorb_i_app.
         rewrite Int64.add_assoc in LS2. exact LS2. }
    set (le3 := PTree.set _t'3 (Vint pfx) le2).
    set (le1 := PTree.set _t'1 (Vint p) le3).
    assert (HCase3 : forall rest,
      Clight2.exec_stmt sha_ge empty_env le2 m
        (Ssequence
           (match ca_switch with
            | Sswitch _ (LScons _ _ (LScons _ _ (LScons _ _ (LScons _ s3 _)))) => s3
            | _ => Sskip
            end) rest) E0 le1 m2 (Out_return None)).
    { intros rest. cbv delta [ca_switch] beta iota.
      eapply exec_Sseq_2; [|discriminate].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m1).
      - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
        + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m).
          * apply exec_Sset. apply ca_prefix_value; [reflexivity|exact HP].
          * unfold le1, p. destruct Hpfx as [-> | ->].
            -- eapply exec_Sifthenelse with (v1 := Vtrue) (b := true);
                 [eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; apply PTree.gss|reflexivity]
                 |reflexivity|].
               apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
            -- eapply exec_Sifthenelse with (v1 := Vfalse) (b := false);
                 [eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; apply PTree.gss|reflexivity]
                 |reflexivity|].
               apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
        + eapply cf_call_uchar with (v2 := Vint p);
            [reflexivity|apply eval_Etempvar; apply PTree.gss| |exact HC1].
          change (Some (Vint (Int.zero_ext 8 p)) = Some (Vint p)). rewrite Hp. reflexivity.
      - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m2); [|apply exec_Sreturn_none].
        eapply cf_call_hash; [reflexivity|apply ca_conf_addr; reflexivity|reflexivity|exact HC2]. }
    eapply eval_funcall_internal with (e := empty_env) (le1 := ca_le) (m1 := m) (m2 := m2) (le2 := le1)
      (out := Out_return None); [apply ca_entry| |reflexivity|reflexivity].
    change (Out_return None) with (outcome_switch (Out_return None)). apply HPre.
    destruct Hpfx as [-> | ->]; cbn.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [apply exec_Sskip|]. apply (HCase3 Sskip).
    + apply (HCase3 Sskip).
Qed.
End ConfAmt.
