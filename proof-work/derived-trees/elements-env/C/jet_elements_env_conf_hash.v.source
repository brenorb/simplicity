(** Execution of [simplicity_sha256_confidential(evenPrefix, oddPrefix, ctx,
    conf)] (elements/ops.c) on a live SHA-256 context: the context absorbs
    [conf_bytes], one prefix byte (0x00 for NONE, 0x01 for EXPLICIT, the
    given even/odd prefix otherwise) followed, unless the value is NONE, by
    the 32 bytes of its data.  This is how every asset and nonce enters the
    hashes of the Elements environment and of the Elements hash jets. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_add_n_init C.jet_sha_hash_exec.
Require Import C.jet_sha_be32_write C.jet_sha_uchars_prep.
Require Import C.jet_elements_env_field_eval C.jet_elements_env_ctxs_ops C.jet_elements_env_ctxs_core.
Require Import C.jet_elements_env_tx_calls C.jet_elements_env_copyrawconf.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Local Notation CONF := (Tstruct _confidential noattr).

Definition cf_switch : statement :=
  ltac:(let b := eval cbv delta [f_simplicity_sha256_confidential fn_body] beta iota in
                 (fn_body f_simplicity_sha256_confidential) in
        lazymatch b with Ssequence (Ssequence _ ?s) _ => exact s end).
Definition cf_last : statement :=
  ltac:(let b := eval cbv delta [f_simplicity_sha256_confidential fn_body] beta iota in
                 (fn_body f_simplicity_sha256_confidential) in
        lazymatch b with Ssequence _ ?s => exact s end).

Lemma cf_body_shape :
  fn_body f_simplicity_sha256_confidential =
    Ssequence
      (Ssequence (Sset _t'1 (Efield (Ederef (Etempvar _conf (tptr CONF)) CONF) _prefix tint)) cf_switch)
      cf_last.
Proof. reflexivity. Qed.

Local Opaque sha_ge.

Lemma upd_upd {A} (l : list A) : forall k x y, upd (upd l k x) k y = upd l k y.
Proof. induction l as [|a l IH]; intros [|k] x y; cbn; try reflexivity. f_equal. apply IH. Qed.

(** The bytes a confidential value contributes. *)
Definition conf_bytes (even odd pfx : int) (ws : list int) : list int :=
  if Int.eq pfx (Int.repr 0) then [Int.repr 0]
  else (if Int.eq pfx (Int.repr 1) then Int.repr 1
        else if Int.eq pfx (Int.repr 2) then even else odd) :: be_bytes ws.

(** Calls through the context pointer parameter. *)
Lemma cf_call_uchar le m m' (a2 : expr) v2 bx x vr :
  le!_ctx = Some (Vptr bx (Ptrofs.repr 0)) ->
  eval_expr sha_ge empty_env le m a2 v2 -> sem_cast v2 (typeof a2) tuchar m = Some (Vint x) ->
  Clight2.eval_funcall sha_ge m (Internal f_sha256_uchar) [Vptr bx (Ptrofs.repr 0); Vint x] E0 m' vr ->
  Clight2.exec_stmt sha_ge empty_env le m
    (Scall None (Evar _sha256_uchar (Tfunction (Tcons CTXP (Tcons tuchar Tnil)) tbool cc_default))
       [Etempvar _ctx CTXP; a2]) E0 le m' Out_normal.
Proof.
  intros Hc H2 HC2 HC. change le with (set_opttemp None vr le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_uchar) Ptrofs.zero)
    (vargs := [Vptr bx (Ptrofs.repr 0); Vint x]) (f := Internal f_sha256_uchar).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_uchar_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [apply eval_Etempvar; exact Hc|reflexivity|].
    eapply eval_Econs; [exact H2|exact HC2|apply eval_Enil].
  - exact sha_uchar_funct.
  - reflexivity.
  - exact HC.
Qed.

Lemma cf_call_hash le m m' (a2 : expr) bx bt ot :
  le!_ctx = Some (Vptr bx (Ptrofs.repr 0)) ->
  eval_expr sha_ge empty_env le m a2 (Vptr bt ot) -> typeof a2 = tptr MID ->
  Clight2.eval_funcall sha_ge m (Internal f_sha256_hash) [Vptr bx (Ptrofs.repr 0); Vptr bt ot] E0 m' Vundef ->
  Clight2.exec_stmt sha_ge empty_env le m
    (Scall None (Evar _sha256_hash (Tfunction (Tcons CTXP (Tcons (tptr MID) Tnil)) tvoid cc_default))
       [Etempvar _ctx CTXP; a2]) E0 le m' Out_normal.
Proof.
  intros Hc H2 T2 HC. change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_hash) Ptrofs.zero)
    (vargs := [Vptr bx (Ptrofs.repr 0); Vptr bt ot]) (f := Internal f_sha256_hash).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_hash_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [apply eval_Etempvar; exact Hc|reflexivity|].
    eapply eval_Econs; [exact H2|rewrite T2; reflexivity|apply eval_Enil].
  - exact sha_hash_funct.
  - reflexivity.
  - exact HC.
Qed.

Section Confidential.
Variable Hmodel : memcpy_model.
Variables (bA : block) (cores : list ctx_core) (live : nat -> Prop) (k : nat).
Variables (bx : block) (ob : Z) (l regs : list int) (c : int64).
Hypothesis Hk : nth_error cores k = Some (bx, ob, l, regs, c).
Hypothesis Hlive : live k.

Variables (bc : block) (oc : Z) (even odd : int) (ws : list int).
Hypothesis Hoc : 0 <= oc /\ oc + 36 <= Ptrofs.max_unsigned.
Hypothesis Heven : Int.zero_ext 8 even = even.
Hypothesis Hodd : Int.zero_ext 8 odd = odd.
Hypothesis Hws : length ws = 8%nat.
Hypothesis Hcx : bc <> bx.
Hypothesis Hsep : bc <> bA \/ oc + 36 <= ob \/ ob + 32 <= oc.

Let ctxv := Vptr bx (Ptrofs.repr 0).
Let confv := Vptr bc (Ptrofs.repr oc).

Definition cf_le : temp_env :=
  PTree.set _conf confv (PTree.set _ctx ctxv (PTree.set _oddPrefix (Vint odd)
    (PTree.set _evenPrefix (Vint even) (create_undef_temps (fn_temps f_simplicity_sha256_confidential))))).

Lemma cf_entry m :
  function_entry2 sha_ge f_simplicity_sha256_confidential [Vint even; Vint odd; ctxv; confv] m empty_env cf_le m.
Proof.
  apply function_entry2_intro.
  - apply list_norepet_nil.
  - repeat constructor; simpl; intuition discriminate.
  - intros x0 y0 HX HY; cbn in HX, HY; intuition (subst; discriminate).
  - apply alloc_variables_nil.
  - reflexivity.
Qed.

Lemma cf_data_addr le m :
  le!_conf = Some confv ->
  eval_expr sha_ge empty_env le m
    (Eaddrof (Efield (Ederef (Etempvar _conf (tptr CONF)) CONF) _data MID) (tptr MID)) confv.
Proof.
  intros HC. unfold confv. replace (Ptrofs.repr oc) with (Ptrofs.add (Ptrofs.repr oc) (Ptrofs.repr 0))
    by (change (Ptrofs.repr 0) with Ptrofs.zero; apply Ptrofs.add_zero).
  eapply eval_Eaddrof. eapply eval_envu_field_lvalue;
    [reflexivity|exact envu_confidential_data|apply eval_envu_deref_struct; exact HC].
Qed.

Lemma cf_prefix_exec m (pfx : int) :
  Mem.load Mint32 m bc (oc + 32) = Some (Vint pfx) ->
  Clight2.exec_stmt sha_ge empty_env cf_le m
    (Sset _t'1 (Efield (Ederef (Etempvar _conf (tptr CONF)) CONF) _prefix tint)) E0
    (PTree.set _t'1 (Vint pfx) cf_le) m Out_normal.
Proof.
  intros HL. apply exec_Sset. eapply eval_envu_field_value;
    [reflexivity|exact envu_confidential_prefix|reflexivity|apply eval_envu_deref_struct; reflexivity|].
  rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|exact HL].
Qed.

(** One prefix byte, then the data. *)
Lemma cf_two_ops m (p : int) :
  LS m bA cores live -> Int.zero_ext 8 p = p ->
  Mem.valid_block m bc ->
  (forall j, (j < 8)%nat -> Mem.load Mint32 m bc (oc + 4 * Z.of_nat j) = Some (Vint (nth j ws Int.zero))) ->
  exists m1 vr m2,
    Clight2.eval_funcall sha_ge m (Internal f_sha256_uchar) [ctxv; Vint p] E0 m1 vr /\
    Clight2.eval_funcall sha_ge m1 (Internal f_sha256_hash) [ctxv; confv] E0 m2 Vundef /\
    LS m2 bA (upd cores k (bx, ob, fst (absorb_i l regs (p :: be_bytes ws)), snd (absorb_i l regs (p :: be_bytes ws)),
                           Int64.add c (Int64.repr 33))) live /\
    mfrP (opP bA bx ob) m m2.
Proof.
  intros HLS Hp Vc HW.
  destruct (LS_uchar Hmodel bA cores live k bx ob l regs c Hk Hlive m p HLS Hp) as (m1 & vr & HC1 & LS1 & FR1).
  pose proof FR1 as (FL1 & _ & _).
  destruct (LS_hash Hmodel bA _ live k bx ob _ _ _ (nth_error_upd_same cores k _ _ Hk) Hlive m1 bc
    (Ptrofs.repr oc) ws LS1 Hws) as (m2 & HC2 & LS2 & FR2).
  { rewrite Ptrofs.unsigned_repr by lia. lia. }
  { intros j Hj. rewrite Ptrofs.unsigned_repr by lia.
    rewrite FL1; [exact (HW j Hj)|exact Vc|].
    split; [exact Hcx|]. change (size_chunk Mint32) with 4.
    destruct Hsep as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]. }
  exists m1, vr, m2. split; [exact HC1|]. split; [exact HC2|]. split; [|exact (mfrP_trans _ _ _ _ FR1 FR2)].
  rewrite upd_upd in LS2.
  change (p :: be_bytes ws) with ([p] ++ be_bytes ws). rewrite absorb_i_app.
  rewrite Int64.add_assoc in LS2. exact LS2.
Qed.

Theorem eval_sha256_confidential m (pfx : int) :
  LS m bA cores live ->
  Mem.load Mint32 m bc (oc + 32) = Some (Vint pfx) ->
  pfx = Int.repr 0 \/ pfx = Int.repr 1 \/ pfx = Int.repr 2 \/ pfx = Int.repr 3 ->
  (forall j, (j < 8)%nat -> Mem.load Mint32 m bc (oc + 4 * Z.of_nat j) = Some (Vint (nth j ws Int.zero))) ->
  let B := conf_bytes even odd pfx ws in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_sha256_confidential)
      [Vint even; Vint odd; ctxv; confv] E0 m' Vundef /\
    LS m' bA (upd cores k (bx, ob, fst (absorb_i l regs B), snd (absorb_i l regs B),
                           Int64.add c (Int64.repr (Z.of_nat (length B))))) live /\
    mfrP (opP bA bx ob) m m'.
Proof.
  intros HLS HP Hcase HW B.
  assert (Vc : Mem.valid_block m bc).
  { eapply Mem.perm_valid_block. apply (proj1 (Mem.load_valid_access _ _ _ _ _ HP) (oc + 32)). cbn. lia. }
  set (le1 := PTree.set _t'1 (Vint pfx) cf_le).
  assert (HSw : forall mS (outS : outcome),
    Clight2.exec_stmt sha_ge empty_env le1 m
      (seq_of_labeled_statement
         (select_switch (Int.unsigned pfx)
            (match cf_switch with Sswitch _ sl => sl | _ => LSnil end))) E0 le1 mS outS ->
    Clight2.exec_stmt sha_ge empty_env le1 m cf_switch E0 le1 mS (outcome_switch outS)).
  { intros mS outS HX. cbv delta [cf_switch] beta iota.
    eapply exec_Sswitch with (v := Vint pfx) (n := Int.unsigned pfx);
      [apply eval_Etempvar; apply PTree.gss|reflexivity|exact HX]. }
  assert (HLen8 : length (be_bytes ws) = 32%nat) by (rewrite be_bytes_length, Hws; reflexivity).
  destruct Hcase as [->|Hcase].
  - (* NONE *)
    destruct (LS_uchar Hmodel bA cores live k bx ob l regs c Hk Hlive m (Int.repr 0) HLS eq_refl)
      as (m1 & vr & HC1 & LS1 & FR1).
    exists m1. split; [|split; [exact LS1|exact FR1]].
    eapply eval_funcall_internal with (e := empty_env) (le1 := cf_le) (m1 := m) (m2 := m1) (le2 := le1)
      (out := Out_return None); [apply cf_entry| |reflexivity|reflexivity].
    rewrite cf_body_shape. eapply exec_Sseq_2; [|discriminate].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact (cf_prefix_exec m _ HP)|].
    change (Out_return None) with (outcome_switch (Out_return None)). apply HSw.
    cbn. eapply exec_Sseq_2; [|discriminate].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [|apply exec_Sreturn_none].
    eapply cf_call_uchar; [reflexivity|apply eval_Econst_int|reflexivity|exact HC1].
  - (* a prefix byte and the data *)
    set (p := if Int.eq pfx (Int.repr 1) then Int.repr 1 else if Int.eq pfx (Int.repr 2) then even else odd).
    assert (Hp : Int.zero_ext 8 p = p).
    { unfold p. destruct Hcase as [->|[->| ->]]; cbn; [reflexivity|exact Heven|exact Hodd]. }
    destruct (cf_two_ops m p HLS Hp Vc HW) as (m1 & vr & m2 & HC1 & HC2 & LS2 & FR2).
    assert (HB : B = p :: be_bytes ws).
    { unfold B, conf_bytes, p. destruct Hcase as [->|[->| ->]]; reflexivity. }
    exists m2. split; [|split; [|exact FR2]].
    2: { rewrite HB. cbn [length]. rewrite HLen8. exact LS2. }
    eapply eval_funcall_internal with (e := empty_env) (le1 := cf_le) (m1 := m) (m2 := m2) (le2 := le1)
      (out := Out_normal); [apply cf_entry| |reflexivity|reflexivity].
    rewrite cf_body_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m1).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact (cf_prefix_exec m _ HP)|].
      change Out_normal with (outcome_switch Out_break). apply HSw.
      assert (HU : forall (a2 : expr) v2 rest,
        eval_expr sha_ge empty_env le1 m a2 v2 -> sem_cast v2 (typeof a2) tuchar m = Some (Vint p) ->
        Clight2.exec_stmt sha_ge empty_env le1 m
          (Ssequence
             (Ssequence
                (Scall None (Evar _sha256_uchar (Tfunction (Tcons CTXP (Tcons tuchar Tnil)) tbool cc_default))
                   [Etempvar _ctx CTXP; a2]) Sbreak) rest) E0 le1 m1 Out_break).
      { intros a2 v2 rest HE HCa. eapply exec_Sseq_2; [|discriminate].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [|apply exec_Sbreak].
        eapply cf_call_uchar; [reflexivity|exact HE|exact HCa|exact HC1]. }
      destruct Hcase as [->|[->| ->]]; cbn.
      * apply HU with (v2 := Vint (Int.repr 1)); [apply eval_Econst_int|reflexivity].
      * apply HU with (v2 := Vint even); [apply eval_Etempvar; reflexivity|].
        change (Some (Vint (Int.zero_ext 8 even)) = Some (Vint p)). rewrite Heven. reflexivity.
      * apply HU with (v2 := Vint odd); [apply eval_Etempvar; reflexivity|].
        change (Some (Vint (Int.zero_ext 8 odd)) = Some (Vint p)). rewrite Hodd. reflexivity.
    + cbv delta [cf_last] beta iota.
      eapply cf_call_hash; [reflexivity|apply cf_data_addr; reflexivity|reflexivity|exact HC2].
Qed.
End Confidential.
