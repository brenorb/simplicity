(** [sha_256_ctx_8_add_n]: statement decomposition, the disabled assertion,
    and the initialisation [sha256_context ctx = {.output = midstate.s}]
    (output pointer, zero counter, 64 zero block bytes, zero overflow). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_be32_exec C.jet_sha_uchars_prep.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Notation CTX := (Tstruct _sha256_context noattr).
Notation CTXP := (tptr (Tstruct _sha256_context noattr)).
Notation MID := (Tstruct _sha256_midstate noattr).
Notation FRP := (tptr (Tstruct _frameItem noattr)).

Definition an_assert : statement :=
  match fn_body f_sha_256_ctx_8_add_n with Ssequence s _ => s | _ => Sskip end.

Definition an_out_assign : statement :=
  Sassign (Efield (Evar _ctx CTX) _output (tptr tuint)) (Efield (Evar _midstate MID) _s (tarray tuint 8)).
Definition an_cnt_assign : statement :=
  Sassign (Efield (Evar _ctx CTX) _counter tulong) (Econst_int (Int.repr 0) tint).
Definition an_blk_assign (k : nat) : statement :=
  Sassign (Ederef (Ebinop Oadd (Efield (Evar _ctx CTX) _block (tarray tuchar 64))
    (Econst_int (Int.repr (Z.of_nat k)) tint) (tptr tuchar)) tuchar) (Econst_int (Int.repr 0) tint).
Fixpoint an_blk_init (n k : nat) (rest : statement) : statement :=
  match n with
  | O => rest
  | S n' => Ssequence (an_blk_assign k) (an_blk_init n' (S k) rest)
  end.
Definition an_ovf_assign : statement :=
  Sassign (Efield (Evar _ctx CTX) _overflow tbool) (Econst_int (Int.repr 0) tint).

Definition an_read : statement :=
  Ssequence
    (Scall (Some _t'3) (Evar _simplicity_read_sha256_context
        (Tfunction (Tcons CTXP (Tcons FRP Tnil)) tbool cc_default))
      [Eaddrof (Evar _ctx CTX) CTXP; Etempvar _src FRP])
    (Sifthenelse (Eunop Onotbool (Etempvar _t'3 tbool) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip).
Definition an_read8s : statement :=
  Scall None (Evar _read8s (Tfunction (Tcons (tptr tuchar) (Tcons tulong (Tcons FRP Tnil))) tvoid cc_default))
    [Evar _buf (tarray tuchar 512); Etempvar _n tulong; Etempvar _src FRP].
Definition an_uchars : statement :=
  Scall None (Evar _sha256_uchars
      (Tfunction (Tcons CTXP (Tcons (tptr tuchar) (Tcons tulong Tnil))) tbool cc_default))
    [Eaddrof (Evar _ctx CTX) CTXP; Evar _buf (tarray tuchar 512); Etempvar _n tulong].
Definition an_write : statement :=
  Ssequence
    (Scall (Some _t'4) (Evar _simplicity_write_sha256_context
        (Tfunction (Tcons FRP (Tcons CTXP Tnil)) tbool cc_default))
      [Etempvar _dst FRP; Eaddrof (Evar _ctx CTX) CTXP])
    (Sreturn (Some (Etempvar _t'4 tbool))).
Definition an_rest : statement :=
  Ssequence an_read (Ssequence an_read8s (Ssequence an_uchars an_write)).

Definition an_init (rest : statement) : statement :=
  Ssequence an_out_assign (Ssequence an_cnt_assign (an_blk_init 64 0 (Ssequence an_ovf_assign rest))).

Lemma an_body : fn_body f_sha_256_ctx_8_add_n = Ssequence an_assert (an_init an_rest).
Proof. reflexivity. Qed.

Lemma eval_local_ctx_field_lvalue k e le m bx :
  e!_ctx = Some (bx, CTX) ->
  eval_lvalue sha_ge e le m (Efield (Evar _ctx CTX) (ctx_field k) (ctx_field_type k))
    bx (Ptrofs.add Ptrofs.zero (Ptrofs.repr (ctx_offset k))) Full.
Proof.
  intros He. eapply eval_Efield_struct.
  - eapply eval_Elvalue; [apply eval_Evar_local; exact He|apply deref_loc_copy; reflexivity].
  - reflexivity.
  - vm_compute; reflexivity.
  - destruct k; vm_compute; reflexivity.
Qed.

Lemma local_ctx_offset k :
  Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (ctx_offset k))) = ctx_offset k.
Proof. destruct k; reflexivity. Qed.

Lemma eval_local_midstate_s e le m bm :
  e!_midstate = Some (bm, MID) ->
  eval_expr sha_ge e le m (Efield (Evar _midstate MID) _s (tarray tuint 8)) (Vptr bm Ptrofs.zero).
Proof.
  intros He. eapply eval_Elvalue.
  - eapply eval_Efield_struct with (delta := 0).
    + eapply eval_Elvalue; [apply eval_Evar_local; exact He|apply deref_loc_copy; reflexivity].
    + reflexivity.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
  - apply deref_loc_reference; reflexivity.
Qed.

Local Opaque sha_ge.

Lemma an_assert_exec e le m :
  Clight2.exec_stmt sha_ge e le m an_assert E0 le m Out_normal.
Proof.
  unfold an_assert. cbn [f_sha_256_ctx_8_add_n fn_body].
  eapply exec_Sloop_stop2 with (t1 := E0) (t2 := E0) (out1 := Out_normal) (out2 := Out_break).
  - eapply exec_Sifthenelse with (b := false).
    + eapply eval_Eunop; [apply eval_Econst_int|reflexivity].
    + reflexivity.
    + apply exec_Sskip.
  - constructor.
  - apply exec_Sbreak.
  - constructor.
Qed.

Definition init_frame (bx : block) (lo : Z) (m m1 : mem) : Prop :=
  (forall ch b ofs, (b <> bx \/ ofs + size_chunk ch <= lo) -> Mem.load ch m1 b ofs = Mem.load ch m b ofs) /\
  (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m1 b ofs k p) /\
  (forall b, Mem.valid_block m b -> Mem.valid_block m1 b).

Lemma init_frame_store ch bx lo m ofs v m1 :
  Mem.store ch m bx ofs v = Some m1 -> lo <= ofs -> init_frame bx lo m m1.
Proof.
  intros HS Hlo. split; [|split].
  - intros c b o Hc. eapply Mem.load_store_other; [exact HS|].
    destruct Hc as [H|H]; [left; exact H|right; left; lia].
  - intros b o k p Hp. eapply Mem.perm_store_1; eauto.
  - intros b Hv. eapply Mem.store_valid_block_1; eauto.
Qed.

Lemma init_frame_trans bx lo lo' m1 m2 m3 :
  lo <= lo' -> init_frame bx lo' m1 m2 -> init_frame bx lo m2 m3 -> init_frame bx lo m1 m3.
Proof.
  intros Hlo (L1 & P1 & V1) (L2 & P2 & V2). split; [|split].
  - intros ch b ofs Hc. rewrite L2 by exact Hc. apply L1.
    destruct Hc as [H|H]; [left; exact H|right; lia].
  - intros b ofs k p Hp. apply P2, P1, Hp.
  - intros b Hv. apply V2, V1, Hv.
Qed.

Section Init.
Variables (e : env) (bx bm : block).
Hypothesis Hex : e!_ctx = Some (bx, CTX).
Hypothesis Hem : e!_midstate = Some (bm, MID).

Lemma an_blk_init_exec n : forall k le m,
  (k + n <= 64)%nat -> Mem.range_perm m bx 0 88 Cur Writable ->
  exists m1,
    (forall rest t le' m' out,
       Clight2.exec_stmt sha_ge e le m1 rest t le' m' out ->
       Clight2.exec_stmt sha_ge e le m (an_blk_init n k rest) t le' m' out) /\
    init_frame bx 16 m m1.
Proof.
  induction n as [|n IH]; intros k le m Hk HP.
  - exists m. split; [intros rest t le' m' out H; exact H|].
    split; [reflexivity|split; auto].
  - assert (HW : Mem.valid_access m Mint8unsigned bx (16 + Z.of_nat k) Writable).
    { split; [|exists (16 + Z.of_nat k); cbn; lia]. intros ofs Ho. apply HP.
      change (size_chunk Mint8unsigned) with 1 in Ho. lia. }
    destruct (Mem.valid_access_store m Mint8unsigned bx (16 + Z.of_nat k)
      (Vint (Int.zero_ext 8 (Int.repr 0))) HW) as [m0 HS].
    destruct (IH (S k) le m0 ltac:(lia)) as (m1 & HEx & HF).
    { intros ofs Ho. eapply Mem.perm_store_1; [exact HS|apply HP; exact Ho]. }
    exists m1. split.
    + intros rest t le' m' out HR. cbn [an_blk_init].
      replace t with (E0 ** t) by reflexivity.
      eapply exec_Sseq_1; [|apply HEx; exact HR].
      unfold an_blk_assign.
      eapply exec_Sassign with (v2 := Vint (Int.repr 0)) (v := Vint (Int.zero_ext 8 (Int.repr 0))).
      * eapply eval_Ederef. eapply eval_Ebinop.
        -- eapply eval_Elvalue; [apply (eval_local_ctx_field_lvalue SBlock); exact Hex|].
           apply deref_loc_reference; reflexivity.
        -- apply eval_Econst_int.
        -- reflexivity.
      * apply eval_Econst_int.
      * reflexivity.
      * eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
        match goal with |- Mem.store _ _ _ (Ptrofs.unsigned ?o) _ = _ =>
          replace (Ptrofs.unsigned o) with (16 + Z.of_nat k); [exact HS|] end.
        assert (H16 : forall o, o = Ptrofs.add Ptrofs.zero (Ptrofs.repr 16) -> Ptrofs.unsigned o = 16)
          by (intros o ->; reflexivity).
        symmetry. rewrite ptr_byte_offset;
          try (match goal with |- context[Ptrofs.unsigned ?o] => rewrite (H16 o eq_refl) end);
          try lia.
        assert (HMU : Ptrofs.max_unsigned = 18446744073709551615) by reflexivity.
        rewrite HMU. clear - Hk. lia.
    + eapply init_frame_trans with (lo' := 16); [lia|eapply init_frame_store; [exact HS|lia]|exact HF].
Qed.

Lemma an_init_exec le m :
  Mem.range_perm m bx 0 88 Cur Writable ->
  exists m1,
    (forall rest t le' m' out,
       Clight2.exec_stmt sha_ge e le m1 rest t le' m' out ->
       Clight2.exec_stmt sha_ge e le m (an_init rest) t le' m' out) /\
    Mem.load Mptr m1 bx 0 = Some (Vptr bm Ptrofs.zero) /\
    init_frame bx 0 m m1.
Proof.
  intros HP.
  assert (HW0 : Mem.valid_access m Mptr bx 0 Writable).
  { split; [|exists 0; reflexivity]. intros ofs Ho. apply HP. change (size_chunk Mptr) with 8 in Ho. lia. }
  destruct (Mem.valid_access_store m Mptr bx 0 (Vptr bm Ptrofs.zero) HW0) as [ma HSa].
  assert (HPa : Mem.range_perm ma bx 0 88 Cur Writable).
  { intros ofs Ho. eapply Mem.perm_store_1; [exact HSa|apply HP; exact Ho]. }
  assert (HW8 : Mem.valid_access ma Mint64 bx 8 Writable).
  { split; [|exists 1; reflexivity]. intros ofs Ho. apply HPa. change (size_chunk Mint64) with 8 in Ho. lia. }
  destruct (Mem.valid_access_store ma Mint64 bx 8 (Vlong (Int64.repr (Int.signed (Int.repr 0)))) HW8)
    as [mb HSb].
  assert (HPb : Mem.range_perm mb bx 0 88 Cur Writable).
  { intros ofs Ho. eapply Mem.perm_store_1; [exact HSb|apply HPa; exact Ho]. }
  destruct (an_blk_init_exec 64 0 le mb ltac:(lia) HPb) as (mc & HExc & HFc).
  assert (HPc : Mem.range_perm mc bx 0 88 Cur Writable).
  { intros ofs Ho. apply (proj1 (proj2 HFc)), HPb, Ho. }
  assert (HW80 : Mem.valid_access mc Mint8unsigned bx 80 Writable).
  { split; [|exists 80; reflexivity]. intros ofs Ho. apply HPc.
    change (size_chunk Mint8unsigned) with 1 in Ho. lia. }
  destruct (Mem.valid_access_store mc Mint8unsigned bx 80 (Vint Int.zero) HW80) as [md HSd].
  exists md. split; [|split].
  - intros rest t le' m' out HR. unfold an_init.
    replace t with (E0 ** (E0 ** t)) by reflexivity.
    eapply exec_Sseq_1.
    { unfold an_out_assign.
      eapply exec_Sassign with (v2 := Vptr bm Ptrofs.zero) (v := Vptr bm Ptrofs.zero).
      - apply (eval_local_ctx_field_lvalue SOutput); exact Hex.
      - apply eval_local_midstate_s; exact Hem.
      - reflexivity.
      - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
        rewrite (local_ctx_offset SOutput). exact HSa. }
    eapply exec_Sseq_1.
    { unfold an_cnt_assign.
      eapply exec_Sassign with (v2 := Vint (Int.repr 0)) (v := Vlong (Int64.repr (Int.signed (Int.repr 0)))).
      - apply (eval_local_ctx_field_lvalue SCounter); exact Hex.
      - apply eval_Econst_int.
      - reflexivity.
      - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
        rewrite (local_ctx_offset SCounter). exact HSb. }
    apply HExc. replace t with (E0 ** t) by reflexivity.
    eapply exec_Sseq_1; [|exact HR].
    unfold an_ovf_assign.
    eapply exec_Sassign with (v2 := Vint (Int.repr 0)) (v := Vint Int.zero).
    + apply (eval_local_ctx_field_lvalue SOverflow); exact Hex.
    + apply eval_Econst_int.
    + reflexivity.
    + eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
      rewrite (local_ctx_offset SOverflow). exact HSd.
  - rewrite (Mem.load_store_other _ _ _ _ _ _ HSd) by (right; left; change (size_chunk Mptr) with 8; lia).
    rewrite (proj1 HFc) by (right; change (size_chunk Mptr) with 8; lia).
    rewrite (Mem.load_store_other _ _ _ _ _ _ HSb) by (right; left; change (size_chunk Mptr) with 8; lia).
    rewrite (Mem.load_store_same _ _ _ _ _ _ HSa). reflexivity.
  - eapply init_frame_trans with (lo' := 0); [lia|eapply init_frame_store; [exact HSa|lia]|].
    eapply init_frame_trans with (lo' := 8); [lia|eapply init_frame_store; [exact HSb|lia]|].
    eapply init_frame_trans with (lo' := 16); [lia|exact HFc|].
    eapply init_frame_store; [exact HSd|lia].
Qed.
End Init.
