(** Execute issuance_hash's actual outer type test from initial represented
    fields, dispatch to the checked payload, and finalize its SHA state. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import C.jet_exec C.jet_memcpy_model C.jet_sha256_iv_init C.jet_bitcoin_composite_hash.
Require Import C.jets_elements C.jet_elements_prim C.jet_elements_amount_jets.
Require Import C.jet_elements_single_issuance_spec C.jet_elements_single_issuance_prep.
Require Import C.jet_elements_single_issuance_none C.jet_elements_single_issuance_active.
Require Import C.jet_elements_single_issuance_amount C.jet_elements_single_issuance_rep.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_ctx_abs.
Require Import C.jet_elements_support_sha_ctxi C.jet_elements_support_sha_add_n_init.
Require Import C.jet_elements_sha_program C.jet_elements_linkage.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64 sha_ge elements_ge.
Set Default Timeout 15.
Local Notation CONF := (Tstruct _confidential noattr).
Local Notation AMT := (Tstruct _confAmount noattr).

Definition eis_dispatch_stmt : statement :=
  ltac:(let s := eval cbv delta [eis_then] beta iota in eis_then in
    lazymatch s with Ssequence _ (Ssequence _ (Ssequence ?d _)) => exact d end).

Lemma eis_dispatch_shape : eis_dispatch_stmt =
  Ssequence (Sset _t'4 (eis_issuance_field _type tint))
    (Sifthenelse (Ebinop Oeq (Econst_int Int.zero tint) (Etempvar _t'4 tint) tint) eis_none eis_some).
Proof. reflexivity. Qed.

Definition eis_payload_le (txi : sigTxInput) (le : temp_env) (bin : block) (ofs : Z) (bz : block) : temp_env :=
  let le0 := PTree.set _t'4 (Vint (eis_tag txi)) le in
  match sigTxiIssuance txi with
  | None => le0
  | Some (inl _) => PTree.set _t'5 (Vint Int.one) (eis_token_le le0 true bin ofs bz)
  | Some (inr _) => PTree.set _t'5 (Vint (Int.repr 2)) (eis_token_le le0 false bin ofs bz)
  end.

Lemma eis_payload_le_dst txi le bin ofs bz :
  (eis_payload_le txi le bin ofs bz)!_dst = le!_dst.
Proof.
  unfold eis_payload_le. destruct (sigTxiIssuance txi) as [[n|r] | ];
    unfold eis_token_le; rewrite !PTree.gso by discriminate; reflexivity.
Qed.

Section Dispatch.
Variable Hmodel : memcpy_model.
Variables bx bm : block.
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.

Theorem exec_eis_dispatch_finalize e le m bin ofs ba bt bz bb txi :
  ctxi m bx bm [] sha256_iv_words Int64.zero false ->
  NoDup [ba; bt; bz; bb] ->
  (forall b, In b [ba; bt; bz; bb] -> b <> bin /\ b <> bx /\ b <> bm /\ b <> GC /\ b <> GM) ->
  e!_ctx = Some (bx, CTX) -> e!___compound = Some (ba, CONF) ->
  e!___compound__1 = Some (bt, CONF) -> e!___compound__2 = Some (bz, AMT) ->
  e!___compound__3 = Some (bb, tarray tuchar 32) ->
  e!_simplicity_sha256_confAsset = None -> e!_simplicity_sha256_confAmt = None ->
  e!_sha256_hash = None -> e!_sha256_uchar = None -> e!_sha256_uchars = None ->
  le!_issuance = Some (Vptr bin (Ptrofs.repr ofs)) ->
  0 <= ofs -> ofs + 280 <= Ptrofs.max_unsigned -> bin <> bx -> bin <> bm ->
  eis_elem_rep m bin ofs txi ->
  Mem.range_perm m ba 0 36 Cur Writable -> Mem.range_perm m bt 0 36 Cur Writable ->
  Mem.range_perm m bz 0 40 Cur Writable -> Mem.range_perm m bb 0 32 Cur Writable ->
  exists mp mf vr,
    Clight2.exec_stmt sha_ge e le m eis_dispatch_stmt E0 (eis_payload_le txi le bin ofs bz) mp Out_normal /\
    Clight2.eval_funcall sha_ge mp (Internal f_sha256_finalize) [Vptr bx Ptrofs.zero] E0 mf vr /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 mf bm (0 + 4 * Z.of_nat j) =
      Some (Vint (nth j (hash256_reg (sha256_bytes_of (eis_message txi))) Int.zero))) /\
    (forall ch b o, Mem.valid_block m b -> b <> ba -> b <> bt -> b <> bz -> b <> bb ->
      b <> bx -> b <> bm -> Mem.load ch mf b o = Mem.load ch m b o) /\
    (forall b o k p, Mem.valid_block m b -> Mem.perm m b o k p -> Mem.perm mf b o k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HX HN HF HC HBa HBt HBz HBb HGA HGM HH HU HUS HI HO HM Hix Him
    (HT & HPA & HPT & HA) PA PT PZ PB.
  set (le0 := PTree.set _t'4 (Vint (eis_tag txi)) le).
  assert (ET : Clight2.exec_stmt sha_ge e le m (Sset _t'4 (eis_issuance_field _type tint))
    E0 le0 m Out_normal).
  { apply exec_Sset. eapply eval_eis_kind; eassumption. }
  assert (HI0 : le0!_issuance = Some (Vptr bin (Ptrofs.repr ofs))).
  { unfold le0. rewrite PTree.gso by discriminate. exact HI. }
  assert (EC : eval_expr sha_ge e le0 m
    (Ebinop Oeq (Econst_int Int.zero tint) (Etempvar _t'4 tint) tint)
    (Val.of_bool (match sigTxiIssuance txi with None => true | Some _ => false end))).
  { eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; unfold le0; apply PTree.gss|].
    unfold eis_tag. destruct (sigTxiIssuance txi) as [[n|r] | ]; reflexivity. }
  destruct (sigTxiIssuance txi) as [[n|r] | ] eqn:HIss.
  - destruct HA as (HAsset & HToken & HAA & HQ & HTA).
    assert (HT' : Mem.load Mint32 m bin (ofs + 272) = Some (Vint (eis_kind true))).
    { unfold eis_tag in HT. rewrite HIss in HT. exact HT. }
    destruct (exec_eis_some_finalize Hmodel bx bm Hmx Hgx Hgm Hcx Hcm true e le0 m bin ofs ba bt bz bb
      (eis_asset_id txi) (eis_token_id txi) (eis_asset_amount txi) (eis_token_amount txi)
      (eis_proof_asset txi) (eis_proof_token txi) (eis_union_hash txi) (eis_re_entropy txi)
      HX HN HF HC HBa HBt HBz HBb HGA HGM HH HU HUS HI0 HO HM Hix Him HT'
      HAsset HToken HAA ltac:(intros _; exact HTA) HPA HPT HQ ltac:(discriminate) PA PT PZ PB)
      as (mp & mf & vr & CP & CF & RF & LF & PF & VF).
    rewrite (eis_message_active txi true ltac:(exists n; exact HIss)) in RF.
    exists mp, mf, vr. split.
    { unfold eis_payload_le. rewrite HIss. fold le0.
      rewrite eis_dispatch_shape. eapply exec_Sseq_1 with
        (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m); [exact ET|].
      eapply exec_Sifthenelse with (v1 := Val.of_bool false) (b := false);
        [exact EC|reflexivity|exact CP]. }
    split; [exact CF|]. split; [exact RF|]. split; [exact LF|]. split; [exact PF|exact VF].
  - destruct HA as (HAsset & HToken & HAA & HQ & HE).
    assert (HT' : Mem.load Mint32 m bin (ofs + 272) = Some (Vint (eis_kind false))).
    { unfold eis_tag in HT. rewrite HIss in HT. exact HT. }
    destruct (exec_eis_some_finalize Hmodel bx bm Hmx Hgx Hgm Hcx Hcm false e le0 m bin ofs ba bt bz bb
      (eis_asset_id txi) (eis_token_id txi) (eis_asset_amount txi) (eis_token_amount txi)
      (eis_proof_asset txi) (eis_proof_token txi) (eis_union_hash txi) (eis_re_entropy txi)
      HX HN HF HC HBa HBt HBz HBb HGA HGM HH HU HUS HI0 HO HM Hix Him HT'
      HAsset HToken HAA ltac:(discriminate) HPA HPT HQ ltac:(intros _; exact HE) PA PT PZ PB)
      as (mp & mf & vr & CP & CF & RF & LF & PF & VF).
    rewrite (eis_message_active txi false ltac:(exists r; exact HIss)) in RF.
    exists mp, mf, vr. split.
    { unfold eis_payload_le. rewrite HIss. fold le0.
      rewrite eis_dispatch_shape. eapply exec_Sseq_1 with
        (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m); [exact ET|].
      eapply exec_Sifthenelse with (v1 := Val.of_bool false) (b := false);
        [exact EC|reflexivity|exact CP]. }
    split; [exact CF|]. split; [exact RF|]. split; [exact LF|]. split; [exact PF|exact VF].
  - destruct (exec_eis_none_finalize Hmodel bx bm Hmx Hgx Hgm Hcx Hcm
      e le0 m bin ofs (eis_proof_asset txi) (eis_proof_token txi)
      HX HO HM Hix Him HH HU HC HI0 HPA HPT)
      as (mp & mf & vr & CP & CF & RF & LF & PF & VF).
    rewrite <- (eis_message_none txi HIss) in RF.
    exists mp, mf, vr. split.
    { unfold eis_payload_le. rewrite HIss. fold le0.
      rewrite eis_dispatch_shape. eapply exec_Sseq_1 with
        (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m); [exact ET|].
      eapply exec_Sifthenelse with (v1 := Val.of_bool true) (b := true);
        [exact EC|reflexivity|exact CP]. }
    split; [exact CF|]. split; [exact RF|]. split.
    { intros ch b o V _ _ _ _ Nx Nm. apply LF; assumption. }
    split; [exact PF|exact VF].
Qed.
End Dispatch.
