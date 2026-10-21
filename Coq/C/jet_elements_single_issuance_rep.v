(** Initial fields read by the computing issuance_hash, with cache values
    related to the primitive-bearing specification. Inactive union members
    and uninitialized local objects are not required. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Values.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import C.jet_uint32_array_init C.jet_bitmachine_rep C.jet_buffer_input.
Require Import C.jet_elements_asset_jets.
Require Import C.jet_elements_indexed_ptr_jets.
Require Import C.jet_elements_prim C.jet_elements_amount_jets.
Require Import C.jet_elements_input_hash_jets C.jet_elements_issuance_entropy_spec.
Require Import C.jet_elements_issuance_amounts_hash_program C.jet_elements_blinding_entropy_spec.
Require Import C.jet_elements_single_issuance_spec C.jet_elements_single_issuance_amount.
Require Import C.jet_elements_single_issuance_active C.jet_elements_single_issuance_blinding.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 15.

Definition eis_tag (txi : sigTxInput) : int :=
  match sigTxiIssuance txi with None => Int.zero | Some (inl _) => Int.one | Some (inr _) => Int.repr 2 end.
Definition eis_asset_id (txi : sigTxInput) : hash256 :=
  match issuance_asset_of_input txi with inl _ => byteStringHash [] | inr h => to_hash256 h end.
Definition eis_token_id (txi : sigTxInput) : hash256 :=
  match issuance_token_of_input txi with inl _ => byteStringHash [] | inr h => to_hash256 h end.
Definition eis_asset_amount (txi : sigTxInput) : amountWith Datatypes.unit :=
  match sigTxiIssuance txi with
  | None => Explicit Int64.zero
  | Some (inl n) => clearPrf (newIssuanceAmount n)
  | Some (inr r) => clearPrf (reissuanceAmount r)
  end.
Definition eis_token_amount (txi : sigTxInput) : amountWith Datatypes.unit :=
  match sigTxiIssuance txi with Some (inl n) => clearPrf (newIssuanceTokenAmount n) | _ => Explicit Int64.zero end.
Definition eis_proof_asset (txi : sigTxInput) : hash256 := byteStringHash (issuance_asset_proof_bytes txi).
Definition eis_proof_token (txi : sigTxInput) : hash256 := byteStringHash (issuance_token_proof_bytes txi).
Definition eis_union_hash (txi : sigTxInput) : hash256 :=
  match sigTxiIssuance txi with
  | None => byteStringHash []
  | Some (inl n) => newIssuanceContractHash n
  | Some (inr r) => reissuanceBlindingNonce r
  end.
Definition eis_re_entropy (txi : sigTxInput) : hash256 :=
  match sigTxiIssuance txi with Some (inr r) => reissuanceEntropy r | _ => byteStringHash [] end.

Definition eis_message (txi : sigTxInput) : list (Ty.tySem Word8) :=
  elements_single_issuance_bytes (issuance_asset_pair_of_input txi) (issuance_token_pair_of_input txi)
    (from_hash256 (eis_proof_asset txi)) (from_hash256 (eis_proof_token txi))
    (elements_blinding_entropy_of_input txi).

Lemma eis_message_none txi : sigTxiIssuance txi = None ->
  eis_message txi = elements_single_issuance_bytes (inl tt) (inl tt)
    (from_hash256 (eis_proof_asset txi)) (from_hash256 (eis_proof_token txi)) (inl tt).
Proof.
  intros HI. unfold eis_message, issuance_asset_pair_of_input, issuance_token_pair_of_input,
    elements_blinding_entropy_of_input. rewrite HI. reflexivity.
Qed.

Lemma eis_message_active txi (isnew : bool) :
  (if isnew then exists n, sigTxiIssuance txi = Some (inl n)
   else exists r, sigTxiIssuance txi = Some (inr r)) ->
  eis_some_message isnew (eis_asset_id txi) (eis_token_id txi) (eis_asset_amount txi)
    (eis_token_amount txi) (eis_proof_asset txi) (eis_proof_token txi)
    (eis_union_hash txi) (eis_re_entropy txi) = eis_message txi.
Proof.
  intros HI. destruct isnew; destruct HI as [n HI];
    unfold eis_some_message, eis_message, eis_asset_id, eis_token_id,
      eis_asset_amount, eis_token_amount, eis_union_hash, eis_re_entropy,
      issuance_asset_pair_of_input, issuance_token_pair_of_input,
      issuance_asset_of_input, issuance_token_of_input, issuance_entropy_of_input,
      elements_blinding_entropy_of_input;
    rewrite HI; cbn [eis_selected_amount eis_blinding_pair]; rewrite !from_to_hash256; reflexivity.
Qed.

Definition eis_elem_rep (m : mem) (b : block) (ofs : Z) (txi : sigTxInput) : Prop :=
  Mem.load Mint32 m b (ofs + 272) = Some (Vint (eis_tag txi)) /\
  uint32_array_at m b (ofs + 104) (hash256_reg (eis_proof_asset txi)) /\
  uint32_array_at m b (ofs + 136) (hash256_reg (eis_proof_token txi)) /\
  match sigTxiIssuance txi with
  | None => True
  | Some iss =>
      uint32_array_at m b (ofs + 168) (hash256_reg (eis_asset_id txi)) /\
      uint32_array_at m b (ofs + 200) (hash256_reg (eis_token_id txi)) /\
      amount_rep m b (ofs + 232) (eis_asset_amount txi) /\
      uint32_array_at m b ofs (hash256_reg (eis_union_hash txi)) /\
      match iss with
      | inl _ => amount_rep m b (ofs + 32) (eis_token_amount txi)
      | inr _ => uint32_array_at m b (ofs + 72) (hash256_reg (eis_re_entropy txi))
      end
  end.

Lemma eis_elem_rep_valid m b ofs txi : eis_elem_rep m b ofs txi -> Mem.valid_block m b.
Proof. intros [HT _]. eapply load_valid_block; exact HT. Qed.

Lemma eis_elem_rep_mono m m' b ofs txi :
  eis_elem_rep m b ofs txi ->
  (forall ch off v, ofs <= off -> off + size_chunk ch <= ofs + 280 ->
     Mem.load ch m b off = Some v -> Mem.load ch m' b off = Some v) ->
  eis_elem_rep m' b ofs txi.
Proof.
  intros (HT & HPA & HPT & HA) HL.
  assert (HW : forall d h, 0 <= d -> d + 32 <= 280 ->
    uint32_array_at m b (ofs + d) (hash256_reg h) ->
    uint32_array_at m' b (ofs + d) (hash256_reg h)).
  { intros d h HD HM HR. eapply uint32_array_at_mono; [apply hash256_len|exact HR|].
    intros ch off v Hlo Hhi HRd. apply HL; [lia|lia|exact HRd]. }
  split.
  { apply HL; [lia|change (size_chunk Mint32) with 4; lia|exact HT]. }
  split. { apply HW; [lia|lia|exact HPA]. }
  split. { apply HW; [lia|lia|exact HPT]. }
  destruct (sigTxiIssuance txi) as [[n|r] | ]; [ | |constructor].
  - destruct HA as (HA & HTok & HAA & HQ & HE).
    split. { apply HW; [lia|lia|exact HA]. }
    split. { apply HW; [lia|lia|exact HTok]. }
    split.
    { eapply amount_rep_mono; [exact HAA|]. intros; apply HL; [lia|lia|assumption]. }
    split.
    { replace ofs with (ofs + 0) at 1 by lia. apply HW; [lia|lia|rewrite Z.add_0_r; exact HQ]. }
    eapply amount_rep_mono; [exact HE|]. intros; apply HL; [lia|lia|assumption].
  - destruct HA as (HA & HTok & HAA & HQ & HE).
    split. { apply HW; [lia|lia|exact HA]. }
    split. { apply HW; [lia|lia|exact HTok]. }
    split.
    { eapply amount_rep_mono; [exact HAA|]. intros; apply HL; [lia|lia|assumption]. }
    split.
    { replace ofs with (ofs + 0) at 1 by lia. apply HW; [lia|lia|rewrite Z.add_0_r; exact HQ]. }
    apply HW; [lia|lia|exact HE].
Qed.
