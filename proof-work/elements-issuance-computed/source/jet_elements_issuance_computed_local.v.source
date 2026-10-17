(** Complete original getter calls against the canonical primitive programs.
    Their caller relation explicitly retains the cached entropy/asset/token
    value obligation. No builder correctness or extra coverage is claimed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Maps Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option C.jet_elements_prim.
Require Import C.jet_application_sep C.jet_elements_issuance_status_exec.
Require Import C.jet_elements_issuance_jets C.jet_elements_field_eval C.jet_elements_version_exec.
Require Import C.jet_elements_indexed_tag3_exec C.jet_elements_indexed_tag3_gen.
Require Import C.jet_elements_indexed_ptr C.jet_elements_indexed_ptr_jets C.jet_elements_index_eval.
Require Import C.jet_elements_wrapper C.jet_elements_linkage C.jets_elements C.jet_encoding C.jet_word_repr.
Require Import C.jet_elements_indexed_scalar C.jet_uint32_array_init C.jet_elements_effects.
Require Import C.jet_elements_issuance_entropy_spec C.jet_elements_issuance_computed_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Theorem computed_issuance_hash_local field delta value f
    (HP : forall x, computed_issuance_present (value x) = opt_is_some (sigTxiIssuance x))
    (HField : elements_field_at _assetIssuance field delta)
    (Hd0 : 0 <= delta) (Hd1 : delta + 32 <= 280)
    (Hshape : elements_wrapper_shape f
      (elements_indexed_rest_tag3 _t'7 _t'8 _numInputs
        (computed_issuance_then_stmt field) (elements_skip_stmt 257)))
    (spec : Ty.tySem Word32 -> Elements.env -> option (Ty.tySem issuance_digest_option))
    (Hsem : forall a environment, spec a environment =
      Some (match nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a)) with
            | None => inl tt | Some txi => inr (value txi) end)) :
  application_jet_local_spec_sep f elements_ge Elements.env Word32 issuance_digest_option
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
      (computed_issuance_hash_rep delta value) 544 0 0 696) spec.
Proof.
  refine (elements_indexed_gen_local_tag3 (fun e => sigTxIn (Elements.envTx e)) 257
    (fun txi => @encode (Ty.Sum Ty.Unit Word256) (value txi))
    (computed_issuance_hash_rep delta value) (Ty.Sum Ty.Unit Word256)
    _t'7 _t'8 _numInputs 696 0 544 (computed_issuance_then_stmt field) f
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate) ltac:(lia)
    ltac:(intro x; change (Z.of_nat (length (@encode (Ty.Sum Ty.Unit Word256) (value x))) = 257);
      rewrite encode_length; reflexivity) elements_elementsTransaction_numInputs
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ Hshape ltac:(reflexivity) spec _).
  - intros m1 m2 b ofs x [HT HA] HL. split.
    + unfold issuance_status_enum_rep in *. apply (HL Mint32 (ofs + 528) _);
        [lia|change (size_chunk Mint32) with 4; lia|exact HT].
    + intros h HH. eapply uint32_array_at_mono;
        [exact (Digest.hash256_len (to_hash256 h))|exact (HA h HH)|].
      intros chunk o v Ho Hsz Hv. apply HL; [lia|lia|exact Hv].
  - intros bd dbase bw edge bl le m x be ebase bt txbase bin inbase r cur
      HI HD HE He0 He1 Ht0 Ht1 Hi0 Hi1 HLtx HLin HT S1 S2 S3 HF.
    pose proof (Int64.unsigned_range r) as Hr0.
    set (lc := PTree.set _input (Vptr bin (Ptrofs.repr (inbase + 544 * Int64.unsigned r)))
      (PTree.set _t'6 (Vptr bin (Ptrofs.repr inbase))
        (PTree.set _t'5 (Vptr bt (Ptrofs.repr txbase)) le))).
    assert (HS : Clight2.exec_stmt elements_ge (elements_version_locals bl) le m
      computed_issuance_setup_stmt E0 lc m Out_normal).
    { exact (exec_computed_issuance_setup bl le m be ebase bt txbase bin inbase r
        HI HE He0 He1 Ht0 Ht1 Hi0 Hi1 HLtx HLin). }
    assert (HID : lc!_input = Some (Vptr bin (Ptrofs.repr (inbase + 544 * Int64.unsigned r)))).
    { unfold lc; apply PTree.gss. }
    assert (HDD : lc!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
    { unfold lc. repeat rewrite PTree.gso by discriminate. exact HD. }
    destruct (exec_computed_issuance_payload field delta value HP bl lc m x bin
      (inbase + 544 * Int64.unsigned r) bd dbase bw edge cur HField Hd0 Hd1 HID HDD
      ltac:(lia) Hi1 HT S3 HF) as (lef & mf & HX & HOut).
    exists lef, mf. split; [|exact HOut]. unfold computed_issuance_then_stmt.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := lc); [exact HS|exact HX].
  - intros a environment. eexists. split; [apply Hsem|].
    unfold indexed_ptr_cells. change (toZ32 a) with (toZ a).
    destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))); reflexivity.
Qed.

Ltac computed_issuance_shape :=
  repeat split; try reflexivity;
  intros x y HX HY Hxy; cbn in HX, HY;
  repeat match goal with HH : _ \/ _ |- _ => destruct HH end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].

Lemma elements_issuance_entropy_shape :
  elements_wrapper_shape f_simplicity_issuance_entropy
    (elements_indexed_rest_tag3 _t'7 _t'8 _numInputs
      (computed_issuance_then_stmt _entropy) (elements_skip_stmt 257)).
Proof. computed_issuance_shape. Qed.

Lemma elements_issuance_asset_shape :
  elements_wrapper_shape f_simplicity_issuance_asset
    (elements_indexed_rest_tag3 _t'7 _t'8 _numInputs
      (computed_issuance_then_stmt _assetId) (elements_skip_stmt 257)).
Proof. computed_issuance_shape. Qed.

Lemma elements_issuance_token_shape :
  elements_wrapper_shape f_simplicity_issuance_token
    (elements_indexed_rest_tag3 _t'7 _t'8 _numInputs
      (computed_issuance_then_stmt _tokenId) (elements_skip_stmt 257)).
Proof. computed_issuance_shape. Qed.

Theorem elements_issuance_entropy_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_entropy elements_ge Elements.env Word32 issuance_digest_option
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
      (computed_issuance_hash_rep 72 issuance_entropy_of_input) 544 0 0 696)
    (fun a environment => @elements_issuance_entropy_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply computed_issuance_hash_local; [| |lia|lia|exact elements_issuance_entropy_shape|].
  - intro x. unfold issuance_entropy_of_input, computed_issuance_present, opt_is_some.
    destruct (sigTxiIssuance x) as [[new | re] | ]; reflexivity.
  - vm_compute; reflexivity.
  - exact elements_issuance_entropy_sem.
Qed.

Theorem elements_issuance_asset_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_asset elements_ge Elements.env Word32 issuance_digest_option
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
      (computed_issuance_hash_rep 168 issuance_asset_of_input) 544 0 0 696)
    (fun a environment => @elements_issuance_asset_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply computed_issuance_hash_local; [| |lia|lia|exact elements_issuance_asset_shape|].
  - intro x. unfold issuance_asset_of_input, issuance_entropy_of_input, computed_issuance_present, opt_is_some.
    destruct (sigTxiIssuance x) as [[new | re] | ]; reflexivity.
  - vm_compute; reflexivity.
  - exact elements_issuance_asset_sem.
Qed.

Theorem elements_issuance_token_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_token elements_ge Elements.env Word32 issuance_digest_option
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
      (computed_issuance_hash_rep 200 issuance_token_of_input) 544 0 0 696)
    (fun a environment => @elements_issuance_token_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply computed_issuance_hash_local; [| |lia|lia|exact elements_issuance_token_shape|].
  - intro x. unfold issuance_token_of_input, computed_issuance_present, opt_is_some.
    destruct (sigTxiIssuance x) as [[new | re] | ]; reflexivity.
  - vm_compute; reflexivity.
  - exact elements_issuance_token_sem.
Qed.
