(** Three further jets of the Elements translation unit, executed in
    [elements_ge], against their canonical programs:

    - [annex_hash]: C text and program ([Programs.Elements.annexHash]) are
      those of Bitcoin; the proof is the accepted one with the function
      renamed (elements-sha/gen-elements-sha-ports.py).
    - [build_tapleaf_simplicity], [build_tapbranch]: same C and program shape
      as Bitcoin's with the tags "TapLeaf/elements" and "TapBranch/elements"
      (elements-sha/gen-elements-tap-ports.py); the tag constants are checked
      by evaluating the canonical [hashBlock] in [jet_elements_tap_tags] and
      [jet_elements_build_tapbranch_spec].

    The tag premises [el_sha_tapleaf_tag_ok] / [el_sha_tapbranch_tag_ok] say
    that the constant global arrays hold their initial contents; like the
    other global-object premises they are facts about program start-up, not
    input requirements. *)
From Coq Require Import ZArith List.
From compcert Require Import Clight Memory.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_memcpy_model C.jet_partial C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_spec.
Require Import C.jet_bitcoin_ctx_hash_spec.
Require C.jets_elements.
Require Import C.jet_elements_linkage C.jet_elements_sha_program C.jet_elements_sha_jets.
Require Import C.jet_elements_annex_hash_jet.
Require Import C.jet_elements_make_tapleaf_exec C.jet_elements_build_tapleaf_spec C.jet_elements_build_tapleaf_jet.
Require Import C.jet_elements_make_tapbranch_exec C.jet_elements_build_tapbranch_spec C.jet_elements_build_tapbranch_jet.

Theorem annex_hash_local_spec_elements : memcpy_model ->
  sha_jet_partial_local_spec_elements jets_elements.f_simplicity_annex_hash
    (Ty.Prod sha256_ctx8_type (Ty.Sum Ty.Unit (Word 8))) sha256_ctx8_type
    (fun a => @annex_hash_spec optalg a).
Proof. intro H. apply sha_jet_partial_local_spec_to_elements. exact (elements_annex_hash_local_spec H). Qed.

Theorem build_tapleaf_simplicity_local_spec_elements : memcpy_model ->
  sha_jet_local_spec_pre_elements el_sha_tapleaf_pre jets_elements.f_simplicity_build_tapleaf_simplicity
    (Word 8) (Word 8) (fun a => @el_build_tapleaf_spec Alg.CoreFunSem a).
Proof. intro H. apply sha_jet_local_spec_pre_to_elements. exact (elements_build_tapleaf_simplicity_local_spec H). Qed.

Theorem build_tapbranch_local_spec_elements : memcpy_model ->
  sha_jet_local_spec_pre_elements el_sha_tapbranch_pre jets_elements.f_simplicity_build_tapbranch
    (Word 9) (Word 8) (fun ab => @el_build_tapbranch_spec Alg.CoreFunSem ab).
Proof. intro H. apply sha_jet_local_spec_pre_to_elements. exact (elements_build_tapbranch_local_spec H). Qed.

