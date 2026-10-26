(** Compare the complete original public call with the exact assertion term
    on every represented key. The deferred memcpy/CTZ boundaries remain
    explicit. This does not assert reachability or impossibility of infinity. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.extraMath C.jet_memcpy_model C.jet_encoding C.jet_frame_layout C.jet_input_layout
 C.jet_output_layout C.jet_frame_inv C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp
 C.jet_secp_field_cmov C.jet_secp_rescale_literal C.jet_secp_generator_hash_map
 C.jet_secp_sha_startup C.jet_secp_swu_startup C.jet_secp_generator_sha_absorb
 C.jet_secp_hash_public_call C.jet_secp_hash_to_curve_spec C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_hash_to_curve Simplicity.Translate.encode rescale_field_output.

Lemma hash_public_expected_return key sx sy sz flag ox oy :
 hash_public_value key sx sy sz flag ox oy ->
 (match @literal_hash_to_curve (Alg.AssertionSem option_Monad_Zero) key with
   | Some _=>Vint Int.one | None=>Vint Int.zero end)=
 Vint (cmov_int ((generator_hash_accepted false key && generator_hash_accepted true key) && Int.eq flag Int.zero)).
Proof.
 intro Value;rewrite (hash_public_assertion_result _ _ _ _ _ _ _ Value).
 destruct (generator_hash_accepted false key && generator_hash_accepted true key);
   [destruct (Int.eq flag Int.zero)|];reflexivity.
Qed.

Lemma hash_public_return_agreement_iff key sx sy sz flag ox oy :
 hash_public_value key sx sy sz flag ox oy ->
 (Vint (cmov_int (generator_hash_accepted false key && generator_hash_accepted true key))=
   match @literal_hash_to_curve (Alg.AssertionSem option_Monad_Zero) key with
   | Some _=>Vint Int.one | None=>Vint Int.zero end <->
  (generator_hash_accepted false key && generator_hash_accepted true key)=false \/ flag=Int.zero).
Proof.
 intro Value;rewrite (hash_public_expected_return _ _ _ _ _ _ _ Value).
 destruct (generator_hash_accepted false key && generator_hash_accepted true key).
 - destruct (Int.eq flag Int.zero) eqn:Zero.
   + apply Int.same_if_eq in Zero;split;[intros;right;exact Zero|intros;reflexivity].
   + assert (Nonzero:flag<>Int.zero) by (intro Equal;subst flag;rewrite Int.eq_true in Zero;discriminate).
     split.
     * intro Equal;discriminate Equal.
     * intros [Impossible|Equal];[discriminate|contradiction].
 - split;[intros;left;reflexivity|intros;reflexivity].
Qed.

Theorem eval_hash_to_curve_compared (Hmodel:memcpy_model) key v_env m0 bd base bs sbase bw outedge cursor N bi edge rc :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
     E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
 secp_sha_startup m0 ->swu_startup m0 ->(forall prefix,generator_sha_prefix_state prefix m0) ->
 write_frame_at m0 bd base bw outedge cursor N ->512<=N ->
 frame_base_valid sbase ->(8|sbase) ->frame_fields_at m0 bs sbase bi edge rc ->
 frame_input_cells_at m0 bi edge rc (Simplicity.Translate.encode (key:Ty.tySem (Word 8))) ->
 0<=rc ->rc+256<=Int64.max_unsigned ->exists mf sx sy sz flag ox oy,
 Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_hash_to_curve)
   [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] E0 mf
   (Vint (cmov_int (generator_hash_accepted false key && generator_hash_accepted true key))) /\
 @literal_hash_to_curve (Alg.AssertionSem option_Monad_Zero) key=
   (if generator_hash_accepted false key && generator_hash_accepted true key
    then if Int.eq flag Int.zero then Some (rescale_field_output ox,rescale_field_output oy) else None
    else None) /\
 hash_public_value key sx sy sz flag ox oy /\
 finv m0 bd base bw outedge cursor N bi mf
   (generator_hash_accepted false key && generator_hash_accepted true key)
   (if generator_hash_accepted false key && generator_hash_accepted true key
    then @Simplicity.Translate.encode (Ty.Prod (Word 8) (Word 8))
      (rescale_field_output ox,rescale_field_output oy) else []) /\
 lframe (fun b _=>~extA m0 bd bw bi b) m0 mf /\readonly_preserved m0 mf.
Proof.
 intros Count SHA SWU Prefixes Output Cap Base Align Source Input RC Max.
 destruct (eval_hash_public_original Hmodel key v_env m0 bd base bs sbase bw outedge cursor N bi edge rc
   Count SHA SWU Prefixes Output Cap Base Align Source Input RC Max)
   as (mf & sx & sy & sz & flag & ox & oy & Call & Value & Final & Frame & RO).
 exists mf,sx,sy,sz,flag,ox,oy;split;[exact Call|];split;
   [exact (hash_public_assertion_result _ _ _ _ _ _ _ Value)|];
   split;[exact Value|];split;[exact Final|];split;assumption.
Qed.
