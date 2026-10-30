(** Whole original hash_to_curve execution from approved models and actual
    startup. This characterizes the code and retains the unresolved infinity
    comparison explicitly; it is not a canonical public equivalence theorem. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.extraMath C.jet_memcpy_model C.jet_ctz_model C.jet_secp_ctz_external_call C.jet_partial
 C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
 C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_field_cmov
 C.jet_secp_rescale_literal C.jet_secp_generator_hash_map C.jet_secp_generator_sha_absorb
 C.jet_secp_hash_public_call C.jet_secp_hash_to_curve_spec C.jet_secp_hash_to_curve_compare
 C.jet_secp_sha_startup C.jet_secp_sha_dispatch C.jet_secp_swu_startup
 C.jet_secp_taptweak_writer_state C.jet_secp_initialized_partial_contract
 C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_hash_to_curve Simplicity.Translate.encode rescale_field_output.
Require Import C.jet_secp_hash_startup.
Theorem eval_hash_to_curve_initialized_characterization (Copy:memcpy_model)(Count:ctz_model)
 (key:Ty.tySem(Word 8)) ve m bd base bs sbase bi bw edge outedge cursor rc:
 hash_to_curve_ready m ->frame_base_valid sbase ->(8|sbase) ->frame_fields_at m bs sbase bi edge rc ->
 0<=rc ->rc+256<=Int64.max_unsigned ->frame_input_cells_at m bi edge rc(Simplicity.Translate.encode key) ->
 write_frame_at m bd base bw outedge cursor 512 ->exists mf sx sy sz flag ox oy,
 Clight2.eval_funcall secp_ge m(Internal f_simplicity_hash_to_curve)
 [Vptr bd(Ptrofs.repr base);Vptr bs(Ptrofs.repr sbase);ve]E0 mf
 (Vint(cmov_int(generator_hash_accepted false key &&generator_hash_accepted true key))) /\
 @literal_hash_to_curve(Alg.AssertionSem option_Monad_Zero)key=
 (if generator_hash_accepted false key &&generator_hash_accepted true key then
  if Int.eq flag Int.zero then Some(rescale_field_output ox,rescale_field_output oy)else None else None) /\
 hash_public_value key sx sy sz flag ox oy /\
 finv m bd base bw outedge cursor 512 bi mf
 (generator_hash_accepted false key &&generator_hash_accepted true key)
 (if generator_hash_accepted false key &&generator_hash_accepted true key then
  @Simplicity.Translate.encode(Ty.Prod(Word 8)(Word 8))(rescale_field_output ox,rescale_field_output oy)else []) /\
 lframe(fun b _=>~extA m bd bw bi b)m mf /\readonly_preserved m mf /\hash_to_curve_ready mf.
Proof.
 intros Ready Base Align Source RC Max Input Output.
 destruct Ready as(SHA & SWU & Prefix & ValidD & BoundsD).
 destruct(eval_hash_to_curve_compared Copy key ve m bd base bs sbase bw outedge cursor 512 bi edge rc
 ltac:(intros mc x Nonzero;apply eval_ctz64_from_external;exact(Count _ mc x Nonzero))SHA SWU Prefix Output ltac:(lia)Base Align Source Input RC Max)
 as(mf & sx & sy & sz & flag & ox & oy & Call & Spec & Value & Final & Frame & Read).
 assert(ReadyF:hash_to_curve_ready mf).
 { eapply hash_to_curve_ready_after_output with(result:=if generator_hash_accepted false key &&generator_hash_accepted true key then
 Some(rescale_field_output ox,rescale_field_output oy)else None).
 - split;[exact SHA|];split;[exact SWU|];split;[exact Prefix|split;assumption].
 - destruct(generator_hash_accepted false key &&generator_hash_accepted true key);exact Final.
 - exact Frame.
 - exact Read. }
 exists mf,sx,sy,sz,flag,ox,oy;split;[exact Call|];split;[exact Spec|];split;[exact Value|];
 split;[exact Final|];split;[exact Frame|];split;[exact Read|exact ReadyF].
Qed.
