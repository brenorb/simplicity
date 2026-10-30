(** Actual hash_to_curve startup and its preservation through public output
    observations. No helper execution or curve-result property is assumed. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.extraMath C.jet_memcpy_model C.jet_ctz_model C.jet_secp_ctz_external_call C.jet_partial
 C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
 C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_field_cmov
 C.jet_secp_rescale_literal C.jet_secp_generator_hash_map C.jet_secp_generator_sha_absorb

 C.jet_secp_sha_startup C.jet_secp_sha_dispatch C.jet_secp_swu_startup
 C.jet_secp_taptweak_writer_state C.jet_secp_initialized_partial_contract
 C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition hash_to_curve_ready m:=secp_sha_startup m /\swu_startup m /\
 (forall prefix,generator_sha_prefix_state prefix m) /\taptweak_dispatch_extent m.
Theorem hash_to_curve_ready_initial m:Genv.init_mem jets_secp.prog=Some m ->hash_to_curve_ready m.
Proof.
 intro Init;split;[apply secp_sha_startup_initial;exact Init|].
 split;[apply swu_startup_initial;exact Init|].
 split;[intro prefix;apply generator_sha_prefix_initial;exact Init|apply taptweak_dispatch_extent_initial;exact Init].
Qed.
Theorem hash_to_curve_ready_exists:exists m,Genv.init_mem jets_secp.prog=Some m /\hash_to_curve_ready m.
Proof.
 destruct secp_sha_startup_exists as(m & Init & Rest).
 exists m;split;[exact Init|apply hash_to_curve_ready_initial;exact Init].
Qed.
Lemma hash_sha_startup_from_dispatch_load m mf:
 secp_sha_startup m ->readonly_preserved m mf ->
 Mem.load Mptr mf secp_sha_dispatch_block 0=Mem.load Mptr m secp_sha_dispatch_block 0 ->secp_sha_startup mf.
Proof.
 intros [[Dispatch Counter][NoWrite NoFree]][Forward Unchanged]Same.
 assert(VC:Mem.valid_block m secp_sha_counter_block)by(eapply load_valid;exact Counter).
 assert(VD:Mem.valid_block m secp_sha_dispatch_block).
 { eapply load_valid;exact Dispatch. }
 split.
 - split.
   + unfold secp_sha_dispatch_ok in *.
     change(Mem.load Mptr mf secp_sha_dispatch_block 0=Some(Vptr(secp_symbol_block jets_secp._sha256_compression_portable)Ptrofs.zero));rewrite Same;exact Dispatch.
   + eapply Mem.load_unchanged_on;[exact Unchanged| |exact Counter].
     intros ofs Range;split;[exact VC|apply NoWrite].
 - split.
   + intros ofs Perm;apply(NoWrite ofs);exact(proj2(Forward _ VC)ofs Writable Perm).
   + intros ofs Perm;apply(NoFree ofs);exact(proj2(Forward _ VD)ofs Freeable Perm).
Qed.

Theorem hash_to_curve_ready_after_output m mf bd base bw outedge cursor bi
 (result:option(Ty.tySem(Ty.Prod(Word 8)(Word 8)))):
 hash_to_curve_ready m ->
 finv m bd base bw outedge cursor 512 bi mf
 (match result with Some _=>true|None=>false end)
 (match result with Some value=>Simplicity.Translate.encode value|None=>[] end) ->
 lframe(fun b _=>~extA m bd bw bi b)m mf ->readonly_preserved m mf ->hash_to_curve_ready mf.
Proof.
 intros(SHA & SWU & Prefix & ValidD & BoundsD)Final Frame Read.
 pose proof(partial_frame_observations(Ty.Prod(Word 8)(Word 8))m bd base bw outedge cursor 512 bi mf result Final Frame)as[_ Loads].
 assert(SmallOutput:write_frame_at m bd base bw outedge cursor 256).
 { eapply write_frame_at_le with(count:=512);[lia|exact(proj1(proj2 Final))]. }
 destruct(small_block_output_separate m secp_sha_dispatch_block 8 bd base bw outedge cursor ltac:(lia)BoundsD SmallOutput)as[Dst Word].
 assert(Dispatch:Mem.load Mptr mf secp_sha_dispatch_block 0=Mem.load Mptr m secp_sha_dispatch_block 0).
 { apply Loads;[exact ValidD|left;congruence|left;congruence]. }
 split;[eapply hash_sha_startup_from_dispatch_load;[exact SHA|exact Read|exact Dispatch]|].
 split;[eapply swu_startup_preserved;[exact SWU|exact Read]|].
 split;[intro prefix;eapply generator_sha_prefix_preserved;[apply Prefix|exact Read]|].
 split;[exact(proj1(proj1 Read _ ValidD))|].
 eapply block_extent_forward;[exact ValidD|exact BoundsD|exact(proj1 Read)].
Qed.
