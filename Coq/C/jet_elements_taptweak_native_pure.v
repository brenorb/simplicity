(** Complete storage and permission results of the original field serializer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Memory Values Ctypes Clight ClightBigstep Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_rep
 C.jets_secp C.jet_secp_linkage C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_secp_b32_exec C.jet_secp_b32_full
 C.jet_read8s_layout C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve
 C.jet_clight_internal_permissions.
Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_sx_exec C.jet_sx_mem C.jet_readBit_layout C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_square_columns C.jet_secp_field_mul_small
 C.jet_secp_field_negate_separate C.jet_secp_field_odd_words C.jet_secp_affine_odd_y
 C.jet_secp_affine_negate_words C.jet_secp_affine_flag_read C.jet_secp_decompress_statements
 C.jet_secp_swu_word_parity C.jet_secp_closed_helpers C.jet_clight_internal_preserve.
Require Import C.jet_secp_b32_owned C.jet_secp_extrakeys_even_y
 C.jet_elements_taptweak_curve_transport C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_parser C.jet_secp_xonly_tweak_entry C.jet_secp_curve_statements.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_has_secp256k1_extrakeys_ge_even_y:
 In (_secp256k1_extrakeys_ge_even_y,f_secp256k1_extrakeys_ge_even_y) elements_taptweak_curve_helpers.
Proof.
 assert(Found:find(fun it=>Pos.eqb(fst it)_secp256k1_extrakeys_ge_even_y)elements_taptweak_curve_helpers=
 Some(_secp256k1_extrakeys_ge_even_y,f_secp256k1_extrakeys_ge_even_y))by(vm_compute;reflexivity).
 apply find_some in Found;exact(proj1 Found).
Qed.
Lemma elements_taptweak_has_secp256k1_fe_get_b32:
 In (_secp256k1_fe_get_b32,f_secp256k1_fe_get_b32) elements_taptweak_curve_helpers.
Proof.
 assert(Found:find(fun it=>Pos.eqb(fst it)_secp256k1_fe_get_b32)elements_taptweak_curve_helpers=
 Some(_secp256k1_fe_get_b32,f_secp256k1_fe_get_b32))by(vm_compute;reflexivity).
 apply find_some in Found;exact(proj1 Found).
Qed.
Local Opaque secp_ge elements_taptweak_ge.
Theorem eval_elements_taptweak_even_y w m b:
 mul_small_input_bounds w ->square_input_bounds w ->fe_at m b 40 (words5 w) ->
 Mem.range_perm m b 0 88 Cur Freeable ->Mem.load Mint32 m b 80=Some (Vint Int.zero) ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_extrakeys_ge_even_y)
 [Vptr b Ptrofs.zero] E0 mf (Vint (bit_int (field_words_odd w))) /\
 fe_at mf b 40 (words5 (extrakeys_even_y_words w)) /\square_input_bounds (extrakeys_even_y_words w) /\
 Mem.range_perm mf b 0 88 Cur Freeable /\
 lframe (fun bx pos=>bx<>b \/pos<40 \/80<=pos) m mf /\readonly_preserved m mf.
Proof.
 intros Small Bounds Field Owned Flag.
 destruct(eval_extrakeys_ge_even_y w m b Small Bounds Field Owned Flag)as(mf & Call & Memory).
 exists mf;split;[|exact Memory].
 exact(elements_taptweak_curve_transport _ _ m _ _ mf _ elements_taptweak_has_secp256k1_extrakeys_ge_even_y Call).
Qed.
Theorem eval_elements_taptweak_fe_get_b32_owned m b offset bf base value:
 0<=value<2^256 ->0<=offset ->offset+32<=Ptrofs.max_unsigned ->
 Mem.range_perm m b offset (offset+32) Cur Freeable ->
 fe_at m bf base (map Int64.repr (fe_limbs_of value)) ->b<>bf ->
 exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_fe_get_b32)
  [Vptr b (Ptrofs.repr offset);Vptr bf (Ptrofs.repr base)] E0 mf Vundef /\
 uint8_array_at mf b offset (map Int.repr (be_bytes value)) /\
 fe_at mf bf base (map Int64.repr (fe_limbs_of value)) /\
 keeps_permissions m mf /\
 lframe (fun block pos=>~foot [(b,offset);(bf,base)]
  (map rshape [mkreg (jet_secp_fe_b32.byte_undef 0 32) true None;
   mkreg (u64_cells 0 (vars5 0)) false None]) block pos) m mf /\readonly_preserved m mf.
Proof.
 intros Range Offset Max Owned Field Separate.
 destruct(eval_fe_get_b32_owned m b offset bf base value Range Offset Max Owned Field Separate)as(mf & Call & Memory).
 exists mf;split;[|exact Memory].
 exact(elements_taptweak_curve_transport _ _ m _ _ mf _ elements_taptweak_has_secp256k1_fe_get_b32 Call).
Qed.

Lemma elements_taptweak_single_point_blocks bk:
 blocks_of_env elements_taptweak_ge(xonly_tweak_env bk)=[(bk,0,88)].
Proof.
 change ([(bk,0,sizeof elements_taptweak_ge curve_ge_type)]=[(bk,0,88)]).
 rewrite(proj2 elements_taptweak_parser_sizes);reflexivity.
Qed.

Theorem elements_taptweak_single_point_free m bk:
 Mem.range_perm m bk 0 88 Cur Freeable ->exists mf,
 Mem.free_list m(blocks_of_env elements_taptweak_ge(xonly_tweak_env bk))=Some mf /\
 lframe(fun b _=>b<>bk)m mf /\readonly_preserved m mf.
Proof.
 intro Owned;destruct(xonly_tweak_free m bk Owned)as(mf & Free & Memory).
 exists mf;split;[|exact Memory].
 rewrite elements_taptweak_single_point_blocks;rewrite xonly_tweak_blocks in Free;exact Free.
Qed.
