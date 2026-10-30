(** Exact canonical scalar storage from the original byte parser and overflow output. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_toZ C.jet_read8s_layout C.jet_sx_expr C.jet_sx_state C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_b32_exec C.jet_secp_canonical_scalar
 C.jet_secp_scalar_limb_bridge C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_overflow_numeric C.jet_secp_scalar_set_shape C.jet_secp_scalar_set_flag
 C.jet_secp_xonly_parse_field C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Require Import C.jet_secp_scalar_set_flag_frame.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_scalar_normalize.
Lemma scalar_parser_limbs_canonical (value:Ty.tySem (Word 8)) words:
 scalar_limb_value words=@toZ (WordToZ 8) value mod canonical_group_order ->
 map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem value)))=
 [words 0%nat;words 1%nat;words 2%nat;words 3%nat].
Proof.
 intro Value;rewrite canonical_scalar_normalize_numeric,<-Value.
 unfold scalar_limb_value;rewrite scalar_limbs_of_four_words;cbn [map];rewrite !Int64.repr_unsigned;reflexivity.
Qed.
Lemma scalar_parser_storage_canonical (value:Ty.tySem (Word 8)) words m b:
 scalar_limb_value words=@toZ (WordToZ 8) value mod canonical_group_order ->
 Mem.range_perm m b 0 32 Cur Freeable ->
 (forall i,(i<4)%nat ->Mem.load Mint64 m b (8*Z.of_nat i)=Some (Vlong (words i))) ->
 scalar_at m b 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem value)))).
Proof.
 intros Value Free Loads;rewrite (scalar_parser_limbs_canonical value words Value).
 split;[reflexivity|];split;[lia|];split;[exists 0;reflexivity|];split.
 - change (32<=18446744073709551615);lia.
 - split.
   + intros pos Range;eapply Mem.perm_implies;[apply Free;exact Range|constructor].
   + intros i limb Nth;destruct i as [|[|[|[|i]]]];cbn [nth_error] in Nth;
     try (destruct i;discriminate);inversion Nth;subst limb;apply Loads;lia.
Qed.
Theorem eval_scalar_set_b32_canonical_flag (value:Ty.tySem (Word 8)) b bb ofs bf m:
 b<>bb ->bf<>b ->bf<>bb ->0<=ofs ->ofs+32<=Ptrofs.max_unsigned ->
 Mem.range_perm m b 0 32 Cur Freeable ->Mem.range_perm m bb ofs (ofs+32) Cur Readable ->
 Mem.range_perm m bf 0 4 Cur Freeable ->
 uint8_array_at m bb ofs (map Int.repr (xonly_input_bytes value)) ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_set_b32)
 [Vptr b Ptrofs.zero;Vptr bb (Ptrofs.repr ofs);Vptr bf Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf b 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem value)))) /\
 Mem.load Mint32 mf bf 0=Some (Vint (b2i (Z.leb canonical_group_order (@toZ (WordToZ 8) value)))) /\
 keeps_permissions m mf /\
 lframe (fun block pos=>~foot [(b,0);(bb,ofs);(bf,0)]
  (map rshape scalar_flag_regs) block pos /\block<>bf) m mf /\readonly_preserved m mf.
Proof.
 intros Separate FB FS Lo Hi Free Read Flag Source.
 assert (Loads:forall i,(i<32)%nat ->Mem.load Mint8unsigned m bb (ofs+Z.of_nat i)=
  Some (Vint (Int.repr (nth i (xonly_input_bytes value) 0)))).
 { intros i Index;apply Source;rewrite nth_error_map,(nth_error_nth' _ 0);
   [reflexivity|rewrite xonly_input_length;exact Index]. }
 destruct (eval_scalar_set_b32_flag_frame (xonly_input_bytes value) b bb ofs bf m
  (xonly_input_length value) (xonly_input_bounds value) Separate FB FS Lo Hi Free Read Flag Loads)
 as (mf & Call & Output & Overflow & Value & Keep & Frame & Readonly).
 rewrite xonly_input_value in Value,Overflow.
 exists mf;split;[exact Call|];split.
 - eapply scalar_parser_storage_canonical;[exact Value| |exact Output].
   intros pos Range;apply Keep,Free;exact Range.
 - split;[exact Overflow|];split;[exact Keep|];split;assumption.
Qed.
