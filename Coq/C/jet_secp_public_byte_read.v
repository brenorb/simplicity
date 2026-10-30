(** Original byte-list reader with ownership, framing and readonly preservation.
    Used for both the 32-byte message and 64-byte signature inputs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_encoding C.jet_word_repr C.jet_read8s_layout C.jet_buffer_input C.jet_input_layout C.jet_frame_layout
 C.jet_sx_mem C.jet_secp_linkage C.jet_secp_frame C.jet_secp_hash_public_read
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Require C.jets.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Translate.encode.
Theorem eval_secp_public_byte_read (xs:list (Ty.tySem (Word 3))) m bo bf bi edge cursor:
 Z.of_nat (length xs)<=Ptrofs.max_unsigned ->0<=cursor ->cursor+8*Z.of_nat (length xs)<=Int64.max_unsigned ->
 bo<>bf ->bf<>bi ->bo<>bi ->
 Mem.range_perm m bo 0 (Z.of_nat (length xs)) Cur Freeable ->Mem.range_perm m bf 0 16 Cur Freeable ->
 frame_fields_at m bf 0 bi edge cursor ->
 frame_input_cells_at m bi edge cursor (concat (map (@Translate.encode (Word 3)) xs)) ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_read8s)
 [Vptr bo Ptrofs.zero;Vlong (Int64.repr (Z.of_nat (length xs)));Vptr bf Ptrofs.zero] E0 mf Vundef /\
 uint8_array_at mf bo 0 (map word8_array_value xs) /\
 frame_fields_at mf bf 0 bi edge (cursor+8*Z.of_nat (length xs)) /\
 keeps_permissions m mf /\lframe (fun b _=>b<>bf /\b<>bo) m mf /\readonly_preserved m mf.
Proof.
 intros Length Cursor Max OF FI OI Owned FreeFrame Source Input.
 assert (OutputWritable:Mem.range_perm m bo 0 (0+Z.of_nat (length xs)) Cur Writable).
 { intros pos Range;eapply Mem.perm_implies;[apply Owned;lia|constructor]. }
 assert (CursorWritable:Mem.valid_access m Mint64 bf (0+8) Writable).
 { split;[|change (8|8);exists 1;reflexivity].
   intros pos Range;eapply Mem.perm_implies;[apply FreeFrame;change (8<=pos<8+8) in Range;lia|constructor]. }
 destruct (secp_read8s_layout m bo 0 bf 0 bi edge cursor xs ltac:(clear;lia)
  ltac:(rewrite Z.add_0_l;exact Length) OutputWritable (not_eq_sym OF) FI OI
  ltac:(unfold frame_base_valid;change (0<=0 /\0+16<=18446744073709551615);clear;lia)
  Cursor Max Source CursorWritable (proj1 (frame_input_byte_list m bi edge cursor xs) Input))
 as (mf & Read & Bytes & Fields & Loads & Perms & Valid).
 exists mf;split;[exact Read|];split;[exact Bytes|];split;[exact Fields|];split;[exact Perms|];split.
 - split.
   + intros chunk b ofs Old Outside;apply Loads.
     * left;exact (proj1 (Outside ofs ltac:(pose proof (size_chunk_pos chunk);lia))).
     * left;exact (proj2 (Outside ofs ltac:(pose proof (size_chunk_pos chunk);lia))).
   + split;[intros;apply Perms;assumption|exact Valid].
 - eapply hash_raw_reader_preserved;exact Read.
Qed.

Lemma uint8_array_split_app m b base xs ys:
 uint8_array_at m b base (xs++ys) ->uint8_array_at m b base xs /\
 uint8_array_at m b (base+Z.of_nat (length xs)) ys.
Proof.
 intro Bytes;split.
 - intros i x Nth;apply Bytes;rewrite nth_error_app1;[exact Nth|].
   apply nth_error_Some;rewrite Nth;discriminate.
 - intros i x Nth.
   replace (base+Z.of_nat (length xs)+Z.of_nat i) with (base+Z.of_nat (length xs+i)) by (rewrite Nat2Z.inj_add;lia).
   apply Bytes;rewrite nth_error_app2 by lia;replace (length xs+i-length xs)%nat with i by lia;exact Nth.
Qed.
Lemma uint8_array_framed m mf b base xs P:
 uint8_array_at m b base xs ->lframe P m mf ->(forall pos,P b pos) ->uint8_array_at mf b base xs.
Proof.
 intros Bytes Frame Outside i x Nth;pose proof (Bytes i x Nth) as Load.
 assert (Valid:Mem.valid_block m b).
 { apply Mem.load_valid_access in Load;eapply Mem.valid_access_valid_block;
   eapply Mem.valid_access_implies;[exact Load|constructor]. }
 rewrite (proj1 Frame Mint8unsigned b (base+Z.of_nat i) Valid);[exact Load|intros;apply Outside].
Qed.
