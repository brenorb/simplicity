(** Actual read32s in the frozen secp program on an arbitrary valid input cursor. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_encoding C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_read32s_layout C.jet_word32_chunks
 C.jet_uint32_array_init C.jet_sha_ctx8_model C.jet_sx_mem C.jet_secp_linkage
 C.jet_clight_internal_frame C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Require C.jets.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition secp_read32_internal_table:=
 [(C.jets._LSBclear,C.jets.f_LSBclear);(C.jets._LSBkeep,C.jets.f_LSBkeep);
 (C.jets._simplicity_read32,C.jets.f_simplicity_read32);(C.jets._read32s,C.jets.f_read32s)].
Lemma secp_read32_internal_ok:internal_table_ok secp_ge secp_read32_internal_table.
Proof.
 intros id fd Lookup;apply internal_lookup_in in Lookup;cbn [secp_read32_internal_table In] in Lookup.
 repeat destruct Lookup as [Same|Lookup];try contradiction;inversion Same;subst id fd;clear Same.
 all:split.
 all:try solve[match goal with |-exists b,Genv.find_symbol _ ?id=Some b /\ _=>
 exists (secp_symbol_block id) end;split;vm_compute;reflexivity].
 all:split;vm_compute;reflexivity.
Qed.
Local Opaque secp_ge Translate.encode.
Lemma secp_read32_preserved m args t mf result:
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_read32s) args t mf result ->readonly_preserved m mf.
Proof.
 intro Run;eapply (proj2 (internal_exec_preserved _ _ secp_read32_internal_ok));[exact Run|].
 exists C.jets._read32s,C.jets.f_read32s;split;reflexivity.
Qed.
Theorem eval_secp_public_hash_read (h:Ty.tySem (Word 8)) m bo bf bi edge cursor:
 0<=cursor ->cursor+256<=Int64.max_unsigned ->bo<>bf ->bf<>bi ->bo<>bi ->
 Mem.range_perm m bo 0 32 Cur Freeable ->Mem.range_perm m bf 0 16 Cur Freeable ->
 frame_fields_at m bf 0 bi edge cursor ->frame_input_cells_at m bi edge cursor (Translate.encode h) ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_read32s)
 [Vptr bo Ptrofs.zero;Vlong (Int64.repr 8);Vptr bf Ptrofs.zero] E0 mf Vundef /\
 uint32_array_at mf bo 0 (state_regs h) /\frame_fields_at mf bf 0 bi edge (cursor+256) /\
 keeps_permissions m mf /\lframe (fun b _=>b<>bf /\b<>bo) m mf /\readonly_preserved m mf.
Proof.
 intros Cursor Max OF FI OI FO FF Fields Input.
 assert (Length:length (word32_chunks 3 h)=8%nat) by apply word32_chunks_length.
 assert (CursorWritable:Mem.valid_access m Mint64 bf (0+8) Writable).
 { split;[|change (8|8);exists 1;reflexivity];intros pos Range;eapply Mem.perm_implies;
 [apply FF;change (8<=pos<8+8) in Range;lia|constructor]. }
 destruct (eval_read32s_layout m bo 0 bf 0 bi edge cursor (word32_chunks 3 h) ltac:(lia)
 ltac:(rewrite Length;change (32<=18446744073709551615);lia) ltac:(exists 0;reflexivity)
 ltac:(rewrite Length;change (Mem.range_perm m bo 0 32 Cur Writable);intros pos Range;eapply Mem.perm_implies;[apply FO;exact Range|constructor])
 (not_eq_sym OF) FI OI ltac:(unfold frame_base_valid;change (0<=0 /\0+16<=18446744073709551615);lia)
 Cursor ltac:(rewrite Length;exact Max) Fields CursorWritable
 (frame_input_word32_chunks m bi edge cursor 3 h Input)) as
 (mf & ReadCore & Words & FieldsF & Loads & Perms & Valid).
 rewrite Length in ReadCore,FieldsF.
 assert (Read:Clight2.eval_funcall secp_ge m (Internal C.jets.f_read32s)
 [Vptr bo Ptrofs.zero;Vlong (Int64.repr 8);Vptr bf Ptrofs.zero] E0 mf Vundef).
 { eapply secp_transport_call;[unfold secp_core_helpers;do 17 right;left;reflexivity|exact ReadCore]. }
 exists mf;split;[exact Read|];split;[exact Words|];split;[exact FieldsF|];split;[exact Perms|];split.
 - split.
   + intros chunk b ofs Old Outside;apply Loads;
     [left;exact (proj1 (Outside ofs ltac:(pose proof (size_chunk_pos chunk);lia)))|
      left;exact (proj2 (Outside ofs ltac:(pose proof (size_chunk_pos chunk);lia)))].
   + split;[intros;apply Perms;assumption|exact Valid].
 - eapply secp_read32_preserved;exact Read.
Qed.

Require Import C.jets_secp C.jet_secp_curve_statements C.jet_secp_sha_init_copy C.jet_secp_generator_sha_start
 C.jet_secp_root_chain_owned.
Definition secp_local_hash_read sid:=curve_call _read32s C.jets.f_read32s None
 [Efield (Evar sid generator_sha_state_type) _s (tarray tuint 8);Econst_int (Int.repr 8) tint;
 Etempvar _src (tptr (Tstruct _frameItem noattr))].
Lemma taptweak_hash_read_source:root_drop_statements 7 (fn_body f_simplicity_generic_taptweak)=
 Ssequence (secp_local_hash_read _input_hash) (root_drop_statements 8 (fn_body f_simplicity_generic_taptweak)).
Proof. reflexivity. Qed.
Theorem exec_secp_local_hash_read sid e le m mf bo bf:
 e!_read32s=None ->e!sid=Some (bo,generator_sha_state_type) ->le!_src=Some (Vptr bf Ptrofs.zero) ->
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_read32s)
 [Vptr bo Ptrofs.zero;Vlong (Int64.repr 8);Vptr bf Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m (secp_local_hash_read sid) E0 le mf Out_normal.
Proof.
 intros Global State Source Read.
 destruct (secp_core_helpers_entries C.jets._read32s C.jets.f_read32s
 ltac:(unfold secp_core_helpers;do 17 right;left;reflexivity)) as (b0 & b & S0 & F0 & Symbol & Function).
 unfold secp_local_hash_read,curve_call;eapply exec_Scall with (vf:=Vptr b Ptrofs.zero)
 (f:=Internal C.jets.f_read32s) (vargs:=[Vptr bo Ptrofs.zero;Vlong (Int64.repr 8);Vptr bf Ptrofs.zero]) (vres:=Vundef).
 - reflexivity.
 - eapply eval_Elvalue.
   { eapply eval_Evar_global;[exact Global|exact Symbol]. }
   apply deref_loc_reference;reflexivity.
 - eapply eval_Econs;[apply eval_sha_local_state;exact State|reflexivity|].
   eapply eval_Econs;[constructor|reflexivity|].
   eapply eval_Econs;[apply eval_Etempvar;exact Source|reflexivity|constructor].
 - exact Function.
 - reflexivity.
 - exact Read.
Qed.
