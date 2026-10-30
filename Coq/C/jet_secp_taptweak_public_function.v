(** Complete original Bitcoin TapTweak wrapper, including its by-value source copy. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jets_secp C.jet_secp_linkage C.jet_sx_mem C.jet_frame_inv C.jet_frame_layout
 C.jet_input_layout C.jet_output_layout C.jet_write_layout C.jet_encoding C.jet_buffer_input C.jet_readBit_layout
 C.jet_memcpy_model C.jet_memset_model C.jet_ctz_model C.jet_secp_curve_frame
 C.jet_secp_taptweak_function C.jet_secp_taptweak_public_support C.jet_secp_taptweak_tag C.jet_secp_taptweak_hash
 C.jet_secp_taptweak_parsed_native C.jet_secp_taptweak_finish C.jet_secp_taptweak_writer_state
 C.jet_clight_forward C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge taptweak_output taptweak_result taptweak_hash_word.
Theorem eval_bitcoin_taptweak_public (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 (pk h:Ty.tySem (Word 8)) ve m bd base bs sbase bin bw edge outedge rc cursor:
 taptweak_ready m ->frame_base_valid sbase ->(8|sbase) ->frame_fields_at m bs sbase bin edge rc ->
 0<=rc ->rc+512<=Int64.max_unsigned ->
 frame_input_cells_at m bin edge rc (@Translate.encode (Word 9) (pk,h)) ->write_frame_at m bd base bw outedge cursor 256 ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_simplicity_bitcoin_build_taptweak)
 [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);ve] E0 mf
 (Vint (bit_int (taptweak_result (taptweak_hash_word pk h) pk))) /\
 (match taptweak_output (taptweak_hash_word pk h) pk with None=>True|Some value=>
 frame_output_cells_at mf bw outedge cursor (Translate.encode value) /\write_prefix_at m mf bw outedge cursor /\frame_fields_at mf bd base bw outedge (cursor-256) end) /\
 (forall chunk b ofs,Mem.valid_block m b ->
 (b<>bd \/ofs+size_chunk chunk<=base+8 \/base+16<=ofs) ->
 (b<>bw \/ofs+size_chunk chunk<=outedge+8*((cursor-256)/64) \/write_word_address outedge cursor+8<=ofs) ->
 Mem.load chunk mf b ofs=Mem.load chunk m b ofs) /\mem_forward m mf /\taptweak_ready mf.
Proof.
 intros Ready Base Align Fields RC Max Input Output.
 assert (VS:Mem.valid_block m bs) by (eapply load_valid;exact (proj1 Fields)).
 assert (VI:Mem.valid_block m bin) by (eapply taptweak_input_valid;exact Input).
 assert (VD:Mem.valid_block m bd) by (eapply load_valid;exact (proj1 (proj1 (proj2 Output)))).
 assert (VW:Mem.valid_block m bw).
 { destruct (write_frame_at_head m bd base bw outedge cursor 256 ltac:(lia) Output) as (_ & _ & _ & w & Load);eapply load_valid;exact Load. }
 destruct (taptweak_public_entry m (Vptr bd (Ptrofs.repr base)) (Vptr bs (Ptrofs.repr sbase)) ve)
 as (mi & bf & Entry & Fresh & FreeI & FrameI & KeepI & ReadI).
 pose (le:=taptweak_public_temps (Vptr bd (Ptrofs.repr base)) (Vptr bs (Ptrofs.repr sbase)) ve).
 assert (FieldsI:frame_fields_at mi bs sbase bin edge rc).
 { destruct Fields as [Edge Cur];split;rewrite (proj1 FrameI) by (try exact VS;intros;exact I);assumption. }
 destruct (taptweak_public_copy_from_fields mi le bf bs sbase bin edge rc Base Align
  ltac:(pose proof (Fresh bs VS);congruence) eq_refl FieldsI FreeI)
 as (mc & CopyStmt & LocalFields & FreeC & FrameC & ReadC).
 assert (Frame0C:lframe (fun _ _=>True) m mc).
 { assert (Old:lframe (fun b _=>Mem.valid_block m b) m mc).
   { eapply lframe_trans.
     - eapply lframe_implies;[exact FrameI|intros;exact I].
     - eapply lframe_implies;[exact FrameC|intros b pos Valid _;exact (Fresh b Valid)]. }
   eapply lframe_implies;[exact Old|intros b pos _ Valid;exact Valid]. }
 assert (Forward0C:mem_forward m mc) by (eapply mem_forward_trans;[exact (proj1 ReadI)|exact (proj1 ReadC)]).
 assert (StartupC:taptweak_startup mc) by (eapply taptweak_startup_framed;[exact (proj1 Ready)|exact Forward0C|exact Frame0C]).
 assert (ReadyC:taptweak_ready mc) by (eapply taptweak_ready_forward;[exact Ready|exact StartupC|exact Forward0C]).
 assert (InputC:frame_input_cells_at mc bin edge rc (@Translate.encode (Word 9) (pk,h))).
 { eapply buffer_input_cells_preserved;[|exact Input];intros ofs w Load;rewrite (proj1 Frame0C) by (try exact VI;intros;exact I);exact Load. }
 assert (OutputC:write_frame_at mc bd base bw outedge cursor 256).
 { eapply write_frame_at_framed;[exact Output|exact Frame0C|intros;split;exact I]. }
 destruct (eval_generic_taptweak Copy Clear Count pk h mc bd base bf bin bw edge outedge rc cursor ReadyC FreeC
 ltac:(pose proof (Fresh bin VI);congruence) ltac:(pose proof (Fresh bd VD);congruence)
 ltac:(pose proof (Fresh bw VW);congruence) RC Max LocalFields InputC OutputC)
 as (mb & Call & Observe & FreeB & LoadsB & ForwardB & ReadyB).
 destruct (taptweak_public_free mb bf FreeB) as (mf & Frees & FrameF & ReadF).
 assert (StartupF:taptweak_startup mf).
 { eapply taptweak_startup_owned_forward with (slots:=[(bf,16)]);[exact (proj1 ReadyB)|exact (proj1 ReadF)| |].
 - intros b hi [Slot|[]];inversion Slot;subst b hi;split;[clear;lia|exact FreeB].
 - eapply lframe_implies;[exact FrameF|intros b pos Outside Valid;cbn [map fst In] in Outside;intuition congruence]. }
 assert (ReadyF:taptweak_ready mf) by (eapply taptweak_ready_forward;[exact ReadyB|exact StartupF|exact (proj1 ReadF)]).
 assert (VBW:Mem.valid_block mb bw) by (exact (proj1 (ForwardB _ (proj1 (Forward0C _ VW))))).
 assert (VBD:Mem.valid_block mb bd) by (exact (proj1 (ForwardB _ (proj1 (Forward0C _ VD))))).
 pose (result:=taptweak_result (taptweak_hash_word pk h) pk).
 pose (lf:=PTree.set _t'1 (Vint (bit_int result)) le).
 exists mf;split.
 - eapply eval_funcall_internal with (e:=taptweak_public_env bf) (le1:=le) (le2:=lf) (m1:=mi) (m2:=mb)
 (out:=Out_return (Some (Vint (bit_int result),tbool))).
   + exact Entry.
   + rewrite taptweak_public_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=le);[exact CopyStmt|].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mb) (le1:=lf).
     * eapply exec_taptweak_public_call;[reflexivity|exact Call].
     * apply exec_Sreturn_some;apply eval_Etempvar;apply PTree.gss.
   + split;[discriminate|unfold result;destruct (taptweak_result (taptweak_hash_word pk h) pk);reflexivity].
   + exact Frees.
 - split.
   + destruct (taptweak_output (taptweak_hash_word pk h) pk) as [value|];[|exact I].
     destruct Observe as (Cells & Prefix & Cur);split.
     * intros i c Nth;destruct c as [bit|];cbn [cell_matches] in *.
       -- eapply taptweak_output_bit_preserved;[|exact (Cells i (Some bit) Nth)].
          intros ofs w Load;rewrite (proj1 FrameF Mint64 bw ofs VBW);[exact Load|intros;apply Fresh;exact VW].
       -- destruct (Cells i None Nth) as (bit & Bit);exists bit;eapply taptweak_output_bit_preserved;[|exact Bit].
          intros ofs w Load;rewrite (proj1 FrameF Mint64 bw ofs VBW);[exact Load|intros;apply Fresh;exact VW].
     * split.
       -- eapply write_prefix_at_preserved with (mr:=mc) (me:=mb).
          ++ intros ofs w Load;rewrite (proj1 Frame0C) by (try exact VW;intros;exact I);exact Load.
          ++ intros ofs w Load;rewrite (proj1 FrameF Mint64 bw ofs VBW);[exact Load|intros;apply Fresh;exact VW].
          ++ exact Prefix.
       -- destruct Cur as [Edge Offset];split;rewrite (proj1 FrameF) by (try exact VBD;intros;apply Fresh;exact VD);assumption.
   + split.
     * intros chunk b ofs Valid OD OW.
       rewrite (proj1 FrameF chunk b ofs (proj1 (ForwardB _ (proj1 (Forward0C _ Valid))))) by (intros;apply Fresh;exact Valid).
       rewrite LoadsB;[|exact (proj1 (Forward0C _ Valid))|exact (Fresh b Valid)|exact OD|exact OW].
       apply (proj1 Frame0C);[exact Valid|intros;exact I].
     * split;[eapply mem_forward_trans;[exact Forward0C|];eapply mem_forward_trans;[exact ForwardB|exact (proj1 ReadF)]|exact ReadyF].
Set Default Timeout 60.
Qed.
Set Default Timeout 10.
