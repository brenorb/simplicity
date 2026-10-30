(** Complete original generic TapTweak callee, including entry and all eleven frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jets_secp C.jet_secp_linkage C.jet_sx_mem C.jet_frame_inv C.jet_frame_spec C.jet_frame_layout
 C.jet_input_layout C.jet_output_layout C.jet_write_layout C.jet_encoding C.jet_buffer_input C.jet_word_repr
 C.jet_memcpy_model C.jet_memset_model C.jet_ctz_model C.jet_readBit_layout C.jet_secp_curve_frame
 C.jet_secp_taptweak_entry C.jet_secp_taptweak_body C.jet_secp_taptweak_tag C.jet_secp_taptweak_hash
 C.jet_secp_taptweak_parsed_native C.jet_secp_taptweak_finish C.jet_secp_taptweak_writer_state
 C.jet_clight_forward C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma taptweak_input_valid m bin edge rc (pk h:Ty.tySem (Word 8)):
 frame_input_cells_at m bin edge rc (@Translate.encode (Word 9) (pk,h)) ->Mem.valid_block m bin.
Proof.
 intro Input;apply frame_input_word_at_encode in Input.
 specialize (Input 0%nat (Z.testbit (@toZ (WordToZ 9) (pk,h)) 511)
 ltac:(apply nth_error_word_bits;change (0<512)%nat;lia)).
 destruct Input as (_ & _ & w & Load & _);eapply load_valid;exact Load.
Qed.
Lemma taptweak_output_bit_preserved m mf bw edge q bit:
 (forall ofs w,Mem.load Mint64 m bw ofs=Some (Vlong w) ->Mem.load Mint64 mf bw ofs=Some (Vlong w)) ->
 frame_output_bit_at m bw edge q bit ->frame_output_bit_at mf bw edge q bit.
Proof. intros Keep (Nonneg & w & Load & Eq);split;[exact Nonneg|exists w;split;[apply Keep;exact Load|exact Eq]]. Qed.
Local Opaque secp_ge taptweak_output taptweak_result taptweak_hash_word.
Theorem eval_generic_taptweak (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 (pk h:Ty.tySem (Word 8)) m bd base bf bin bw edge outedge rc cursor:
 taptweak_ready m ->Mem.range_perm m bf 0 16 Cur Freeable ->bf<>bin ->bf<>bd ->bf<>bw ->
 0<=rc ->rc+512<=Int64.max_unsigned ->frame_fields_at m bf 0 bin edge rc ->
 frame_input_cells_at m bin edge rc (@Translate.encode (Word 9) (pk,h)) ->write_frame_at m bd base bw outedge cursor 256 ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_simplicity_generic_taptweak)
 [Vptr bd (Ptrofs.repr base);Vptr bf Ptrofs.zero;Vptr taptweak_tag_block Ptrofs.zero;Vlong (Int64.repr 8)] E0 mf
 (Vint (bit_int (taptweak_result (taptweak_hash_word pk h) pk))) /\
 (match taptweak_output (taptweak_hash_word pk h) pk with None=>True|Some value=>
 frame_output_cells_at mf bw outedge cursor (Translate.encode value) /\write_prefix_at m mf bw outedge cursor /\frame_fields_at mf bd base bw outedge (cursor-256) end) /\
 Mem.range_perm mf bf 0 16 Cur Freeable /\
 (forall chunk b ofs,Mem.valid_block m b ->b<>bf ->
 (b<>bd \/ofs+size_chunk chunk<=base+8 \/base+16<=ofs) ->
 (b<>bw \/ofs+size_chunk chunk<=outedge+8*((cursor-256)/64) \/write_word_address outedge cursor+8<=ofs) ->
 Mem.load chunk mf b ofs=Mem.load chunk m b ofs) /\mem_forward m mf /\taptweak_ready mf.
Proof.
 intros Ready FreeSource FI FD FW RC Max Fields Input Output.
 assert (VF:Mem.valid_block m bf) by (eapply Mem.perm_valid_block;apply (FreeSource 0);clear;lia).
 assert (VI:Mem.valid_block m bin) by (eapply taptweak_input_valid;exact Input).
 assert (VD:Mem.valid_block m bd) by (eapply load_valid;exact (proj1 (proj1 (proj2 Output)))).
 assert (VW:Mem.valid_block m bw).
 { destruct (write_frame_at_head m bd base bw outedge cursor 256 ltac:(lia) Output) as (_ & _ & _ & w & Load);eapply load_valid;exact Load. }
 destruct (taptweak_entry m (Vptr bd (Ptrofs.repr base)) (Vptr bf Ptrofs.zero)
 (Vptr taptweak_tag_block Ptrofs.zero) (Vlong (Int64.repr 8))) as
 (mi & bb & bi & bo & bp & bt & bh & bs & bc & bc1 & br & br1 & Entry & Distinct & Fresh & Private & FrameI & KeepI & ReadI).
 pose (le:=taptweak_temps (Vptr bd (Ptrofs.repr base)) (Vptr bf Ptrofs.zero)
 (Vptr taptweak_tag_block Ptrofs.zero) (Vlong (Int64.repr 8))).
 pose proof (Fresh bf VF) as OutsideF;pose proof (Fresh bin VI) as OutsideI.
 assert (AllSep:NoDup (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1++[bf;bin])).
 { clear -Distinct OutsideF OutsideI FI;unfold taptweak_locals in *;cbn [app] in *;
 repeat rewrite NoDup_cons_iff in *;repeat rewrite not_in_cons in *;cbn [In] in *;
 repeat split;try apply NoDup_nil;intuition congruence. }
 assert (OutsideD:~In bd (taptweak_body_locals bb bi bo bp bt bh bs bc bc1 br br1 bf)).
 { unfold taptweak_body_locals;rewrite in_app_iff;cbn [In];pose proof (Fresh bd VD);intuition congruence. }
 assert (OutsideW:~In bw (taptweak_body_locals bb bi bo bp bt bh bs bc bc1 br br1 bf)).
 { unfold taptweak_body_locals;rewrite in_app_iff;cbn [In];pose proof (Fresh bw VW);intuition congruence. }
 assert (OwnedI:forall b hi,In (b,hi) (taptweak_body_storage bb bi bo bp bt bh bs bc bc1 br br1 bf) ->Mem.range_perm mi b 0 hi Cur Freeable).
 { intros b hi Slot;apply in_app_iff in Slot as [Slot|[Slot|[]]].
 - apply Private;exact Slot.
 - inversion Slot;subst b hi;intros pos Range;apply KeepI,FreeSource;exact Range. }
 assert (StartupI:taptweak_startup mi) by (eapply taptweak_startup_framed;[exact (proj1 Ready)|exact (proj1 ReadI)|exact FrameI]).
 assert (ReadyI:taptweak_ready mi) by (eapply taptweak_ready_forward;[exact Ready|exact StartupI|exact (proj1 ReadI)]).
 assert (FieldsI:frame_fields_at mi bf 0 bin edge rc).
 { destruct Fields as [Edge Cur];split;rewrite (proj1 FrameI) by (try exact VF;intros;exact I);assumption. }
 assert (InputI:frame_input_cells_at mi bin edge rc (@Translate.encode (Word 9) (pk,h))).
 { eapply buffer_input_cells_preserved;[|exact Input];intros ofs w Load;rewrite (proj1 FrameI) by (try exact VI;intros;exact I);exact Load. }
 assert (OutputI:write_frame_at mi bd base bw outedge cursor 256).
 { eapply write_frame_at_framed;[exact Output|exact FrameI|intros;split;exact I]. }
 destruct (exec_taptweak_body Copy Clear Count pk h le mi bb bi bo bp bt bh bs bc bc1 br br1 bf bin edge rc bd base bw outedge cursor
 eq_refl eq_refl eq_refl eq_refl AllSep OutsideD OutsideW OwnedI ReadyI RC Max FieldsI InputI OutputI) as
 (mb & lef & Body & ObserveB & OwnedB & FrameB & LoadsB & ForwardB & ReadyB).
 assert (PrivateB:forall b hi,In (b,hi) (taptweak_storage bb bi bo bp bt bh bs bc bc1 br br1) ->Mem.range_perm mb b 0 hi Cur Freeable).
 { intros b hi Slot;apply OwnedB;apply in_or_app;left;exact Slot. }
 destruct (taptweak_free mb bb bi bo bp bt bh bs bc bc1 br br1 Distinct PrivateB) as (mf & Frees & FrameF & ReadF).
 assert (StartupF:taptweak_startup mf).
 { eapply taptweak_startup_owned_forward with (slots:=taptweak_storage bb bi bo bp bt bh bs bc bc1 br br1);
 [exact (proj1 ReadyB)|exact (proj1 ReadF)| |].
 - intros b hi Slot;split.
   + eapply taptweak_body_slots_positive with (bf:=bf);apply in_or_app;left;exact Slot.
   + apply PrivateB;exact Slot.
 - change (lframe (fun b _=>~In b (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1)) mb mf);exact FrameF. }
 assert (ReadyF:taptweak_ready mf) by (eapply taptweak_ready_forward;[exact ReadyB|exact StartupF|exact (proj1 ReadF)]).
 assert (FreeF:Mem.range_perm mf bf 0 16 Cur Freeable).
 { eapply curve_keep_free;[clear;lia| |exact FrameF|intros;exact OutsideF].
 apply OwnedB;apply in_or_app;right;left;reflexivity. }
 assert (VBF:Mem.valid_block mb bw) by (exact (proj1 (ForwardB _ (proj1 (proj1 ReadI bw VW))))).
 assert (VDF:Mem.valid_block mb bd) by (exact (proj1 (ForwardB _ (proj1 (proj1 ReadI bd VD))))).
 exists mf;split.
 - eapply eval_funcall_internal with (e:=taptweak_env bb bi bo bp bt bh bs bc bc1 br br1)
 (le1:=le) (le2:=lef) (m1:=mi) (m2:=mb)
 (out:=Out_return (Some (Vint (bit_int (taptweak_result (taptweak_hash_word pk h) pk)),tint))).
   + exact Entry.
   + exact Body.
   + split;[discriminate|destruct (taptweak_result (taptweak_hash_word pk h) pk);reflexivity].
   + exact Frees.
 - split.
   + destruct (taptweak_output (taptweak_hash_word pk h) pk) as [value|];[|exact I].
     destruct ObserveB as (Cells & Prefix & Cur);split.
     * intros i c Nth;destruct c as [bit|];cbn [cell_matches] in *.
       -- eapply taptweak_output_bit_preserved;[|exact (Cells i (Some bit) Nth)].
          intros ofs w Load;rewrite (proj1 FrameF Mint64 bw ofs VBF);[exact Load|intros;apply Fresh;exact VW].
       -- destruct (Cells i None Nth) as (bit & Bit);exists bit;eapply taptweak_output_bit_preserved;[|exact Bit].
          intros ofs w Load;rewrite (proj1 FrameF Mint64 bw ofs VBF);[exact Load|intros;apply Fresh;exact VW].
     * split.
       -- eapply write_prefix_at_preserved with (mr:=mi) (me:=mb).
          ++ intros ofs w Load;rewrite (proj1 FrameI) by (try exact VW;intros;exact I);exact Load.
          ++ intros ofs w Load;rewrite (proj1 FrameF Mint64 bw ofs VBF);[exact Load|intros;apply Fresh;exact VW].
          ++ exact Prefix.
       -- destruct Cur as [Edge Offset];split;rewrite (proj1 FrameF) by (try exact VDF;intros;apply Fresh;exact VD);assumption.
   + split;[exact FreeF|];split.
     * intros chunk b ofs Valid NotSource OD OW.
       assert (Outside:~In b (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1)) by (apply Fresh;exact Valid).
       assert (VB:Mem.valid_block mb b) by (exact (proj1 (ForwardB _ (proj1 (proj1 ReadI b Valid))))).
       rewrite (proj1 FrameF chunk b ofs VB) by (intros;exact Outside).
       rewrite LoadsB.
       -- apply (proj1 FrameI);[exact Valid|intros;exact I].
       -- exact (proj1 (proj1 ReadI b Valid)).
       -- unfold taptweak_body_locals;rewrite in_app_iff;cbn [In];intuition congruence.
       -- exact OD.
       -- exact OW.
     * split.
       -- eapply mem_forward_trans;[exact (proj1 ReadI)|];eapply mem_forward_trans;[exact ForwardB|exact (proj1 ReadF)].
       -- exact ReadyF.
Set Default Timeout 60.
Qed.
Set Default Timeout 10.
