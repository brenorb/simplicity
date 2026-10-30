(** Both zero-X outcomes of the original native-storage public-key loader. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_pubkey_copy C.jet_secp_field_zero_readonly C.jet_secp_affine_storage
 C.jet_secp_affine_storage_frame C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge C.jet_memcpy_model
 C.jet_clight_internal_frame C.jet_clight_internal_preserve C.jet_clight_internal_permissions C.jet_secp_closed_helpers.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Require Import C.jet_secp_pubkey_load_body C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_curve_transport C.jet_elements_taptweak_parse_start
 C.jet_elements_taptweak_save C.jet_transport.
Require Import C.jet_elements_taptweak_load_copy.
From compcert Require Import Globalenvs Coqlib.
Lemma elements_taptweak_has_secp256k1_fe_is_zero:
 In (_secp256k1_fe_is_zero,f_secp256k1_fe_is_zero) elements_taptweak_curve_helpers.
Proof.
 assert (Found:find(fun it=>Pos.eqb(fst it)_secp256k1_fe_is_zero)elements_taptweak_curve_helpers=
 Some(_secp256k1_fe_is_zero,f_secp256k1_fe_is_zero))by(vm_compute;reflexivity).
 apply find_some in Found;exact(proj1 Found).
Qed.
Lemma elements_taptweak_has_secp256k1_ge_from_storage:
 In (_secp256k1_ge_from_storage,f_secp256k1_ge_from_storage) elements_taptweak_curve_helpers.
Proof.
 assert (Found:find(fun it=>Pos.eqb(fst it)_secp256k1_ge_from_storage)elements_taptweak_curve_helpers=
 Some(_secp256k1_ge_from_storage,f_secp256k1_ge_from_storage))by(vm_compute;reflexivity).
 apply find_some in Found;exact(proj1 Found).
Qed.
Lemma elements_taptweak_pubkey_x_address_checked:
 expr_okb secp_ge elements_taptweak_ge pubkey_ge_x_address=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque elements_taptweak_ge.
Lemma eval_elements_taptweak_pubkey_x_address e le m bout:
 le!_ge=Some(Vptr bout Ptrofs.zero) ->eval_expr elements_taptweak_ge e le m pubkey_ge_x_address(Vptr bout Ptrofs.zero).
Proof.
 intro Ge;apply(proj1(eval_expr_transport secp_ge elements_taptweak_ge e le m));
 [apply eval_pubkey_ge_x_address;exact Ge|exact elements_taptweak_pubkey_x_address_checked].
Qed.
Lemma exec_elements_taptweak_arith_call id fd result args vargs v e le m mf:
 In(id,fd)elements_taptweak_curve_helpers ->e!id=None ->
 eval_exprlist elements_taptweak_ge e le m args(type_of_params(fn_params fd))vargs ->
 Clight2.eval_funcall elements_taptweak_ge m(Internal fd)vargs E0 mf v ->
 Clight2.exec_stmt elements_taptweak_ge e le m(curve_call id fd result args)E0(set_opttemp result v le)mf Out_normal.
Proof.
 intros Member Global Args Call.
 destruct(elements_taptweak_curve_entries id fd Member)as(b1 & b2 & S1 & F1 & S2 & F2).
 eapply exec_elements_taptweak_curve_call with(bf:=b2);[exact S2| |exact Global|exact Args|exact Call].
 unfold Genv.find_funct;rewrite pred_dec_true by reflexivity;exact F2.
Qed.
Theorem exec_elements_taptweak_pubkey_load_tail w e le m bout:
 le!_ge=Some (Vptr bout Ptrofs.zero) ->e!_secp256k1_fe_is_zero=None ->
 fe_at m bout 0 (words5 (affine_storage_coord w false)) ->Mem.range_perm m bout 0 40 Cur Freeable ->
 exists lef,Clight2.exec_stmt elements_taptweak_ge e le m pubkey_load_tail E0 lef m
  (Out_return (Some (Vint (bit_int (pubkey_storage_accept w)),tint))).
Proof.
 intros Ge Symbol X Free.
 pose proof (eval_field_zero_readonly (affine_storage_coord w false) m bout X Free) as SourceZero.
 pose proof(elements_taptweak_curve_transport _ _ m _ _ m _ elements_taptweak_has_secp256k1_fe_is_zero SourceZero)as Zero.
 set (iszero:=Int64.eq (field_words_or (affine_storage_coord w false)) Int64.zero) in *.
 assert (Call:Clight2.exec_stmt elements_taptweak_ge e le m pubkey_load_zero_call E0
  (PTree.set _t'1 (Vint (bit_int iszero)) le) m Out_normal).
 { unfold pubkey_load_zero_call;eapply exec_elements_taptweak_arith_call with
   (vargs:=[Vptr bout Ptrofs.zero]) (v:=Vint (bit_int iszero)).
   - exact elements_taptweak_has_secp256k1_fe_is_zero.
   - exact Symbol.
   - eapply eval_Econs;[apply eval_elements_taptweak_pubkey_x_address;exact Ge|reflexivity|constructor].
   - destruct iszero;exact Zero. }
 exists (PTree.set _t'1 (Vint (bit_int iszero)) le).
 unfold pubkey_storage_accept;fold iszero;destruct iszero.
 - cbn [bit_int negb] in *;unfold pubkey_load_tail.
   eapply exec_Sseq_2 with (t1:=E0);[|discriminate].
   eapply exec_Sloop_stop1 with (out':=Out_return (Some (Vint Int.zero,tint)));[|constructor].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _t'1 (Vint Int.one) le);[exact Call|].
   unfold pubkey_load_zero_guard;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
   + eapply eval_Eunop;[eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|reflexivity]|reflexivity].
   + reflexivity.
   + apply exec_Sreturn_some;constructor.
 - cbn [bit_int negb] in *;unfold pubkey_load_tail.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _t'1 (Vint Int.zero) le);[|apply exec_Sreturn_some;constructor].
   eapply exec_Sloop_stop2 with (out1:=Out_normal) (out2:=Out_break) (t1:=E0) (t2:=E0).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
     (le1:=PTree.set _t'1 (Vint Int.zero) le);[exact Call|].
     unfold pubkey_load_zero_guard;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
     * eapply eval_Eunop;[eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|reflexivity]|reflexivity].
     * reflexivity.
     * constructor.
   + constructor.
   + constructor.
   + constructor.
Qed.
Theorem exec_elements_taptweak_pubkey_load_body (Model:memcpy_model) w e le m bin base bout bs bx b_y:
 e!_s=Some (bs,pubkey_storage_type) ->e!_memcpy=None ->
 e!_secp256k1_ge_from_storage=None ->e!_secp256k1_fe_is_zero=None ->
 le!_pubkey=Some (Vptr bin (Ptrofs.repr base)) ->le!_ge=Some (Vptr bout Ptrofs.zero) ->
 NoDup [bout;bs;bx;b_y] ->bin<>bs ->
 (forall b hi,In (b,hi) [(bout,88);(bs,64);(bx,40);(b_y,40)] ->Mem.range_perm m b 0 hi Cur Freeable) ->
 affine_storage_readable m bin base w ->
 exists mf lef,
 Clight2.exec_stmt elements_taptweak_ge e le m (fn_body f_secp256k1_pubkey_load) E0 lef mf
  (Out_return (Some (Vint (bit_int (pubkey_storage_accept w)),tint))) /\
 (forall k:bool,fe_at mf bout (if k then 40 else 0) (words5 (affine_storage_coord w k))) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\
 (forall b hi,In (b,hi) [(bout,88);(bs,64);(bx,40);(b_y,40)] ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>b<>bout /\b<>bs) m mf /\readonly_preserved m mf.
Proof.
 intros S CopySym DecodeSym ZeroSym Key Ge Separate SourceSep Owned Input.
 destruct (exec_elements_taptweak_pubkey_load_copy Model w e le m bin base bs S CopySym Key (not_eq_sym SourceSep)
  (Owned bs 64 ltac:(clear;cbn [In];tauto)) Input)
 as (mc & Copy & Storage & FreeS & FrameC & ReadC).
 assert (OutputSep:bout<>bs).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 assert (OwnedC:forall b hi,In (b,hi) [(bout,88);(bs,64);(bx,40);(b_y,40)] ->Mem.range_perm mc b 0 hi Cur Freeable).
 { intros b hi Slot;destruct (Pos.eq_dec b bs) as [Same|Other].
   - subst b;assert (Size:hi=64) by (clear -Slot Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence);subst hi;exact FreeS.
   - eapply curve_keep_free;[ |apply Owned;exact Slot|exact FrameC|intros;exact Other].
     clear -Slot;cbn [In] in Slot;repeat destruct Slot as [Slot|Slot];try contradiction;inversion Slot;lia. }
 destruct (eval_ge_from_storage_readonly w mc bout bs 0 OutputSep
  (OwnedC bout 88 ltac:(clear;cbn [In];tauto)) Storage)
 as (md & SourceDecode & FreeOut & Fields & Flag & Source & FrameD).
 assert (KeepD:keeps_permissions mc md).
 { exact (proj2 (internal_exec_keeps_permissions _ _ secp_closed_helpers_ok)
   _ _ _ _ _ _ SourceDecode pubkey_decode_allowed). }
 assert (ReadD:readonly_preserved mc md).
 { exact (proj2 (internal_exec_preserved _ _ secp_closed_helpers_ok)
   _ _ _ _ _ _ SourceDecode pubkey_decode_allowed). }
 pose proof(elements_taptweak_curve_transport _ _ mc _ _ md _
 elements_taptweak_has_secp256k1_ge_from_storage SourceDecode)as Decode.
 destruct (exec_elements_taptweak_pubkey_load_tail w e le md bout Ge ZeroSym (Fields false)
  ltac:(intros pos Pos;apply FreeOut;lia)) as (lef & Tail).
 assert (DecodeCall:Clight2.exec_stmt elements_taptweak_ge e le mc pubkey_load_decode E0 le md Out_normal).
 { unfold pubkey_load_decode;eapply exec_elements_taptweak_arith_call with
    (vargs:=[Vptr bout Ptrofs.zero;Vptr bs Ptrofs.zero]) (v:=Vundef).
   - exact elements_taptweak_has_secp256k1_ge_from_storage.
   - exact DecodeSym.
   - eapply eval_Econs;[apply eval_Etempvar;exact Ge|reflexivity|].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact S|reflexivity|constructor].
   - exact Decode. }
 exists md,lef;split.
 - rewrite pubkey_load_body_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=le);[|exact Tail].
   eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
   + apply(proj1(eval_expr_transport secp_ge elements_taptweak_ge e le m)).
     * unfold pubkey_load_size_test;eapply eval_Ebinop;[apply eval_Esizeof|constructor|reflexivity].
     * exact elements_taptweak_storage_test_checked.
   + reflexivity.
   + unfold pubkey_load_branch;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=le);[exact Copy|exact DecodeCall].
 - split;[exact Fields|];split;[exact Flag|];split.
   + intros b hi Slot pos Pos;apply KeepD;exact (OwnedC b hi Slot pos Pos).
   + split.
     * eapply lframe_trans.
       { eapply lframe_implies;[exact FrameC|];intros b pos [_ Outside] _;exact Outside. }
       { apply curve_frame_two with (regs:=affine_storage_regs);[reflexivity|exact FrameD]. }
     * eapply preserved_trans;[exact ReadC|exact ReadD].
Qed.
