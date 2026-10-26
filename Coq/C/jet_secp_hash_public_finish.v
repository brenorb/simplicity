(** The original public hash_to_curve branch, load/write calls and return.
    Digest rejection writes nothing. Success writes the actual saved point,
    including the cleared-coordinate infinity case; no such case is excluded. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Translate.
Require Import C.jet_sx_mem C.jet_sx_exec C.jet_frame_inv C.jet_output_layout C.jet_secp_frame
 C.jet_secp_linkage C.jets_secp C.jet_secp_field_cmov C.jet_secp_field_pair_multiply
 C.jet_secp_rescale_literal C.jet_secp_generator_codec C.jet_secp_generator_roundtrip
 C.jet_secp_generator_load_write C.jet_secp_generator_field_roundtrip C.jet_secp_curve_frame
 C.jet_clight_internal_preserve C.jet_secp_hash_public_entry C.jet_secp_hash_public_read
 C.jet_secp_hash_public_generate.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Simplicity.Translate.encode generator_saved_bytes rescale_field_output.

Definition hash_public_load := Scall None
 (Evar _secp256k1_generator_load (type_of_function f_secp256k1_generator_load))
 [Eaddrof (Evar _ge (Tstruct __6121 noattr)) (tptr (Tstruct __6121 noattr));
  Eaddrof (Evar _gen (Tstruct __6563 noattr)) (tptr (Tstruct __6563 noattr))].
Definition hash_public_write := Scall None (Evar _write_ge (type_of_function f_write_ge))
 [Etempvar _dst (tptr (Tstruct _frameItem noattr));
  Eaddrof (Evar _ge (Tstruct __6121 noattr)) (tptr (Tstruct __6121 noattr))].
Lemma hash_public_finish_source : hash_public_finish=
 Ssequence hash_public_load (Ssequence hash_public_write (Sreturn (Some (Econst_int Int.one tint)))).
Proof. reflexivity. Qed.
Lemma hash_public_decision_source : hash_public_decision=
 Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
   (Sreturn (Some (Econst_int Int.zero tint))) Sskip.
Proof. reflexivity. Qed.
Lemma hash_public_output_links :
 (Genv.find_symbol secp_ge _secp256k1_generator_load=
   Some (secp_symbol_block _secp256k1_generator_load) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block _secp256k1_generator_load) Ptrofs.zero)=
   Some (Internal f_secp256k1_generator_load)) /\
 (Genv.find_symbol secp_ge _write_ge=Some (secp_symbol_block _write_ge) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block _write_ge) Ptrofs.zero)=Some (Internal f_write_ge)).
Proof. vm_compute;repeat split;reflexivity. Qed.

Lemma exec_hash_public_finish le m mr mf bl bk bg bp bd base :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_generator_load)
   [Vptr bp Ptrofs.zero;Vptr bg Ptrofs.zero] E0 mr Vundef ->
 Clight2.eval_funcall secp_ge mr (Internal f_write_ge)
   [Vptr bd (Ptrofs.repr base);Vptr bp Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (hash_public_env bl bk bg bp) le m hash_public_finish E0 le mf
   (Out_return (Some (Vint Int.one,tint))).
Proof.
 intros Dst Load Write;destruct hash_public_output_links as [[LS LF] [WS WF]].
 rewrite hash_public_finish_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le).
 - unfold hash_public_load;eapply exec_Scall with
     (vf:=Vptr (secp_symbol_block _secp256k1_generator_load) Ptrofs.zero)
     (vargs:=[Vptr bp Ptrofs.zero;Vptr bg Ptrofs.zero]) (f:=Internal f_secp256k1_generator_load) (vres:=Vundef).
   + reflexivity.
   + eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact LS]|apply deref_loc_reference;reflexivity].
   + eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
   + exact LF.
   + reflexivity.
   + exact Load.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
   + unfold hash_public_write;eapply exec_Scall with
       (vf:=Vptr (secp_symbol_block _write_ge) Ptrofs.zero)
       (vargs:=[Vptr bd (Ptrofs.repr base);Vptr bp Ptrofs.zero]) (f:=Internal f_write_ge) (vres:=Vundef).
     * reflexivity.
     * eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact WS]|apply deref_loc_reference;reflexivity].
     * eapply eval_Econs;[apply eval_Etempvar;exact Dst|reflexivity|].
       eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
     * exact WF.
     * reflexivity.
     * exact Write.
   + apply exec_Sreturn_some;constructor.
Qed.

Lemma exec_hash_public_decision e le m accepted :
 le!_t'1=Some (Vint (cmov_int accepted)) ->
 Clight2.exec_stmt secp_ge e le m hash_public_decision E0 le m
   (if accepted then Out_normal else Out_return (Some (Vint Int.zero,tint))).
Proof.
 intro Flag;rewrite hash_public_decision_source;destruct accepted.
 - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
   eapply eval_Eunop;[apply eval_Etempvar;exact Flag|reflexivity].
 - eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|].
   + eapply eval_Eunop;[apply eval_Etempvar;exact Flag|reflexivity].
   + apply exec_Sreturn_some;constructor.
Qed.

Lemma hash_public_storage_member bl bk bg bp b hi :
 In (b,hi) (hash_public_storage bl bk bg bp) ->In b (hash_public_locals bl bk bg bp).
Proof.
 unfold hash_public_storage,hash_public_locals;cbn [In];intuition congruence.
Qed.

Theorem exec_hash_public_rest le m0 bd base bw edge cursor N bi (rc:Z) m bl bk bg bp accepted ox oy :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->le!_t'1=Some (Vint (cmov_int accepted)) ->
 write_frame_at m0 bd base bw edge cursor N ->512<=N ->
 finv m0 bd base bw edge cursor N bi m false [] ->
 NoDup (hash_public_locals bl bk bg bp) ->
 (forall b,Mem.valid_block m0 b ->~In b (hash_public_locals bl bk bg bp)) ->
 (forall b hi,In (b,hi) (hash_public_storage bl bk bg bp) ->Mem.range_perm m b 0 hi Cur Freeable) ->
 (forall (second:bool) i,(i<32)%nat ->Mem.load Mint8unsigned m bg ((if second then 32 else 0)+Z.of_nat i)=
   Some (Vint (nth i (map Int.repr (generator_saved_bytes (field_pair_valuation ox oy)
     (if second then 5 else 0))) Int.zero))) ->exists mf,
 Clight2.exec_stmt secp_ge (hash_public_env bl bk bg bp) le m
   (Ssequence hash_public_decision hash_public_finish) E0 le mf
   (Out_return (Some (Vint (cmov_int accepted),tint))) /\
 finv m0 bd base bw edge cursor N bi mf accepted
   (if accepted then @Simplicity.Translate.encode (Ty.Prod (Word 8) (Word 8))
     (rescale_field_output ox,rescale_field_output oy) else []) /\
 (forall b hi,In (b,hi) (hash_public_storage bl bk bg bp) ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>b<>bp /\ b<>bg /\ ~extA m0 bd bw bi b) m mf /\readonly_preserved m mf.
Proof.
 intros Dst Flag Output Cap Inv Distinct Old Free Bytes.
 destruct accepted.
 - assert (PG:bp<>bg).
   { clear -Distinct;unfold hash_public_locals in Distinct;repeat rewrite NoDup_cons_iff in Distinct;
     cbn [In] in Distinct;intuition congruence. }
   assert (Outside:forall b,In b (hash_public_locals bl bk bg bp) ->~extA m0 bd bw bi b).
   { intros b Member [_ Valid];exact (Old b Valid Member). }
   assert (Sep:xsep (extA m0 bd bw bi) [(bp,0);(bg,0)]).
   { intros [|[|i]] Index;[apply Outside|apply Outside|clear -Index;cbn in Index;lia];
       clear;unfold hash_public_locals;cbn;tauto. }
   destruct (eval_generator_load_write m0 bd base bw edge cursor N bi rc
     (generator_saved_bytes (field_pair_valuation ox oy) 0)
     (generator_saved_bytes (field_pair_valuation ox oy) 5) m bp bg Output Cap Inv
     (generator_saved_bytes_length _ _) (generator_saved_bytes_length _ _)
     (generator_saved_bytes_bound _ _) (generator_saved_bytes_bound _ _) PG
     ltac:(apply Free;clear;cbn [hash_public_storage In];tauto)
     ltac:(apply Free;clear;cbn [hash_public_storage In];tauto) Sep
     (generator_saved_concat_loads _ _ _ Bytes)) as (mr & mf & Load & Write & Final & FPF & FGF & Frame & RO).
   rewrite generator_field_pair_output in Final.
   assert (FreeF:forall b hi,In (b,hi) (hash_public_storage bl bk bg bp) ->Mem.range_perm mf b 0 hi Cur Freeable).
   { intros b hi Slot;destruct (peq b bp) as [Same|NP];[|destruct (peq b bg) as [Same|NG]].
     - subst b;assert (Hi:hi=88).
       { clear -Slot Distinct;unfold hash_public_locals in Distinct;
         repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct;
         cbn [hash_public_storage In] in Slot;intuition congruence. }
       subst hi;exact FPF.
     - subst b;assert (Hi:hi=64).
       { clear -Slot Distinct;unfold hash_public_locals in Distinct;
         repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct;
         cbn [hash_public_storage In] in Slot;intuition congruence. }
       subst hi;exact FGF.
     - intros pos Range;apply (proj1(proj2 Frame)).
       + eapply Mem.perm_valid_block;apply (Free b hi Slot pos Range).
       + split;[exact NP|];split;[exact NG|apply Outside;eapply hash_public_storage_member;exact Slot].
       + exact (Free b hi Slot pos Range). }
   exists mf;split.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le).
     * apply (exec_hash_public_decision _ _ _ true);exact Flag.
     * eapply exec_hash_public_finish;eassumption.
   + split;[exact Final|];split;[exact FreeF|];split;assumption.
 - exists m;split.
   + eapply exec_Sseq_2;[apply (exec_hash_public_decision _ _ _ false);exact Flag|discriminate].
   + split;[exact Inv|];split;[exact Free|];split;[apply lframe_refl|apply preserved_refl].
Qed.
