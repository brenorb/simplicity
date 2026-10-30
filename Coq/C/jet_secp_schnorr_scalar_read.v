(** Original Schnorr scalar parser, overflow guard and retained r bytes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_read8s_layout C.jet_sx_expr C.jet_sx_state C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_secp_canonical_scalar C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_set_canonical C.jet_secp_scalar_set_flag C.jet_secp_scalar_set_flag_frame
 C.jet_secp_schnorr_challenge_absorb C.jet_secp_xonly_parse_field
 C.jet_secp_root_chain_owned C.jet_secp_statement_prefix C.jet_secp_schnorr_keyload_return
 C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition schnorr_scalar_read_call:=curve_call _secp256k1_scalar_set_b32 f_secp256k1_scalar_set_b32 None
 [Eaddrof (Evar _s (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
  Ebinop Oadd (Etempvar _sig64 (tptr tuchar)) (Econst_int (Int.repr 32) tint) (tptr tuchar);
  Eaddrof (Evar _overflow tint) (tptr tint)].
Definition schnorr_scalar_overflow_guard:=Ssequence (Sset _t'8 (Evar _overflow tint))
 (Sifthenelse (Etempvar _t'8 tint) (Sreturn (Some (Econst_int Int.zero tint))) Sskip).
Definition schnorr_scalar_read_statements:=[schnorr_scalar_read_call;schnorr_scalar_overflow_guard].
Lemma schnorr_scalar_read_source:
 root_drop_statements 4 (fn_body f_secp256k1_schnorrsig_verify)=
 statement_sequence schnorr_scalar_read_statements schnorr_keyload_return.
Proof. reflexivity. Qed.
Definition schnorr_scalar_outcome (overflow:bool):=
 if overflow then Out_return (Some (Vint Int.zero,tint)) else Out_normal.
Definition schnorr_scalar_read_temps le overflow:=PTree.set _t'8 (Vint (b2i overflow)) le.
Lemma exec_schnorr_overflow_guard e le m bf overflow:
 e!_overflow=Some (bf,tint) ->Mem.load Mint32 m bf 0=Some (Vint (b2i overflow)) ->
 Clight2.exec_stmt secp_ge e le m schnorr_scalar_overflow_guard E0
 (schnorr_scalar_read_temps le overflow) m (schnorr_scalar_outcome overflow).
Proof.
 intros Local Load;unfold schnorr_scalar_overflow_guard,schnorr_scalar_read_temps.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'8 (Vint (b2i overflow)) le).
 - apply exec_Sset;eapply eval_Elvalue.
   + apply eval_Evar_local;exact Local.
   + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
     change (Mem.load Mint32 m bf 0=Some (Vint (b2i overflow)));exact Load.
 - destruct overflow;cbn [b2i schnorr_scalar_outcome].
   + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
     * apply eval_Etempvar;apply PTree.gss.
     * reflexivity.
     * apply exec_Sreturn_some;constructor.
   + eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
     * apply eval_Etempvar;apply PTree.gss.
     * reflexivity.
     * constructor.
Qed.
Lemma exec_schnorr_scalar_read_call e le m mf bs bsig bf:
 e!_s=Some (bs,Tstruct __5826 noattr) ->e!_overflow=Some (bf,tint) ->
 e!_secp256k1_scalar_set_b32=None ->le!_sig64=Some (Vptr bsig Ptrofs.zero) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_set_b32)
 [Vptr bs Ptrofs.zero;Vptr bsig (Ptrofs.repr 32);Vptr bf Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m schnorr_scalar_read_call E0 le mf Out_normal.
Proof.
 intros S Flag Symbol Sig Call;unfold schnorr_scalar_read_call;eapply exec_curve_call with
 (vargs:=[Vptr bs Ptrofs.zero;Vptr bsig (Ptrofs.repr 32);Vptr bf Ptrofs.zero]) (v:=Vundef).
 - unfold secp_pure;repeat first [left;reflexivity|right].
 - exact Symbol.
 - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact S|reflexivity|].
   eapply eval_Econs.
   + eapply eval_Ebinop;[apply eval_Etempvar;exact Sig|constructor|reflexivity].
   + reflexivity.
   + eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Flag|reflexivity|constructor].
 - exact Call.
Qed.
Theorem exec_schnorr_scalar_read (s:Ty.tySem (Word 8)) rbytes e le m bs bsig bf:
 e!_s=Some (bs,Tstruct __5826 noattr) ->e!_overflow=Some (bf,tint) ->
 e!_secp256k1_scalar_set_b32=None ->le!_sig64=Some (Vptr bsig Ptrofs.zero) ->
 bs<>bsig ->bf<>bs ->bf<>bsig ->
 Mem.range_perm m bs 0 32 Cur Freeable ->Mem.range_perm m bsig 0 64 Cur Freeable ->
 Mem.range_perm m bf 0 4 Cur Freeable ->
 uint8_array_at m bsig 32 (map Int.repr (xonly_input_bytes s)) ->
 (length rbytes<=32)%nat ->schnorr_bytes_at m bsig Ptrofs.zero rbytes ->
 let overflow:=Z.leb canonical_group_order (@toZ (WordToZ 8) s) in exists mf,
 Clight2.exec_stmt secp_ge e le m (statement_sequence schnorr_scalar_read_statements Sskip) E0
 (schnorr_scalar_read_temps le overflow) mf (schnorr_scalar_outcome overflow) /\
 scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem s)))) /\
 Mem.load Mint32 mf bf 0=Some (Vint (b2i overflow)) /\
 schnorr_bytes_at mf bsig Ptrofs.zero rbytes /\keeps_permissions m mf /\
 lframe (fun block pos=>~foot [(bs,0);(bsig,32);(bf,0)]
  (map rshape scalar_flag_regs) block pos /\block<>bf) m mf /\readonly_preserved m mf.
Proof.
 intros S Flag Symbol Sig Separate FB FS Free SigFree FlagFree Input Length RBytes overflow.
 destruct (eval_scalar_set_b32_canonical_flag s bs bsig 32 bf m Separate FB FS
  ltac:(lia) ltac:(clear;change (64<=18446744073709551615);lia) Free
  ltac:(intros pos Range;eapply Mem.perm_implies;[apply SigFree;lia|constructor]) FlagFree Input)
 as (mf & Call & Scalar & Overflow & Keep & Frame & Read).
 fold overflow in Overflow.
 pose proof (exec_schnorr_overflow_guard e le mf bf overflow Flag Overflow) as Guard.
 assert (RBytesF:schnorr_bytes_at mf bsig Ptrofs.zero rbytes).
 { intros i Index;rewrite (proj1 Frame Mint8unsigned bsig (Ptrofs.unsigned Ptrofs.zero+Z.of_nat i));
   [apply RBytes;exact Index| |].
   - eapply Mem.perm_valid_block;apply (SigFree 0);lia.
   - intros pos Range;apply scalar_flag_before_source;[exact Separate|exact FS|].
     change (size_chunk Mint8unsigned) with 1 in Range;rewrite Ptrofs.unsigned_zero in Range;lia. }
 exists mf;split.
 - cbn [statement_sequence schnorr_scalar_read_statements].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
   + exact (exec_schnorr_scalar_read_call e le m mf bs bsig bf S Flag Symbol Sig Call).
   + destruct overflow.
     * eapply exec_Sseq_2 with (t1:=E0);[exact Guard|discriminate].
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
        (le1:=schnorr_scalar_read_temps le false);[exact Guard|constructor].
 - split;[exact Scalar|];split;[exact Overflow|];split;[exact RBytesF|];split;[exact Keep|];split;assumption.
Qed.
