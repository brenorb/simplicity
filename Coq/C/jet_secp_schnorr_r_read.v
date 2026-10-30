(** Original Schnorr r field reader/guard and retention of the later s bytes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Cop.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_word_repr C.jet_read8s_layout C.jet_sx_state C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_b32_exec
 C.jet_secp_set_b32_owned C.jet_secp_set_b32_owned_frame C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_input_input C.jet_secp_word_bytes_codec C.jet_secp_schnorr_challenge_hash
 C.jet_secp_schnorr_challenge_absorb C.jet_secp_xonly_parse_control C.jet_secp_xonly_parse_field
 C.jet_secp_root_chain_owned C.jet_secp_statement_prefix C.jet_secp_schnorr_scalar_read
 C.jet_secp_schnorr_signature_guards C.jet_secp_schnorr_verify_literal
 C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition schnorr_r_read_call:=curve_call _secp256k1_fe_set_b32 f_secp256k1_fe_set_b32 (Some _t'2)
 [Eaddrof (Evar _rx (Tstruct __5467 noattr)) (tptr (Tstruct __5467 noattr));
 Ebinop Oadd (Etempvar _sig64 (tptr tuchar)) (Econst_int Int.zero tint) (tptr tuchar)].
Definition schnorr_r_read_guard:=Ssequence schnorr_r_read_call (xonly_parse_guard _t'2).
Lemma schnorr_r_read_source:
 root_drop_statements 3 (fn_body f_secp256k1_schnorrsig_verify)=Ssequence schnorr_r_read_guard
 (root_drop_statements 4 (fn_body f_secp256k1_schnorrsig_verify)).
Proof. reflexivity. Qed.
Lemma schnorr_r_raw_bounds (r:Ty.tySem (Word 8)):forall i,(i<5)%nat ->
 Int64.unsigned (limb_rho (@toZ (WordToZ 8) r) i)<
 if Nat.eqb i 4 then 562949953421312 else 4503599627370496.
Proof.
 intros i Index;pose proof (word_toZ_range 8 r) as Range.
 pose proof (proj1 (fe_limbs_of_ok _ Range)) as (B0 & B1 & B2 & B3 & B4).
 destruct i as [|[|[|[|[|i]]]]];try lia;rewrite limb_rho_unsigned by exact Range;
 cbn [Nat.eqb fe_limbs_of nth];lia.
Qed.
Lemma schnorr_word_bytes_from_be_loads (r:Ty.tySem (Word 8)) m b:
 (forall i,(i<32)%nat ->Mem.load Mint8unsigned m b (Z.of_nat i)=
  Some (Vint (Int.repr (nth i (xonly_input_bytes r) 0)))) ->
 schnorr_bytes_at m b Ptrofs.zero (schnorr_word_bytes r).
Proof.
 intros Loads i Index;rewrite schnorr_word_bytes_length in Index.
 unfold schnorr_word_bytes;rewrite <-word256_serializer_bytes.
 change (Mem.load Mint8unsigned m b (Z.of_nat i)=
  Some (Vint (nth i (map Int.repr (xonly_input_bytes r)) (Int.repr 0)))).
 rewrite map_nth;apply Loads;exact Index.
Qed.
Definition schnorr_r_read_outcome (r:Ty.tySem (Word 8)):=
 if Z.ltb (@toZ (WordToZ 8) r) feP then Out_normal else Out_return (Some (Vint Int.zero,tint)).
Definition schnorr_r_read_temps le r:=PTree.set _t'2 (Vint (xonly_strict_flag r)) le.
Theorem exec_schnorr_r_read (r:Ty.tySem (Word 8)) sbytes e le m bx bsig:
 e!_rx=Some (bx,Tstruct __5467 noattr) ->e!_secp256k1_fe_set_b32=None ->
 le!_sig64=Some (Vptr bsig Ptrofs.zero) ->bx<>bsig ->
 Mem.range_perm m bx 0 40 Cur Freeable ->Mem.range_perm m bsig 0 64 Cur Freeable ->
 uint8_array_at m bsig 0 (map Int.repr (xonly_input_bytes r)) ->
 (length sbytes<=32)%nat ->uint8_array_at m bsig 32 sbytes ->exists mf,
 Clight2.exec_stmt secp_ge e le m schnorr_r_read_guard E0 (schnorr_r_read_temps le r) mf (schnorr_r_read_outcome r) /\
 fe_at mf bx 0 (map Int64.repr (fe_limbs_of (@toZ (WordToZ 8) r))) /\
 schnorr_bytes_at mf bsig Ptrofs.zero (schnorr_word_bytes r) /\uint8_array_at mf bsig 32 sbytes /\
 keeps_permissions m mf /\
 lframe (fun b pos=>~foot [(bx,0);(bsig,0)] (map rshape owned_b32_regs) b pos) m mf /\readonly_preserved m mf.
Proof.
 intros X Symbol Sig Separate Free SigFree Input Length SBytes.
 assert (Loads:forall i,(i<32)%nat ->Mem.load Mint8unsigned m bsig (Z.of_nat i)=
  Some (Vint (Int.repr (nth i (xonly_input_bytes r) 0)))).
 { intros i Index;apply Input;rewrite nth_error_map,(nth_error_nth' _ 0);
   [reflexivity|rewrite xonly_input_length;exact Index]. }
 destruct (eval_set_b32_owned_frame (xonly_input_bytes r) m bx bsig
  (xonly_input_length r) (xonly_input_bounds r) Separate Free
  ltac:(intros pos Range;apply SigFree;lia) Loads)
 as (mf & Call & Field & FreeX & FreeSig32 & RBytes & Frame & Read).
 rewrite xonly_input_value in Call,Field.
 assert (Flag:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_set_b32)
  [Vptr bx Ptrofs.zero;Vptr bsig Ptrofs.zero] E0 mf (Vint (xonly_strict_flag r))).
 { unfold xonly_strict_flag;destruct (Z.ltb (@toZ (WordToZ 8) r) feP);exact Call. }
 assert (Allowed:allowed_call secp_closed_helpers (Internal f_secp256k1_fe_set_b32)).
 { exists _secp256k1_fe_set_b32,f_secp256k1_fe_set_b32;split;vm_compute;reflexivity. }
 pose proof (proj2 (internal_exec_keeps_permissions _ _ secp_closed_helpers_ok)
  _ _ _ _ _ _ Flag Allowed) as Keep.
 assert (RBytesF:schnorr_bytes_at mf bsig Ptrofs.zero (schnorr_word_bytes r)).
 { apply schnorr_word_bytes_from_be_loads;exact RBytes. }
 assert (SBytesF:uint8_array_at mf bsig 32 sbytes).
 { intros i x Nth.
   assert (Index:(i<length sbytes)%nat) by (apply nth_error_Some;congruence).
   rewrite (proj1 Frame Mint8unsigned bsig (32+Z.of_nat i));[apply SBytes;exact Nth| |].
   - eapply Mem.perm_valid_block;apply (SigFree 0);lia.
   - intros pos Range Foot;destruct (owned_b32_foot_bounds bx bsig bsig pos Foot)
     as [[Same _]|[_ Bounds]];[congruence|change (size_chunk Mint8unsigned) with 1 in Range;lia]. }
 assert (ReadStmt:Clight2.exec_stmt secp_ge e le m schnorr_r_read_call E0 (schnorr_r_read_temps le r) mf Out_normal).
 { unfold schnorr_r_read_call,schnorr_r_read_temps;eapply exec_curve_call with
   (vargs:=[Vptr bx Ptrofs.zero;Vptr bsig Ptrofs.zero]) (v:=Vint (xonly_strict_flag r)).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - exact Symbol.
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact X|reflexivity|].
     eapply eval_Econs;[eapply eval_Ebinop;[apply eval_Etempvar;exact Sig|constructor|reflexivity]|reflexivity|constructor].
   - exact Flag. }
 exists mf;split.
 - unfold schnorr_r_read_guard;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
   (le1:=schnorr_r_read_temps le r);[exact ReadStmt|].
   unfold schnorr_r_read_outcome,schnorr_r_read_temps,xonly_strict_flag.
   destruct (Z.ltb (@toZ (WordToZ 8) r) feP).
   + apply exec_xonly_guard_one;apply PTree.gss.
   + apply exec_xonly_guard_zero;apply PTree.gss.
 - split;[exact Field|];split;[exact RBytesF|];split;[exact SBytesF|];split;[exact Keep|];split;assumption.
Qed.
Theorem exec_schnorr_r_reject (pk msg r s:Ty.tySem (Word 8)) e le m bx bsig:
 feP<=@toZ (WordToZ 8) r ->
 e!_rx=Some (bx,Tstruct __5467 noattr) ->e!_secp256k1_fe_set_b32=None ->
 le!_sig64=Some (Vptr bsig Ptrofs.zero) ->bx<>bsig ->
 Mem.range_perm m bx 0 40 Cur Freeable ->Mem.range_perm m bsig 0 64 Cur Freeable ->
 uint8_array_at m bsig 0 (map Int.repr (xonly_input_bytes r)) ->exists mf lef,
 Clight2.exec_stmt secp_ge e le m
 (root_drop_statements 3 (fn_body f_secp256k1_schnorrsig_verify)) E0 lef mf
 (Out_return (Some (Vint Int.zero,tint))) /\
 Simplicity.Bit.toBool (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,s)))=false /\
 keeps_permissions m mf /\
 lframe (fun b pos=>~foot [(bx,0);(bsig,0)] (map rshape owned_b32_regs) b pos) m mf /\readonly_preserved m mf.
Proof.
 intros Bound X Symbol Sig Separate Free SigFree Input.
 destruct (exec_schnorr_r_read r [] e le m bx bsig X Symbol Sig Separate Free SigFree Input
  ltac:(cbn;lia) ltac:(intros i x Bad;destruct i;discriminate Bad))
 as (mf & Guard & Field & RBytes & Empty & Keep & Frame & Read).
 assert (Rejected:Z.ltb (@toZ (WordToZ 8) r) feP=false) by (apply Z.ltb_ge;exact Bound).
 unfold schnorr_r_read_outcome in Guard;rewrite Rejected in Guard.
 exists mf,(schnorr_r_read_temps le r);split.
 - rewrite schnorr_r_read_source;eapply exec_Sseq_2;[exact Guard|discriminate].
 - split;[apply schnorr_spec_reject_r;exact Bound|];split;[exact Keep|];split;assumption.
Qed.
