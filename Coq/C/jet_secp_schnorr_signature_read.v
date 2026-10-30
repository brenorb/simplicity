(** Successful original r/s parsing, ready for the canonical key-load suffix. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_toZ C.jet_word_repr C.jet_read8s_layout C.jet_sx_state C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_b32_exec
 C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_input_input
 C.jet_secp_canonical_scalar C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_set_flag C.jet_secp_set_b32_owned_frame C.jet_secp_schnorr_r_read C.jet_secp_schnorr_scalar_read
 C.jet_secp_schnorr_challenge_hash C.jet_secp_schnorr_challenge_absorb C.jet_secp_root_chain_owned
 C.jet_secp_statement_prefix C.jet_secp_xonly_parse_field C.jet_secp_schnorr_keyload_return
 C.jet_secp_field_read_preservation C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition schnorr_signature_read_statements:=schnorr_r_read_guard::schnorr_scalar_read_statements.
Lemma schnorr_signature_read_source:
 root_drop_statements 3 (fn_body f_secp256k1_schnorrsig_verify)=
 statement_sequence schnorr_signature_read_statements schnorr_keyload_return.
Proof. reflexivity. Qed.
Theorem exec_schnorr_signature_read (r s:Ty.tySem (Word 8)) e le m bx bs bf bsig:
 @toZ (WordToZ 8) r<feP ->@toZ (WordToZ 8) s<canonical_group_order ->
 e!_rx=Some (bx,Tstruct __5467 noattr) ->e!_s=Some (bs,Tstruct __5826 noattr) ->e!_overflow=Some (bf,tint) ->
 e!_secp256k1_fe_set_b32=None ->e!_secp256k1_scalar_set_b32=None ->
 le!_sig64=Some (Vptr bsig Ptrofs.zero) ->NoDup [bx;bs;bf;bsig] ->
 Mem.range_perm m bx 0 40 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->
 Mem.range_perm m bf 0 4 Cur Freeable ->Mem.range_perm m bsig 0 64 Cur Freeable ->
 uint8_array_at m bsig 0 (map Int.repr (xonly_input_bytes r)) ->
 uint8_array_at m bsig 32 (map Int.repr (xonly_input_bytes s)) ->exists mf,
 Clight2.exec_stmt secp_ge e le m (statement_sequence schnorr_signature_read_statements Sskip) E0
 (schnorr_scalar_read_temps (schnorr_r_read_temps le r) false) mf Out_normal /\
 fe_at mf bx 0 (words5 (limb_rho (@toZ (WordToZ 8) r))) /\
 scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem s)))) /\
 schnorr_bytes_at mf bsig Ptrofs.zero (schnorr_word_bytes r) /\
 (forall i,(i<5)%nat ->Int64.unsigned (limb_rho (@toZ (WordToZ 8) r) i)<
  if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
 radix_value (limb_rho (@toZ (WordToZ 8) r)) mod feP=@toZ (WordToZ 8) r /\
 keeps_permissions m mf /\
 lframe (fun b _=>b<>bx /\b<>bs /\b<>bf /\b<>bsig) m mf /\readonly_preserved m mf.
Proof.
 intros RBound SBound X S Flag ReadSym ScalarSym Sig Separate FreeX FreeS FreeFlag SigFree RInput SInput.
 assert (Pairs:bx<>bs /\bx<>bf /\bx<>bsig /\bs<>bf /\bs<>bsig /\bf<>bsig).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 destruct Pairs as (XS & XF & XI & SF & SI & FI).
 destruct (exec_schnorr_r_read r (map Int.repr (xonly_input_bytes s)) e le m bx bsig X ReadSym Sig XI
  FreeX SigFree RInput ltac:(rewrite map_length,xonly_input_length;lia) SInput)
 as (mr & RRead & RX & RBytes & SBytes & KeepR & FrameR & ReadR).
 assert (SigR:(schnorr_r_read_temps le r)!_sig64=Some (Vptr bsig Ptrofs.zero)).
 { unfold schnorr_r_read_temps;rewrite PTree.gso by discriminate;exact Sig. }
 destruct (exec_schnorr_scalar_read s (schnorr_word_bytes r) e (schnorr_r_read_temps le r) mr bs bsig bf
  S Flag ScalarSym SigR SI (not_eq_sym SF) FI
  ltac:(intros pos Range;apply KeepR,FreeS;exact Range)
  ltac:(intros pos Range;apply KeepR,SigFree;exact Range)
  ltac:(intros pos Range;apply KeepR,FreeFlag;exact Range)
  SBytes ltac:(rewrite schnorr_word_bytes_length;lia) RBytes)
 as (mf & SRead & Scalar & Overflow & RBytesF & KeepS & FrameS & ReadS).
 assert (NoOverflow:Z.leb canonical_group_order (@toZ (WordToZ 8) s)=false) by (apply Z.leb_gt;exact SBound).
 rewrite NoOverflow in SRead;cbn [schnorr_scalar_outcome] in SRead.
 assert (InRange:Z.ltb (@toZ (WordToZ 8) r) feP=true) by (apply Z.ltb_lt;exact RBound).
 unfold schnorr_r_read_outcome in RRead;rewrite InRange in RRead.
 assert (RXF:fe_at mf bx 0 (words5 (limb_rho (@toZ (WordToZ 8) r)))).
 { eapply field_at_lframe;[exact RX|exact FrameS|].
   intros pos;split;[apply scalar_flag_foot_outside;repeat split;congruence|exact XF]. }
 exists mf;split.
 - cbn [schnorr_signature_read_statements statement_sequence].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=schnorr_r_read_temps le r);
   [exact RRead|exact SRead].
 - split;[exact RXF|];split;[exact Scalar|];split;[exact RBytesF|];split;[apply schnorr_r_raw_bounds|];split.
   + rewrite radix_limb_rho by apply word_toZ_range;apply Z.mod_small.
     split;[apply word_toZ_range|exact RBound].
   + split.
     * intros b pos kind perm P;apply KeepS,KeepR;exact P.
     * split.
       -- eapply lframe_trans.
          { eapply lframe_implies;[exact FrameR|].
            intros b pos (NX & _ & _ & NI) _ Foot;
             destruct (owned_b32_foot_bounds bx bsig b pos Foot) as [[Same _]|[Same _]];congruence. }
          { eapply lframe_implies;[exact FrameS|].
            intros b pos (_ & NS & NF & NI) _;split;[apply scalar_flag_foot_outside;repeat split;assumption|exact NF]. }
       -- eapply preserved_trans;[exact ReadR|exact ReadS].
Qed.
