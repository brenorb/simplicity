(** Complete original ge_set_xo_var body, including both root outcomes and
    both parity outcomes. The literal output and function boundary are separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_curve_statements
 C.jet_secp_curve_frame C.jet_secp_statement_prefix C.jet_secp_root_chain_numeric C.jet_secp_root_check
 C.jet_secp_rescale_literal C.jet_secp_decompress_literal C.jet_secp_decompress_numeric
 C.jet_secp_decompress_statements C.jet_secp_decompress_prefix C.jet_secp_decompress_root_test
 C.jet_secp_root_affine_y_state C.jet_secp_decompress_parity.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge root_chain_candidate root_check_flag decompress_root_words
 literal_y_from_x rescale_field_output decompress_parity_limbs decompress_parity_temps.

Definition decompress_body_value w := radix_value (root_chain_candidate (decompress_root_words w)) mod feP.
Definition decompress_body_y w (odd : bool) := if root_check_flag (decompress_root_words w)
 then decompress_parity_limbs (decompress_body_value w) odd else words5 (root_chain_candidate (decompress_root_words w)).
Definition decompress_body_temps le w := if root_check_flag (decompress_root_words w)
 then decompress_parity_temps (decompress_root_temps le w) (decompress_body_value w) else decompress_root_temps le w.
Definition decompress_body_return w := if root_check_flag (decompress_root_words w) then Int.one else Int.zero.

Theorem exec_decompress_body_owned e le m bx br b2 b3 w (x : Ty.tySem (Word 8)) (odd : bool) :
 le!_x=Some (Vptr bx Ptrofs.zero) -> le!_r=Some (Vptr br Ptrofs.zero) ->
 le!_odd=Some (Vint (if odd then Int.one else Int.zero)) ->
 e!_x2=Some (b2,curve_fe_type) -> e!_x3=Some (b3,curve_fe_type) ->
 e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_add_int=None ->
 e!_secp256k1_fe_sqrt_var=None -> e!_secp256k1_fe_normalize_var=None ->
 e!_secp256k1_fe_is_odd=None -> e!_secp256k1_fe_negate=None ->
 NoDup [bx;br;b2;b3] -> root_words_match w x -> fe_at m bx 0 (words5 w) ->
 Mem.range_perm m bx 0 40 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable ->
 Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_ge_set_xo_var) E0
  (decompress_body_temps le w) mf (Out_return (Some (Vint (decompress_body_return w),tint))) /\
 fe_at mf br 0 (words5 w) /\ fe_at mf br 40 (decompress_body_y w odd) /\
 Mem.load Mint32 mf br 80=Some (Vint Int.zero) /\
 @literal_y_from_x Alg.CoreFunSem x=(if root_check_flag (decompress_root_words w)
  then inr (rescale_field_output (root_chain_candidate (decompress_root_words w))) else inl tt) /\
 Mem.range_perm mf bx 0 40 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
 lframe (decompress_prefix_frame bx br b2 b3) m mf.
Proof.
 intros HX HR HO E2 E3 EQ EM EA ER EV EO EN Sep Match Input XF RF F2 F3.
 assert (Pairs : bx<>br /\ bx<>b3 /\ br<>b3 /\ b2<>br /\ b2<>b3).
 { repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence. }
 destruct Pairs as (XR & X3 & R3 & N2R & N23).
 destruct (exec_decompress_prefix_owned e le m bx br b2 b3 w HX HR E2 E3 EQ EM EA Sep
  (proj1 Match) Input XF RF F2 F3)
  as (mi & Prefix & IX & RX & RootInput & Finite & XFI & RFI & F2I & F3I & FrameP).
 destruct (exec_decompress_root_test_owned e le mi br b3 w x HR E3 ER ltac:(congruence)
  Match RootInput F3I RFI) as (mr & Test & Y & Bounds & Literal & F3R & RFR & FrameR).
 assert (RXR : fe_at mr br 0 (words5 w)).
 { eapply curve_keep_field_range;[reflexivity|exact RX|exact FrameR|].
   intros pos Range;split;[exact R3|right;left;lia]. }
 assert (XFR : Mem.range_perm mr bx 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact XFI|exact FrameR|];intros;split;[exact X3|left;exact XR]. }
 assert (F2R : Mem.range_perm mr b2 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F2I|exact FrameR|];intros;split;[exact N23|left;exact N2R]. }
 assert (FiniteR : Mem.load Mint32 mr br 80=Some (Vint Int.zero)).
 { rewrite (proj1 FrameR Mint32 br 80 ltac:(eapply Mem.perm_valid_block;apply (RFI 0);lia)).
   - exact Finite.
   - intros pos Range;split;[exact R3|right;right;change (80<=pos<84) in Range;lia]. }
 assert (FramePR : lframe (decompress_prefix_frame bx br b2 b3) m mr).
 { eapply lframe_trans;[exact FrameP|].
   eapply lframe_implies;[exact FrameR|];intros b pos [NX [NR [N2 N3]]] _;split;[exact N3|left;exact NR]. }
 unfold decompress_root_outcome in Test.
 destruct (root_check_flag (decompress_root_words w)) eqn:Flag.
 - assert (HR1 : (decompress_root_temps le w)!_r=Some (Vptr br Ptrofs.zero)).
   { unfold decompress_root_temps;rewrite PTree.gso by discriminate;exact HR. }
   assert (HO1 : (decompress_root_temps le w)!_odd=Some (Vint (if odd then Int.one else Int.zero))).
   { unfold decompress_root_temps;rewrite PTree.gso by discriminate;exact HO. }
   destruct (exec_decompress_success_tail e (decompress_root_temps le w) mr br
    (root_chain_candidate (decompress_root_words w)) odd HR1 HO1 EV EO EN Bounds Y RFR)
    as (mf & Tail & Output & RFF & FrameT).
   assert (RXF : fe_at mf br 0 (words5 w)).
   { eapply curve_keep_field_range;[reflexivity|exact RXR|exact FrameT|].
     intros pos Range;right;left;lia. }
   assert (FiniteF : Mem.load Mint32 mf br 80=Some (Vint Int.zero)).
   { rewrite (proj1 FrameT Mint32 br 80 ltac:(eapply Mem.perm_valid_block;apply (RFR 0);lia)).
     - exact FiniteR.
     - intros pos Range;right;right;change (80<=pos<84) in Range;lia. }
   assert (XFF : Mem.range_perm mf bx 0 40 Cur Freeable).
   { eapply curve_keep_free;[lia|exact XFR|exact FrameT|];intros;left;exact XR. }
   assert (F2F : Mem.range_perm mf b2 0 40 Cur Freeable).
   { eapply curve_keep_free;[lia|exact F2R|exact FrameT|];intros;left;exact N2R. }
   assert (F3F : Mem.range_perm mf b3 0 40 Cur Freeable).
   { eapply curve_keep_free;[lia|exact F3R|exact FrameT|];intros;left;congruence. }
   exists mf;unfold decompress_body_temps,decompress_body_return,decompress_body_y;rewrite Flag;split.
   + rewrite decompress_helper_body_source.
     eapply exec_statement_prefix_then_last;[exact Prefix|].
     rewrite decompress_rest_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Test|exact Tail].
   + split;[exact RXF|];split;[exact Output|];split;[exact FiniteF|];split;[exact Literal|].
     split;[exact XFF|];split;[exact RFF|];split;[exact F2F|];split;[exact F3F|].
     eapply lframe_trans;[exact FramePR|].
     eapply lframe_implies;[exact FrameT|];intros b pos [NX [NR [N2 N3]]] _;left;exact NR.
 - exists mr;unfold decompress_body_temps,decompress_body_return,decompress_body_y;rewrite Flag;split.
   + rewrite decompress_helper_body_source.
     eapply exec_statement_prefix_then_last;[exact Prefix|].
     rewrite decompress_rest_source;eapply exec_Sseq_2;[exact Test|discriminate].
   + split;[exact RXR|];split;[exact Y|];split;[exact FiniteR|];split;[exact Literal|].
     split;[exact XFR|];split;[exact RFR|];split;[exact F2R|];split;assumption.
Qed.
