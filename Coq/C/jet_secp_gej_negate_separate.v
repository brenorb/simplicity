(** Original projective negation into a distinct, uninitialized point.
    This is the first helper call made by the original gej_eq_ge_var. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_mem C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_b32_exec C.jet_secp_curve_frame
 C.jet_secp_gej_flag_read C.jet_secp_gej_read_flag_store C.jet_secp_gej_negate_flag
 C.jet_secp_gej_negate_fields C.jet_secp_gej_negate_prefix C.jet_secp_gej_negate_y_tail
 C.jet_secp_gej_negate_separate_copy C.jet_secp_point_write_run C.jet_secp_point_write_preservation
 C.jet_secp_field_negate_storage C.jet_secp_write_fe_numeric.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem exec_gej_negate_separate_flag le m bs bd flag :
 le!_a=Some (Vptr bs Ptrofs.zero) -> le!_r=Some (Vptr bd Ptrofs.zero) ->
 Mem.range_perm m bd 0 128 Cur Freeable -> Mem.load Mint32 m bs 120=Some (Vint flag) -> exists mi,
 Clight2.exec_stmt secp_ge empty_env le m gej_negate_flag_prefix E0
  (PTree.set _t'1 (Vint flag) le) mi Out_normal /\
 Mem.load Mint32 mi bd 120=Some (Vint flag) /\ Mem.range_perm mi bd 0 128 Cur Freeable /\
 lframe (fun b _=>b<>bd) m mi.
Proof.
 intros Src Dst Free Flag.
 assert (DstT : (PTree.set _t'1 (Vint flag) le)!_r=Some (Vptr bd Ptrofs.zero))
  by (rewrite PTree.gso by discriminate;exact Dst).
 destruct (exec_gej_read_flag_owned (PTree.set _t'1 (Vint flag) le) m bd 0 flag
  ltac:(lia) ltac:(exists 0;lia) ltac:(change (128<=18446744073709551615);lia)
  DstT ltac:(apply PTree.gss) Free) as (mi & Store & FlagI & FreeI & Loads & Perms & Valid).
 exists mi;split.
 - unfold gej_negate_flag_prefix;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0)
    (m1:=m) (le1:=PTree.set _t'1 (Vint flag) le).
   + apply exec_Sset;exact (eval_gej_flag_load m le bs 0 flag ltac:(lia)
      ltac:(change (128<=18446744073709551615);lia) Src Flag).
   + exact Store.
 - split;[exact FlagI|];split;[exact FreeI|];split.
   + intros chunk b ofs VB Outside;apply Loads;left;apply (Outside ofs);pose proof (size_chunk_pos chunk);lia.
   + split;[intros b pos k p VB Outside HP;apply (proj2 (Perms b pos k p));exact HP|exact Valid].
Qed.

Definition gej_negate_separate_temps bs bd :=
 PTree.set _a (Vptr bs Ptrofs.zero) (PTree.set _r (Vptr bd Ptrofs.zero)
  (create_undef_temps (fn_temps f_secp256k1_gej_neg))).

Lemma gej_negate_separate_entry m bs bd :
 function_entry2 secp_ge f_secp256k1_gej_neg [Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero]
  m empty_env (gej_negate_separate_temps bs bd) m.
Proof.
 assert (Ok : fn_okb f_secp256k1_gej_neg=true) by reflexivity.
 destruct (fn_okb_true _ Ok) as (HN1 & HN2 & HD).
 constructor;[exact HN1|exact HN2|exact HD|constructor|reflexivity].
Qed.

Theorem exec_gej_negate_separate_body le m bs bd x value z flag :
 bs<>bd -> le!_a=Some (Vptr bs Ptrofs.zero) -> le!_r=Some (Vptr bd Ptrofs.zero) ->
 0<=value<2^256 -> fe_at m bs 0 (words5 x) ->
 fe_at m bs 40 (words5 (limb_rho value)) -> fe_at m bs 80 (words5 z) ->
 Mem.load Mint32 m bs 120=Some (Vint flag) -> Mem.range_perm m bd 0 128 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge empty_env le m (fn_body f_secp256k1_gej_neg) E0
  (PTree.set _t'1 (Vint flag) le) mf Out_normal /\
 fe_at mf bd 0 (words5 x) /\ fe_at mf bd 40 (negate_values (write_fe_rho value 0)) /\
 fe_at mf bd 80 (words5 z) /\ Mem.load Mint32 mf bd 120=Some (Vint flag) /\
 Mem.range_perm mf bd 0 128 Cur Freeable /\ lframe (fun b _=>b<>bd) m mf.
Proof.
 intros NE Src Dst Bound X Y Z Flag Free.
 destruct (exec_gej_negate_separate_flag le m bs bd flag Src Dst Free Flag)
  as (mi & Prefix & FlagI & FreeI & FrameI).
 assert (XI : fe_at mi bs 0 (words5 x)).
 { eapply curve_keep_field_range;[reflexivity|exact X|exact FrameI|];intros;exact NE. }
 assert (YI : fe_at mi bs 40 (words5 (limb_rho value))).
 { eapply curve_keep_field_range;[reflexivity|exact Y|exact FrameI|];intros;exact NE. }
 assert (ZI : fe_at mi bs 80 (words5 z)).
 { eapply curve_keep_field_range;[reflexivity|exact Z|exact FrameI|];intros;exact NE. }
 assert (SrcT : (PTree.set _t'1 (Vint flag) le)!_a=Some (Vptr bs Ptrofs.zero))
  by (rewrite PTree.gso by discriminate;exact Src).
 assert (DstT : (PTree.set _t'1 (Vint flag) le)!_r=Some (Vptr bd Ptrofs.zero))
  by (rewrite PTree.gso by discriminate;exact Dst).
 destruct (exec_gej_negate_separate_three_copies (PTree.set _t'1 (Vint flag) le)
  mi bs bd x (limb_rho value) z NE SrcT DstT XI YI ZI FreeI)
  as (mx & my & mz & CopyX & CopyY & CopyZ & XZ & YZ & ZZ & FreeZ & FrameZ).
 assert (FlagZ : Mem.load Mint32 mz bd 120=Some (Vint flag)).
 { rewrite (proj1 FrameZ Mint32 bd 120);[exact FlagI| |].
   - eapply Mem.perm_valid_block;apply (FreeI 0);lia.
   - intros pos HP;right;change (120<=pos<124) in HP;lia. }
 change (fe_at mz bd 40 (map Int64.repr (fe_limbs_of value))) in YZ.
 destruct (exec_gej_negate_y_tail_owned (PTree.set _t'1 (Vint flag) le) mz bd value
  DstT Bound YZ FreeZ) as (mf & Tail & YF & FreeF & FrameF).
 assert (XF : fe_at mf bd 0 (words5 x)).
 { eapply curve_keep_field_range;[reflexivity|exact XZ|exact FrameF|].
   intros pos HP Foot;destruct (point_write_foot_bounds PointY bd bd pos Foot) as [_ Range].
   change (40<=pos<80) in Range;lia. }
 assert (ZF : fe_at mf bd 80 (words5 z)).
 { eapply curve_keep_field_range;[reflexivity|exact ZZ|exact FrameF|].
   intros pos HP Foot;destruct (point_write_foot_bounds PointY bd bd pos Foot) as [_ Range].
   change (40<=pos<80) in Range;lia. }
 assert (FlagF : Mem.load Mint32 mf bd 120=Some (Vint flag)).
 { rewrite (proj1 FrameF Mint32 bd 120);[exact FlagZ| |].
   - eapply Mem.perm_valid_block;apply (FreeZ 0);lia.
   - intros pos HP Foot;destruct (point_write_foot_bounds PointY bd bd pos Foot) as [_ Range].
     change (120<=pos<124) in HP;change (40<=pos<80) in Range;lia. }
 exists mf;split.
 - rewrite gej_negate_helper_body.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi)
    (le1:=PTree.set _t'1 (Vint flag) le);[exact Prefix|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mx)
    (le1:=PTree.set _t'1 (Vint flag) le);[exact CopyX|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=my)
    (le1:=PTree.set _t'1 (Vint flag) le);[exact CopyY|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz)
    (le1:=PTree.set _t'1 (Vint flag) le);[exact CopyZ|exact Tail].
 - split;[exact XF|];split;[exact YF|];split;[exact ZF|];split;[exact FlagF|];split;[exact FreeF|].
   eapply lframe_trans;[exact FrameI|];eapply lframe_trans.
   + eapply lframe_implies;[exact FrameZ|];intros b pos NEB VB;left;exact NEB.
   + eapply lframe_implies;[exact FrameF|];intros b pos NEB VB Foot.
     destruct (point_write_foot_bounds PointY bd b pos Foot) as [HE _];contradiction.
Qed.

Theorem eval_gej_negate_separate m bs bd x value z flag :
 bs<>bd -> 0<=value<2^256 -> fe_at m bs 0 (words5 x) ->
 fe_at m bs 40 (words5 (limb_rho value)) -> fe_at m bs 80 (words5 z) ->
 Mem.load Mint32 m bs 120=Some (Vint flag) -> Mem.range_perm m bd 0 128 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_neg)
  [Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef /\
 fe_at mf bd 0 (words5 x) /\ fe_at mf bd 40 (negate_values (write_fe_rho value 0)) /\
 fe_at mf bd 80 (words5 z) /\ Mem.load Mint32 mf bd 120=Some (Vint flag) /\
 Mem.range_perm mf bd 0 128 Cur Freeable /\ lframe (fun b _=>b<>bd) m mf.
Proof.
 intros NE Bound X Y Z Flag Free.
 destruct (exec_gej_negate_separate_body (gej_negate_separate_temps bs bd) m bs bd x value z flag
  NE ltac:(apply PTree.gss) ltac:(unfold gej_negate_separate_temps;rewrite PTree.gso by discriminate;apply PTree.gss)
  Bound X Y Z Flag Free) as (mf & Body & XF & YF & ZF & FlagF & FreeF & FrameF).
 exists mf;split.
 - eapply eval_funcall_internal with (e:=empty_env) (le1:=gej_negate_separate_temps bs bd)
    (le2:=PTree.set _t'1 (Vint flag) (gej_negate_separate_temps bs bd))
    (m1:=m) (m2:=mf) (out:=Out_normal).
   + apply gej_negate_separate_entry.
   + exact Body.
   + reflexivity.
   + reflexivity.
 - split;[exact XF|];split;[exact YF|];split;[exact ZF|];split;[exact FlagF|];split;assumption.
Qed.
