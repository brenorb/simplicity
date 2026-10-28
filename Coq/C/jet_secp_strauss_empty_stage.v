(** Original zero-length point stage; no inactive table is read. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_generator_point_stage C.jet_secp_generator_loop_control
 C.jet_secp_generator_final C.jet_secp_double_statements C.jet_secp_double_flag
 C.jet_secp_gej_infinity_owned C.jet_secp_fe_nv.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Opaque secp_ge.
Set Default Timeout 10.

Definition strauss_empty_stage_temps le :=
 PTree.set _t'16 (Vint Int.one) (PTree.set _i (Vint (Int.repr (-1))) le).

Theorem exec_strauss_empty_point_stage e le m br :
 e!_secp256k1_gej_set_infinity=None ->
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_bits=Some (Vint Int.zero) ->
 Mem.range_perm m br 0 128 Cur Freeable ->
 exists mf,
 Clight2.exec_stmt secp_ge e le m generator_point_stage E0 (strauss_empty_stage_temps le) mf Out_normal /\
 fe_at mf br 0 (repeat Int64.zero 5) /\ fe_at mf br 40 (repeat Int64.zero 5) /\
 fe_at mf br 80 (repeat Int64.zero 5) /\ Mem.load Mint32 mf br 120=Some (Vint Int.one) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ lframe (fun b _=>b<>br) m mf /\
 (forall b pos k p,Mem.perm mf b pos k p <-> Mem.perm m b pos k p).
Proof.
 intros Symbol R Bits Owned.
 destruct (eval_gej_infinity_initializer_owned m br 0 ltac:(clear;lia)
  ltac:(exists 0;reflexivity) ltac:(change (128<=18446744073709551615);clear;lia)
  ltac:(intros pos Range;eapply Mem.perm_implies;[apply Owned;exact Range|constructor]))
  as (mf & Init & X & Y & Z & Flag & Loads & Perms & Valid).
 assert (Free:Mem.range_perm mf br 0 128 Cur Freeable).
 { intros pos Range;apply (proj2 (Perms _ _ _ _));apply Owned;exact Range. }
 assert (Frame:lframe (fun b _=>b<>br) m mf).
 { split.
   - intros chunk b ofs V Outside;apply Loads;left;apply (Outside ofs);pose proof (size_chunk_pos chunk);lia.
   - split;[intros b pos k p V Outside P;apply (proj2 (Perms _ _ _ _));exact P|exact Valid]. }
 pose (li:=PTree.set _i (Vint (Int.repr (-1))) le).
 pose (lf:=strauss_empty_stage_temps le).
 assert (RI:li!_r=Some (Vptr br Ptrofs.zero)) by (unfold li;rewrite PTree.gso by discriminate;exact R).
 assert (Loop:Clight2.exec_stmt secp_ge e li mf generator_descending_loop E0 li mf Out_normal).
 { apply exec_generator_loop_done;unfold li;apply PTree.gss. }
 assert (Read:Clight2.exec_stmt secp_ge e li mf
  (Sset _t'16 (double_point_field _r _infinity tint)) E0 lf mf Out_normal).
 { apply exec_Sset;eapply eval_Elvalue.
   - apply eval_double_flag_field;exact RI.
   - eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
     change (Mem.load Mint32 mf br 120=Some (Vint Int.one));exact Flag. }
 assert (Final:Clight2.exec_stmt secp_ge e li mf generator_final_statement E0 lf mf Out_normal).
 { rewrite generator_final_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Read|].
   eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
   eapply eval_Eunop;[apply eval_Etempvar;unfold lf,strauss_empty_stage_temps;apply PTree.gss|reflexivity]. }
 exists mf;split.
 - rewrite generator_point_stage_source.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mf).
   + unfold generator_infinity_statement;eapply exec_curve_call with (vargs:=[Vptr br Ptrofs.zero]) (v:=Vundef).
     * unfold secp_pure;repeat first [left;reflexivity|right].
     * exact Symbol.
     * eapply eval_Econs;[apply eval_Etempvar;exact R|reflexivity|constructor].
     * exact Init.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=li) (m1:=mf);[|exact Final].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[|exact Loop].
     unfold generator_start_index_statement;apply exec_Sset.
     eapply eval_Ebinop with (v1:=Vint Int.zero) (v2:=Vint Int.one);
      [apply eval_Etempvar;exact Bits|constructor|reflexivity].
 - split;[exact X|];split;[exact Y|];split;[exact Z|];split;[exact Flag|];
   split;[exact Free|];split;assumption.
Qed.

Lemma strauss_empty_stage_other le id : id<>_i -> id<>_t'16 ->
 (strauss_empty_stage_temps le)!id=le!id.
Proof. intros I T;unfold strauss_empty_stage_temps;rewrite !PTree.gso by assumption;reflexivity. Qed.
