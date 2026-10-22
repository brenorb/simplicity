(** The original projective-addition infinity early returns, in place at A. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_double_statements C.jet_secp_double_flag
 C.jet_secp_gej_add_statements C.jet_secp_gej_add_finite_start C.jet_secp_gej_copy_owned
 C.jet_secp_self_copy_assign C.jet_secp_double_var_statements C.jet_exec.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition gej_add_copy_b := Sassign
 (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr))) (Tstruct __6123 noattr))
 (Ederef (Etempvar _b (tptr (Tstruct __6123 noattr))) (Tstruct __6123 noattr)).
Lemma gej_add_head_source : gej_add_flag_head false=
 Ssequence (Sset _t'4 (double_point_field _a _infinity tint))
 (Sifthenelse (Etempvar _t'4 tint)
   (Ssequence (Sloop Sskip Sbreak) (Ssequence gej_add_copy_b (Sreturn None))) Sskip).
Proof. reflexivity. Qed.
Lemma gej_add_head_then_rest : fn_body f_secp256k1_gej_add_var=
 Ssequence (gej_add_flag_head false) (gej_add_after 1).
Proof. reflexivity. Qed.

Theorem exec_gej_add_a_infinite e le m ba bb x y z flagA flagB :
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
 le!_b=Some (Vptr bb Ptrofs.zero) -> ba<>bb ->
 Mem.load Mint32 m ba 120=Some (Vint flagA) -> flagA<>Int.zero ->
 Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bb 0 128 Cur Freeable ->
 fe_at m bb 0 (words5 x) -> fe_at m bb 40 (words5 y) -> fe_at m bb 80 (words5 z) ->
 Mem.load Mint32 m bb 120=Some (Vint flagB) -> exists mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_var) E0
  (PTree.set _t'4 (Vint flagA) le) mf (Out_return None) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
 Mem.load Mint32 mf ba 120=Some (Vint flagB) /\
 Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bb 0 128 Cur Freeable /\
 lframe (fun b _=>b<>ba) m mf.
Proof.
 intros A R B Sep FlagA NZ FA FB X Y Z FlagB.
 set (leA := PTree.set _t'4 (Vint flagA) le).
 destruct (exec_gej_copy_owned e leA m
   (Ederef (Etempvar _b (tptr (Tstruct __6123 noattr))) (Tstruct __6123 noattr))
   (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr))) (Tstruct __6123 noattr))
   bb ba x y z flagB eq_refl eq_refl
   ltac:(eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;unfold leA;rewrite PTree.gso by discriminate;exact B|apply deref_loc_copy;reflexivity])
   ltac:(apply eval_Ederef;apply eval_Etempvar;unfold leA;rewrite PTree.gso by discriminate;exact R)
   ltac:(congruence) FB FA X Y Z FlagB)
   as (mf & Copy & XO & YO & ZO & FlagO & FBF & FAF & Frame).
 exists mf;split.
 - rewrite gej_add_head_then_rest;eapply exec_Sseq_2.
   + rewrite gej_add_head_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=leA).
     * apply exec_Sset;eapply eval_Elvalue.
       -- apply eval_double_flag_field;exact A.
       -- eapply deref_loc_value with (chunk:=Mint32);[reflexivity|exact FlagA].
     * eapply exec_Sifthenelse with (v1:=Vint flagA) (b:=true).
       -- apply eval_Etempvar;apply PTree.gss.
       -- change (Some (negb (Int.eq flagA Int.zero))=Some true);rewrite Int.eq_false by exact NZ;reflexivity.
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=leA).
          ++ eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=leA) (out1:=Out_normal);
               [apply exec_Sskip|constructor|apply exec_Sbreak|constructor].
          ++ eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=leA);
               [exact Copy|apply exec_Sreturn_none].
   + discriminate.
 - split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FlagO|];
   split;[exact FAF|];split;[exact FBF|exact Frame].
Qed.

Definition gej_add_copy_a := Sassign
 (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr))) (Tstruct __6123 noattr))
 (Ederef (Etempvar _a (tptr (Tstruct __6123 noattr))) (Tstruct __6123 noattr)).
Lemma exec_gej_add_self_copy e le m ba :
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
 Mem.range_perm m ba 0 128 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m gej_add_copy_a E0 le mf Out_normal /\
 lframe (fun _ _=>True) m mf.
Proof.
 intros A R Free.
 assert (Align : sizeof secp_ge (Tstruct __6123 noattr)>0 ->
   (alignof_blockcopy secp_ge (Tstruct __6123 noattr)|Ptrofs.unsigned Ptrofs.zero)).
 { intros _;change (8|0);exists 0;reflexivity. }
 assert (WritePerm : Mem.range_perm m ba (Ptrofs.unsigned Ptrofs.zero)
   (Ptrofs.unsigned Ptrofs.zero+sizeof secp_ge (Tstruct __6123 noattr)) Cur Writable).
 { change (Mem.range_perm m ba 0 128 Cur Writable).
   intros pos Pos;eapply Mem.perm_implies;[apply Free;exact Pos|constructor]. }
 destruct (assign_loc_owned_self_copy secp_ge (Tstruct __6123 noattr) m ba Ptrofs.zero
   eq_refl ltac:(change (0<=128);lia) Align WritePerm) as (mf & Assign & Unchanged).
 exists mf;split.
 - unfold gej_add_copy_a;eapply exec_Sassign_copy with (b:=ba) (b':=ba)
    (ofs:=Ptrofs.zero) (ofs':=Ptrofs.zero) (v:=Vptr ba Ptrofs.zero).
   + apply eval_Ederef;apply eval_Etempvar;exact R.
   + eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact A|apply deref_loc_copy;reflexivity].
   + reflexivity.
   + exact Assign.
 - apply lframe_unchanged;exact Unchanged.
Qed.

Definition gej_add_b_infinite_branch := match gej_add_flag_head true with
 | Ssequence _ (Sifthenelse _ branch _) => branch | _ => Sskip end.
Lemma gej_add_b_branch_source : gej_add_b_infinite_branch=
 Ssequence (Sifthenelse double_var_null_test
   (C.jet_secp_curve_statements.curve_call _secp256k1_fe_set_int f_secp256k1_fe_set_int None
     [Etempvar _rzr (tptr (Tstruct __5467 noattr));Econst_int Int.one tint]) Sskip)
   (Ssequence gej_add_copy_a (Sreturn None)).
Proof. reflexivity. Qed.

Theorem exec_gej_add_b_infinite e le m ba bb flagB :
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
 le!_b=Some (Vptr bb Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
 Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
 Mem.load Mint32 m bb 120=Some (Vint flagB) -> flagB<>Int.zero ->
 Mem.range_perm m ba 0 128 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_var) E0
  (PTree.set _t'3 (Vint flagB) (PTree.set _t'4 (Vint Int.zero) le)) mf (Out_return None) /\
 lframe (fun _ _=>True) m mf.
Proof.
 intros A R B Null FlagA FlagB NZ Free.
 set (leB := PTree.set _t'3 (Vint flagB) (PTree.set _t'4 (Vint Int.zero) le)).
 destruct (exec_gej_add_self_copy e leB m ba
   ltac:(unfold leB;rewrite !PTree.gso by discriminate;exact A)
   ltac:(unfold leB;rewrite !PTree.gso by discriminate;exact R) Free) as (mf & Copy & Frame).
 exists mf;split;[|exact Frame].
 rewrite gej_add_head_then_rest.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'4 (Vint Int.zero) le).
 - apply exec_gej_add_flag_finite with (bp:=ba);assumption.
 - change (Clight2.exec_stmt secp_ge e (PTree.set _t'4 (Vint Int.zero) le) m
    (Ssequence (gej_add_flag_head true) (gej_add_after 2)) E0 leB mf (Out_return None)).
   eapply exec_Sseq_2.
   + change (Clight2.exec_stmt secp_ge e (PTree.set _t'4 (Vint Int.zero) le) m
      (Ssequence (Sset _t'3 (double_point_field _b _infinity tint))
       (Sifthenelse (Etempvar _t'3 tint) gej_add_b_infinite_branch Sskip)) E0 leB mf (Out_return None)).
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=leB).
     * apply exec_Sset;eapply eval_Elvalue.
       -- apply eval_double_flag_field;rewrite PTree.gso by discriminate;exact B.
       -- eapply deref_loc_value with (chunk:=Mint32);[reflexivity|exact FlagB].
     * eapply exec_Sifthenelse with (v1:=Vint flagB) (b:=true).
       -- apply eval_Etempvar;apply PTree.gss.
       -- change (Some (negb (Int.eq flagB Int.zero))=Some true);rewrite Int.eq_false by exact NZ;reflexivity.
       -- rewrite gej_add_b_branch_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=leB).
          ++ eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
             ** apply eval_double_var_null_test;unfold leB;rewrite !PTree.gso by discriminate;exact Null.
             ** reflexivity.
             ** apply exec_Sskip.
          ++ eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=leB);
               [exact Copy|apply exec_Sreturn_none].
   + discriminate.
Qed.
