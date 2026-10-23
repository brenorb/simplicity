(** The remaining original affine-infinity branch is a real struct self-copy. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements
 C.jet_secp_mixed_finite_start C.jet_secp_zinv_finite C.jet_secp_gej_add_infinite.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Lemma zinv_b_infinite_source : zinv_b_head =
 Ssequence (Sset _t'3 (mixed_b_field _infinity tint))
 (Sifthenelse (Etempvar _t'3 tint) (Ssequence gej_add_copy_a (Sreturn None)) Sskip).
Proof. reflexivity. Qed.
Theorem exec_zinv_b_infinite e le m bp ba flag :
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
 Mem.load Mint32 m bp 120=Some (Vint Int.zero) -> Mem.load Mint32 m ba 80=Some (Vint flag) ->
 flag<>Int.zero -> Mem.range_perm m bp 0 128 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_zinv_var) E0
 (PTree.set _t'3 (Vint flag) (PTree.set _t'4 (Vint Int.zero) le)) mf (Out_return None) /\
 lframe (fun _ _=>True) m mf.
Proof.
 intros HA HR HB FlagA FlagB NZ Free.
 set (leB := PTree.set _t'3 (Vint flag) (PTree.set _t'4 (Vint Int.zero) le)).
 destruct (exec_gej_add_self_copy e leB m bp
   ltac:(unfold leB;rewrite !PTree.gso by discriminate;exact HA)
   ltac:(unfold leB;rewrite !PTree.gso by discriminate;exact HR) Free) as (mf & Copy & Frame).
 exists mf;split;[|exact Frame].
 rewrite zinv_body_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'4 (Vint Int.zero) le).
 - exact (exec_zinv_a_head_finite e le m bp HA FlagA).
 - eapply exec_Sseq_2;[|discriminate].
   rewrite zinv_b_infinite_source.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=leB).
   + apply exec_Sset;eapply eval_Elvalue.
     * apply eval_mixed_b_field;[cbn [In];tauto|rewrite PTree.gso by discriminate;exact HB].
     * eapply deref_loc_value with (chunk:=Mint32);[reflexivity|exact FlagB].
   + eapply exec_Sifthenelse with (v1:=Vint flag) (b:=true).
     * apply eval_Etempvar;unfold leB;apply PTree.gss.
     * change (Some (negb (Int.eq flag Int.zero))=Some true);rewrite Int.eq_false by exact NZ;reflexivity.
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=leB);[exact Copy|apply exec_Sreturn_none].
Qed.
