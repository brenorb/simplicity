(** Original Strauss preprocessing loop at its generate zero-scalar caller. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Memory Values Events Maps.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_statement_prefix.
Require Import C.jet_secp_curve_statements C.jet_secp_generator_zero_scalar.
Require Import C.jet_secp_scalar_get_b32_storage.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque secp_ge.
Set Default Timeout 10.

Definition generator_preprocess_statement := nth 5
 (fst (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf))) Sskip.
Definition generator_preprocess_loop := match generator_preprocess_statement with
 | Ssequence _ loop=>loop | _=>Sskip end.
Definition generator_preprocess_work := match generator_preprocess_loop with
 | Sloop (Ssequence _ work) _=>work | _=>Sskip end.
Definition generator_preprocess_check := match generator_preprocess_work with
 | Ssequence check _=>check | _=>Sskip end.
Definition generator_preprocess_after_check := match generator_preprocess_work with
 | Ssequence _ rest=>rest | _=>Sskip end.
Definition generator_preprocess_other_flag := match generator_preprocess_check with
 | Ssequence (Ssequence _ (Sifthenelse _ _ alt)) _=>alt | _=>Sskip end.
Definition generator_preprocess_scalar_call := curve_call _secp256k1_scalar_is_zero
 f_secp256k1_scalar_is_zero (Some _t'1)
 [Ebinop Oadd (Etempvar _na (tptr (Tstruct __5826 noattr))) (Etempvar _np tulong)
   (tptr (Tstruct __5826 noattr))].

Lemma generator_preprocess_check_source : generator_preprocess_check=
 Ssequence
  (Ssequence generator_preprocess_scalar_call
    (Sifthenelse (Etempvar _t'1 tint) (Sset _t'2 (Econst_int Int.one tint)) generator_preprocess_other_flag))
  (Sifthenelse (Etempvar _t'2 tint) Scontinue Sskip).
Proof. reflexivity. Qed.
Lemma generator_preprocess_work_source : generator_preprocess_work=
 Ssequence generator_preprocess_check generator_preprocess_after_check.
Proof. reflexivity. Qed.
Lemma generator_preprocess_loop_source : generator_preprocess_loop=
 Sloop (Ssequence (Sifthenelse
  (Ebinop Olt (Etempvar _np tulong) (Etempvar _num tulong) tint) Sskip Sbreak)
  generator_preprocess_work)
  (Sset _np (Ebinop Oadd (Etempvar _np tulong) (Econst_int Int.one tint) tulong)).
Proof. reflexivity. Qed.
Lemma generator_preprocess_statement_source : generator_preprocess_statement=
 Ssequence (Sset _np (Ecast (Econst_int Int.zero tint) tulong)) generator_preprocess_loop.
Proof. reflexivity. Qed.

Definition generator_preprocess_checked le :=
 PTree.set _t'2 (Vint Int.one) (PTree.set _t'1 (Vint Int.one) le).

Lemma exec_generator_preprocess_check_zero e le m b ofs :
 e!_secp256k1_scalar_is_zero=None ->
 le!_na=Some (Vptr b (Ptrofs.repr ofs)) -> le!_np=Some (Vlong Int64.zero) ->
 scalar_at m b ofs [Int64.zero;Int64.zero;Int64.zero;Int64.zero] ->
 Clight2.exec_stmt secp_ge e le m generator_preprocess_check E0
  (generator_preprocess_checked le) m Out_continue.
Proof.
 intros Symbol NA NP Storage;rewrite generator_preprocess_check_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=generator_preprocess_checked le).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'1 (Vint Int.one) le).
   + unfold generator_preprocess_scalar_call;eapply exec_curve_call with
      (vargs:=[Vptr b (Ptrofs.repr ofs)]) (v:=Vint Int.one).
     * unfold secp_pure;repeat first [left;reflexivity|right].
     * exact Symbol.
     * eapply eval_Econs with (v1:=Vptr b (Ptrofs.repr ofs)).
       -- eapply eval_Ebinop with (v1:=Vptr b (Ptrofs.repr ofs)) (v2:=Vlong Int64.zero).
          ++ apply eval_Etempvar;exact NA.
          ++ apply eval_Etempvar;exact NP.
          ++ change (Some (Vptr b (Ptrofs.add (Ptrofs.repr ofs) Ptrofs.zero))=
               Some (Vptr b (Ptrofs.repr ofs))).
             rewrite Ptrofs.add_zero;reflexivity.
       -- reflexivity.
       -- constructor.
     * apply eval_generator_scalar_zero;exact Storage.
   + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
     * apply eval_Etempvar;apply PTree.gss.
     * reflexivity.
     * apply exec_Sset;constructor.
 - eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
   + apply eval_Etempvar;unfold generator_preprocess_checked;apply PTree.gss.
   + reflexivity.
   + constructor.
Qed.

Definition generator_preprocessed_temps le :=
 PTree.set _np (Vlong Int64.one) (generator_preprocess_checked (PTree.set _np (Vlong Int64.zero) le)).

Lemma generator_preprocessed_preserves le id : id<>_np -> id<>_t'1 -> id<>_t'2 ->
 (generator_preprocessed_temps le)!id=le!id.
Proof.
 intros NP T1 T2;unfold generator_preprocessed_temps,generator_preprocess_checked.
 rewrite PTree.gso by exact NP;rewrite PTree.gso by exact T2;
 rewrite PTree.gso by exact T1;rewrite PTree.gso by exact NP;reflexivity.
Qed.

Theorem exec_generator_preprocess_zero e le m b ofs :
 e!_secp256k1_scalar_is_zero=None ->
 le!_na=Some (Vptr b (Ptrofs.repr ofs)) -> le!_num=Some (Vlong Int64.one) ->
 scalar_at m b ofs [Int64.zero;Int64.zero;Int64.zero;Int64.zero] ->
 Clight2.exec_stmt secp_ge e le m generator_preprocess_statement E0
  (generator_preprocessed_temps le) m Out_normal.
Proof.
 intros Symbol NA Num Storage.
 set (l0:=PTree.set _np (Vlong Int64.zero) le).
 set (l1:=generator_preprocess_checked l0).
 set (l2:=PTree.set _np (Vlong Int64.one) l1).
 assert (NP0:l0!_np=Some (Vlong Int64.zero)) by (unfold l0;apply PTree.gss).
 assert (NA0:l0!_na=Some (Vptr b (Ptrofs.repr ofs))).
 { unfold l0;rewrite PTree.gso by discriminate;exact NA. }
 assert (Num0:l0!_num=Some (Vlong Int64.one)).
 { unfold l0;rewrite PTree.gso by discriminate;exact Num. }
 assert (NP1:l1!_np=Some (Vlong Int64.zero)).
 { unfold l1,generator_preprocess_checked;rewrite PTree.gso by discriminate;
   rewrite PTree.gso by discriminate;exact NP0. }
 assert (NP2:l2!_np=Some (Vlong Int64.one)) by (unfold l2;apply PTree.gss).
 assert (Num2:l2!_num=Some (Vlong Int64.one)).
 { unfold l2,l1,generator_preprocess_checked;rewrite PTree.gso by discriminate;
   rewrite PTree.gso by discriminate;rewrite PTree.gso by discriminate;exact Num0. }
 rewrite generator_preprocess_statement_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=l0).
 - apply exec_Sset;eapply eval_Ecast;[constructor|reflexivity].
 - rewrite generator_preprocess_loop_source.
   eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0)
    (m1:=m) (m2:=m) (le1:=l1) (le2:=l2) (out1:=Out_continue).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=l0).
     * eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|constructor].
       eapply eval_Ebinop;[apply eval_Etempvar;exact NP0|apply eval_Etempvar;exact Num0|reflexivity].
     * rewrite generator_preprocess_work_source;eapply exec_Sseq_2;[|discriminate].
       exact (exec_generator_preprocess_check_zero e l0 m b ofs Symbol NA0 NP0 Storage).
   + constructor.
   + apply exec_Sset;eapply eval_Ebinop;[apply eval_Etempvar;exact NP1|constructor|reflexivity].
   + eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
     eapply exec_Sseq_2;[|discriminate].
     eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
     eapply eval_Ebinop;[apply eval_Etempvar;exact NP2|apply eval_Etempvar;exact Num2|reflexivity].
Qed.
