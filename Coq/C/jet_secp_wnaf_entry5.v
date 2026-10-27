(** Entry and initialization of the original 129/5 variable-point caller. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Cop Clight Clightdefs ClightBigstep Integers Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix
 C.jet_secp_wnaf_digit C.jet_secp_wnaf_control C.jet_secp_wnaf_prepare C.jet_secp_wnaf_entry15.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition wnaf_entry5_temps b base a :=
 PTree.set _w (Vint (Int.repr 5)) (PTree.set _a a (PTree.set _len (Vint (Int.repr 129))
 (PTree.set _wnaf (Vptr b (Ptrofs.repr base)) (create_undef_temps (fn_temps f_secp256k1_ecmult_wnaf))))).

Lemma wnaf_entry5 m mi bs b base a : Mem.alloc m 0 32=(mi,bs) ->
 function_entry2 secp_ge f_secp256k1_ecmult_wnaf
 [Vptr b (Ptrofs.repr base);Vint (Int.repr 129);a;Vint (Int.repr 5)] m
 (wnaf_env bs) (wnaf_entry5_temps b base a) mi.
Proof.
 intro Alloc;destruct (fn_okb_true _ wnaf_entry15_ok) as (Vars & Params & Disjoint).
 constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
 eapply alloc_variables_cons with (m1:=mi) (b1:=bs);[exact Alloc|constructor].
Qed.

Theorem exec_wnaf_before_memset5 e le m :
 le!_len=Some (Vint (Int.repr 129)) -> le!_w=Some (Vint (Int.repr 5)) ->
 Clight2.exec_stmt secp_ge e le m wnaf_before_memset E0 (wnaf_before_temps le) m Out_normal.
Proof.
 intros Len W;unfold wnaf_before_memset;rewrite wnaf_before_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply exec_Sset;eapply eval_Eunop;[constructor|reflexivity]|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply exec_Sset;constructor|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply exec_Sset;constructor|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply exec_Sset;constructor|].
 change (Clight2.exec_stmt secp_ge e (wnaf_before_temps le) m
  (Ssequence (Sloop Sskip Sbreak)
   (Ssequence (Sloop (Sifthenelse (Ebinop Ole (Econst_int Int.zero tint) (Etempvar _len tint) tint) Sskip Sskip) Sbreak)
    (Ssequence (Sloop Sskip Sbreak)
     (Ssequence (Sloop (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 2) tint) (Etempvar _w tint) tint) Sskip Sskip) Sbreak) Sskip))))
  E0 (wnaf_before_temps le) m Out_normal).
 assert (LenReady:(wnaf_before_temps le)!_len=Some (Vint (Int.repr 129)))
  by (rewrite wnaf_before_preserves by discriminate;exact Len).
 assert (WReady:(wnaf_before_temps le)!_w=Some (Vint (Int.repr 5)))
  by (rewrite wnaf_before_preserves by discriminate;exact W).
 repeat eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=wnaf_before_temps le).
 - eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (out1:=Out_normal) (out2:=Out_break);constructor.
 - eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (out1:=Out_normal) (out2:=Out_break);[|constructor|constructor|constructor].
   eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|constructor].
   eapply eval_Ebinop with (v1:=Vint Int.zero) (v2:=Vint (Int.repr 129));
    [constructor|apply eval_Etempvar;exact LenReady|reflexivity].
 - eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (out1:=Out_normal) (out2:=Out_break);constructor.
 - eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (out1:=Out_normal) (out2:=Out_break);[|constructor|constructor|constructor].
   eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|constructor].
   eapply eval_Ebinop with (v1:=Vint (Int.repr 2)) (v2:=Vint (Int.repr 5));
    [constructor|apply eval_Etempvar;exact WReady|reflexivity].
 - constructor.
Qed.
