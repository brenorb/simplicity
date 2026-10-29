(** Exact short-circuit control of the original point verifier. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_readBit_layout C.jet_secp_linkage C.jets_secp
 C.jet_secp_curve_statements C.jet_secp_linear_verify_public_body.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition point_verify_guard_call pv xv parity dest :=
 curve_call _secp256k1_ge_set_xo_var f_secp256k1_ge_set_xo_var (Some dest)
 [Eaddrof (Evar pv (Tstruct __6121 noattr)) (tptr (Tstruct __6121 noattr));
  Eaddrof (Evar xv (Tstruct __5467 noattr)) (tptr (Tstruct __5467 noattr));Etempvar parity tbool].
Definition point_verify_guards := Ssequence (point_verify_guard_call _a__1 _ax _ay _t'4)
 (Sifthenelse (Etempvar _t'4 tint)
  (Ssequence (point_verify_guard_call _b _bx _by _t'6)
    (Sset _t'5 (Ecast (Etempvar _t'6 tint) tbool)))
  (Sset _t'5 (Econst_int Int.zero tint))).
Definition point_verify_guard_temps le (a b:bool) :=
 if a then PTree.set _t'5 (Vint (bit_int b))
  (PTree.set _t'6 (Vint (bit_int b)) (PTree.set _t'4 (Vint Int.one) le))
 else PTree.set _t'5 (Vint Int.zero) (PTree.set _t'4 (Vint Int.zero) le).

Lemma exec_point_verify_guard_call e le m mf pv xv parity dest bp bx odd good :
 e!pv=Some (bp,Tstruct __6121 noattr) -> e!xv=Some (bx,Tstruct __5467 noattr) ->
 e!_secp256k1_ge_set_xo_var=None -> le!parity=Some (Vint (bit_int odd)) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_xo_var)
  [Vptr bp Ptrofs.zero;Vptr bx Ptrofs.zero;Vint (bit_int odd)] E0 mf (Vint (bit_int good)) ->
 Clight2.exec_stmt secp_ge e le m (point_verify_guard_call pv xv parity dest) E0
  (PTree.set dest (Vint (bit_int good)) le) mf Out_normal.
Proof.
 intros EP EX EG Odd Call;unfold point_verify_guard_call.
 eapply linear_verify_direct_call with (dest:=Some dest) (v:=Vint (bit_int good));
 [reflexivity|reflexivity|exact EG| |exact Call].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact EP|reflexivity|].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact EX|reflexivity|].
 eapply eval_Econs;[apply eval_Etempvar;exact Odd|destruct odd;reflexivity|constructor].
Qed.
Lemma point_verify_guard_result le a b :
 (point_verify_guard_temps le a b)!_t'5=Some (Vint (bit_int (andb a b))).
Proof. destruct a;apply PTree.gss. Qed.

Theorem exec_point_verify_guards e le m ma mf ba bb bax bbx ay bybit a b :
 e!_a__1=Some (ba,Tstruct __6121 noattr) -> e!_b=Some (bb,Tstruct __6121 noattr) ->
 e!_ax=Some (bax,Tstruct __5467 noattr) -> e!_bx=Some (bbx,Tstruct __5467 noattr) ->
 e!_secp256k1_ge_set_xo_var=None ->
 le!_ay=Some (Vint (bit_int ay)) -> le!_by=Some (Vint (bit_int bybit)) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_xo_var)
  [Vptr ba Ptrofs.zero;Vptr bax Ptrofs.zero;Vint (bit_int ay)] E0 ma (Vint (bit_int a)) ->
 (if a then Clight2.eval_funcall secp_ge ma (Internal f_secp256k1_ge_set_xo_var)
   [Vptr bb Ptrofs.zero;Vptr bbx Ptrofs.zero;Vint (bit_int bybit)] E0 mf (Vint (bit_int b)) else mf=ma) ->
 Clight2.exec_stmt secp_ge e le m point_verify_guards E0 (point_verify_guard_temps le a b) mf Out_normal.
Proof.
 intros EA EB EXA EXB EG AY BY CallA CallB;unfold point_verify_guards;destruct a.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ma) (le1:=PTree.set _t'4 (Vint Int.one) le).
   + eapply exec_point_verify_guard_call with (odd:=ay) (good:=true);[exact EA|exact EXA|exact EG|exact AY|exact CallA].
   + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
     * apply eval_Etempvar;apply PTree.gss.
     * reflexivity.
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
        (le1:=PTree.set _t'6 (Vint (bit_int b)) (PTree.set _t'4 (Vint Int.one) le)).
       -- eapply exec_point_verify_guard_call with (odd:=bybit) (good:=b);[exact EB|exact EXB|exact EG| |exact CallB].
          rewrite PTree.gso by discriminate;exact BY.
       -- apply exec_Sset;eapply eval_Ecast;[apply eval_Etempvar;apply PTree.gss|].
          destruct b;reflexivity.
 - subst mf;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ma) (le1:=PTree.set _t'4 (Vint Int.zero) le).
   + eapply exec_point_verify_guard_call with (odd:=ay) (good:=false);[exact EA|exact EXA|exact EG|exact AY|exact CallA].
   + eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
     * apply eval_Etempvar;apply PTree.gss.
     * reflexivity.
     * apply exec_Sset;constructor.
Qed.
