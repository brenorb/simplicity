(** Exact original point-verifier statement tree and arithmetic control. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp C.jet_readBit_layout
 C.jet_secp_point_verify_public_support C.jet_secp_point_verify_guards
 C.jet_secp_curve_statements C.jet_secp_scalar_add_body C.jet_secp_gej_flag_read
 C.jet_secp_linear_verify_public_body.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition point_verify_bit_read parity dest := Ssequence
 (curve_call _readBit f_readBit (Some dest)
  [linear_verify_address _src (Tstruct _frameItem noattr)])
 (Sset parity (Ecast (Etempvar dest tbool) tbool)).
Definition point_verify_fe_read var := curve_call _read_fe f_read_fe None
 [linear_verify_address var (Tstruct __5467 noattr);linear_verify_address _src (Tstruct _frameItem noattr)].
Definition point_verify_infinity := curve_call _secp256k1_gej_is_infinity f_secp256k1_gej_is_infinity (Some _t'3)
 [linear_verify_address _r (Tstruct __6123 noattr)].
Definition point_verify_arithmetic_spine := Ssequence linear_verify_set_ge
 (Ssequence linear_verify_negate (Ssequence linear_verify_multiply
  (Ssequence linear_verify_add (Ssequence point_verify_infinity
   (Sreturn (Some (Etempvar _t'3 tint))))))).
Definition point_verify_branch := Sifthenelse (Etempvar _t'5 tint)
 point_verify_arithmetic_spine (Sreturn (Some (Econst_int Int.zero tint))).
Definition point_verify_rest := Ssequence (scalar_add_read_stmt _na__1)
 (Ssequence (point_verify_bit_read _ay _t'1)
  (Ssequence (point_verify_fe_read _ax)
   (Ssequence (scalar_add_read_stmt _ng__2)
    (Ssequence (point_verify_bit_read _by _t'2)
     (Ssequence (point_verify_fe_read _bx) (Ssequence point_verify_guards point_verify_branch)))))).
Lemma point_verify_public_body_source :
 fn_body f_simplicity_point_verify_1=Ssequence point_verify_public_copy point_verify_rest.
Proof. reflexivity. Qed.

Theorem exec_point_verify_arithmetic_spine le m ms mn mm mf bl bax bbx ba bb bk bg br bz bit :
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_set_ge)
  [Vptr bz Ptrofs.zero;Vptr ba Ptrofs.zero] E0 ms Vundef ->
 Clight2.eval_funcall secp_ge ms (Internal f_secp256k1_ge_neg)
  [Vptr bb Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mn Vundef ->
 Clight2.eval_funcall secp_ge mn (Internal f_secp256k1_ecmult)
  [Vptr br Ptrofs.zero;Vptr bz Ptrofs.zero;Vptr bk Ptrofs.zero;Vptr bg Ptrofs.zero] E0 mm Vundef ->
 Clight2.eval_funcall secp_ge mm (Internal f_secp256k1_gej_add_ge_var)
  [Vptr br Ptrofs.zero;Vptr br Ptrofs.zero;Vptr bb Ptrofs.zero;Vlong Int64.zero] E0 mf Vundef ->
 Mem.load Mint32 mf br 120=Some (Vint (bit_int bit)) ->
 Clight2.exec_stmt secp_ge (point_verify_public_env bl bax bbx ba bb bk bg br bz) le m
  point_verify_arithmetic_spine E0 (PTree.set _t'3 (Vint (bit_int bit)) le) mf
  (Out_return (Some (Vint (bit_int bit),tint))).
Proof.
 intros SetCall Neg Mult Add Flag;unfold point_verify_arithmetic_spine.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ms) (le1:=le).
 - unfold linear_verify_set_ge;eapply linear_verify_direct_call with (dest:=None) (v:=Vundef);
    [reflexivity|reflexivity|reflexivity| |exact SetCall].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn) (le1:=le).
   + unfold linear_verify_negate;eapply linear_verify_direct_call with (dest:=None) (v:=Vundef);
      [reflexivity|reflexivity|reflexivity| |exact Neg].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mm) (le1:=le).
     * unfold linear_verify_multiply;eapply linear_verify_direct_call with (dest:=None) (v:=Vundef);
        [reflexivity|reflexivity|reflexivity| |exact Mult].
       eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
       eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
       eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
       eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
       -- unfold linear_verify_add;eapply linear_verify_direct_call with (dest:=None) (v:=Vundef);
           [reflexivity|reflexivity|reflexivity| |exact Add].
          eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
          eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
          eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
          eapply eval_Econs;[eapply eval_Ecast;[constructor|reflexivity]|reflexivity|constructor].
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
           (le1:=PTree.set _t'3 (Vint (bit_int bit)) le).
          ++ unfold point_verify_infinity;eapply linear_verify_direct_call with (dest:=Some _t'3) (v:=Vint (bit_int bit));
              [reflexivity|reflexivity|reflexivity| |].
             ** eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
             ** exact (eval_gej_flag_accessor mf br 0 (bit_int bit) ltac:(lia) ltac:(change (128<=18446744073709551615);lia) Flag).
          ++ apply exec_Sreturn_some;apply eval_Etempvar;apply PTree.gss.
Qed.

