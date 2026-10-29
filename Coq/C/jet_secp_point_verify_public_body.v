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


Definition point_verify_parity_temps le parity dest (bit:bool) :=
 PTree.set parity (Vint (bit_int bit)) (PTree.set dest (Vint (bit_int bit)) le).
Definition point_verify_read_temps le (a b:bool) :=
 point_verify_parity_temps (point_verify_parity_temps le _ay _t'1 a) _by _t'2 b.
Lemma point_verify_read_parities le a b :
 (point_verify_read_temps le a b)!_ay=Some (Vint (bit_int a)) /\
 (point_verify_read_temps le a b)!_by=Some (Vint (bit_int b)).
Proof.
 unfold point_verify_read_temps,point_verify_parity_temps;split;[|apply PTree.gss].
 rewrite !PTree.gso by discriminate;apply PTree.gss.
Qed.
Lemma exec_point_verify_bit_read e le m mf parity dest bl bit :
 e!_src=Some (bl,Tstruct _frameItem noattr) -> e!_readBit=None ->
 Clight2.eval_funcall secp_ge m (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mf (Vint (bit_int bit)) ->
 Clight2.exec_stmt secp_ge e le m (point_verify_bit_read parity dest) E0
  (point_verify_parity_temps le parity dest bit) mf Out_normal.
Proof.
 intros Local Global Call;unfold point_verify_bit_read,point_verify_parity_temps.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set dest (Vint (bit_int bit)) le).
 - eapply linear_verify_direct_call with (dest:=Some dest) (v:=Vint (bit_int bit));
   [reflexivity|reflexivity|exact Global| |exact Call].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Local|reflexivity|constructor].
 - apply exec_Sset;eapply eval_Ecast;[apply eval_Etempvar;apply PTree.gss|].
   destruct bit;reflexivity.
Qed.
Lemma exec_point_verify_fe_read e le m mf var bx bl :
 e!var=Some (bx,Tstruct __5467 noattr) -> e!_src=Some (bl,Tstruct _frameItem noattr) -> e!_read_fe=None ->
 Clight2.eval_funcall secp_ge m (Internal f_read_fe) [Vptr bx Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m (point_verify_fe_read var) E0 le mf Out_normal.
Proof.
 intros Local Source Global Call;unfold point_verify_fe_read.
 eapply linear_verify_direct_call with (dest:=None) (v:=Vundef);[reflexivity|reflexivity|exact Global| |exact Call].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Local|reflexivity|].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Source|reflexivity|constructor].
Qed.

Theorem exec_point_verify_read_spine le lef m m1 m2 m3 m4 m5 mr mf bl bax bbx ba bb bk bg br bz a b out :
 Clight2.eval_funcall secp_ge m (Internal f_read_scalar) [Vptr bk Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m1 Vundef ->
 Clight2.eval_funcall secp_ge m1 (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 m2 (Vint (bit_int a)) ->
 Clight2.eval_funcall secp_ge m2 (Internal f_read_fe) [Vptr bax Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m3 Vundef ->
 Clight2.eval_funcall secp_ge m3 (Internal f_read_scalar) [Vptr bg Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m4 Vundef ->
 Clight2.eval_funcall secp_ge m4 (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 m5 (Vint (bit_int b)) ->
 Clight2.eval_funcall secp_ge m5 (Internal f_read_fe) [Vptr bbx Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
 Clight2.exec_stmt secp_ge (point_verify_public_env bl bax bbx ba bb bk bg br bz) (point_verify_read_temps le a b) mr
  (Ssequence point_verify_guards point_verify_branch) E0 lef mf out ->
 Clight2.exec_stmt secp_ge (point_verify_public_env bl bax bbx ba bb bk bg br bz) le m point_verify_rest E0 lef mf out.
Proof.
 intros ScalarA BitA FieldA ScalarG BitB FieldB Suffix;unfold point_verify_rest.
 pose (leA:=point_verify_parity_temps le _ay _t'1 a).
 pose (leB:=point_verify_read_temps le a b).
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le).
 - eapply exec_scalar_add_read;[reflexivity|reflexivity|reflexivity|exact ScalarA].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=leA).
   + eapply exec_point_verify_bit_read;[reflexivity|reflexivity|exact BitA].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m3) (le1:=leA).
     * eapply exec_point_verify_fe_read;[reflexivity|reflexivity|reflexivity|exact FieldA].
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m4) (le1:=leA).
       -- eapply exec_scalar_add_read;[reflexivity|reflexivity|reflexivity|exact ScalarG].
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m5) (le1:=leB).
          ++ eapply exec_point_verify_bit_read;[reflexivity|reflexivity|exact BitB].
          ++ eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=leB).
             ** eapply exec_point_verify_fe_read;[reflexivity|reflexivity|reflexivity|exact FieldB].
             ** exact Suffix.
Qed.
Lemma exec_point_verify_branch_true le lef m mf bl bax bbx ba bb bk bg br bz out :
 le!_t'5=Some (Vint Int.one) ->
 Clight2.exec_stmt secp_ge (point_verify_public_env bl bax bbx ba bb bk bg br bz) le m
  point_verify_arithmetic_spine E0 lef mf out ->
 Clight2.exec_stmt secp_ge (point_verify_public_env bl bax bbx ba bb bk bg br bz) le m point_verify_branch E0 lef mf out.
Proof.
 intros Temp Body;unfold point_verify_branch;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
 - apply eval_Etempvar;exact Temp.
 - reflexivity.
 - exact Body.
Qed.
Lemma exec_point_verify_branch_false le m bl bax bbx ba bb bk bg br bz :
 le!_t'5=Some (Vint Int.zero) ->
 Clight2.exec_stmt secp_ge (point_verify_public_env bl bax bbx ba bb bk bg br bz) le m point_verify_branch E0 le m
  (Out_return (Some (Vint Int.zero,tint))).
Proof.
 intro Temp;unfold point_verify_branch;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
 - apply eval_Etempvar;exact Temp.
 - reflexivity.
 - apply exec_Sreturn_some;constructor.
Qed.
