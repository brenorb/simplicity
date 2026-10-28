(** Exact original linear_verify_1 statements. Call premises in these control
    lemmas are discharged by reader, guard and arithmetic execution proofs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp C.jet_readBit_layout
 C.jet_secp_linear_verify_public_support C.jet_secp_linear_verify_guards
 C.jet_secp_curve_statements C.jet_secp_scalar_add_body C.jet_secp_gej_flag_read.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition linear_verify_address id ty := Eaddrof (Evar id ty) (tptr ty).
Definition linear_verify_ge_read var := curve_call _read_ge f_read_ge None
 [linear_verify_address var (Tstruct __6121 noattr);linear_verify_address _src (Tstruct _frameItem noattr)].
Definition linear_verify_set_ge := curve_call _secp256k1_gej_set_ge f_secp256k1_gej_set_ge None
 [linear_verify_address _a0 (Tstruct __6123 noattr);linear_verify_address _a__1 (Tstruct __6121 noattr)].
Definition linear_verify_negate := curve_call _secp256k1_ge_neg f_secp256k1_ge_neg None
 [linear_verify_address _b (Tstruct __6121 noattr);linear_verify_address _b (Tstruct __6121 noattr)].
Definition linear_verify_multiply := curve_call _secp256k1_ecmult f_secp256k1_ecmult None
 [linear_verify_address _r (Tstruct __6123 noattr);linear_verify_address _a0 (Tstruct __6123 noattr);
  linear_verify_address _na__1 (Tstruct __5826 noattr);linear_verify_address _ng__2 (Tstruct __5826 noattr)].
Definition linear_verify_add := curve_call _secp256k1_gej_add_ge_var f_secp256k1_gej_add_ge_var None
 [linear_verify_address _r (Tstruct __6123 noattr);linear_verify_address _r (Tstruct __6123 noattr);
  linear_verify_address _b (Tstruct __6121 noattr);Ecast (Econst_int Int.zero tint) (tptr tvoid)].
Definition linear_verify_infinity := curve_call _secp256k1_gej_is_infinity f_secp256k1_gej_is_infinity (Some _t'1)
 [linear_verify_address _r (Tstruct __6123 noattr)].
Definition linear_verify_arithmetic_spine := Ssequence linear_verify_set_ge
 (Ssequence linear_verify_negate (Ssequence linear_verify_multiply
  (Ssequence linear_verify_add (Ssequence linear_verify_infinity
   (Sreturn (Some (Etempvar _t'1 tint))))))).
Definition linear_verify_branch := Sifthenelse (Etempvar _t'3 tint)
 linear_verify_arithmetic_spine (Sreturn (Some (Econst_int Int.zero tint))).
Definition linear_verify_rest := Ssequence (scalar_add_read_stmt _na__1)
 (Ssequence (linear_verify_ge_read _a__1) (Ssequence (scalar_add_read_stmt _ng__2)
  (Ssequence (linear_verify_ge_read _b) (Ssequence linear_verify_guards linear_verify_branch)))).
Lemma linear_verify_public_body_source :
 fn_body f_simplicity_linear_verify_1=Ssequence linear_verify_public_copy linear_verify_rest.
Proof. reflexivity. Qed.

Lemma linear_verify_direct_call e le m mf id fd args vargs dest v :
 Genv.find_symbol secp_ge id=Some (secp_symbol_block id) ->
 Genv.find_funct secp_ge (Vptr (secp_symbol_block id) Ptrofs.zero)=Some (Internal fd) -> e!id=None ->
 eval_exprlist secp_ge e le m args (type_of_params (fn_params fd)) vargs ->
 Clight2.eval_funcall secp_ge m (Internal fd) vargs E0 mf v ->
 Clight2.exec_stmt secp_ge e le m (curve_call id fd dest args) E0 (set_opttemp dest v le) mf Out_normal.
Proof.
 intros Symbol Function Global Args Call;unfold curve_call.
 eapply exec_Scall with (vf:=Vptr (secp_symbol_block id) Ptrofs.zero)
  (f:=Internal fd) (vargs:=vargs) (vres:=v).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[exact Global|exact Symbol]|apply deref_loc_reference;reflexivity].
 - exact Args.
 - exact Function.
 - reflexivity.
 - exact Call.
Qed.
Lemma exec_linear_verify_ge_read le m mf bl ba bb bk bg br bz var b :
 (linear_verify_public_env bl ba bb bk bg br bz)!var=Some (b,Tstruct __6121 noattr) ->
 Clight2.eval_funcall secp_ge m (Internal f_read_ge) [Vptr b Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (linear_verify_public_env bl ba bb bk bg br bz) le m
 (linear_verify_ge_read var) E0 le mf Out_normal.
Proof.
 intros Local Call;unfold linear_verify_ge_read.
 eapply linear_verify_direct_call with (dest:=None) (v:=Vundef);[reflexivity|reflexivity|reflexivity| |exact Call].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Local|reflexivity|].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
Qed.
Theorem exec_linear_verify_arithmetic_spine le m ms mn mm mf bl ba bb bk bg br bz bit :
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_set_ge)
  [Vptr bz Ptrofs.zero;Vptr ba Ptrofs.zero] E0 ms Vundef ->
 Clight2.eval_funcall secp_ge ms (Internal f_secp256k1_ge_neg)
  [Vptr bb Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mn Vundef ->
 Clight2.eval_funcall secp_ge mn (Internal f_secp256k1_ecmult)
  [Vptr br Ptrofs.zero;Vptr bz Ptrofs.zero;Vptr bk Ptrofs.zero;Vptr bg Ptrofs.zero] E0 mm Vundef ->
 Clight2.eval_funcall secp_ge mm (Internal f_secp256k1_gej_add_ge_var)
  [Vptr br Ptrofs.zero;Vptr br Ptrofs.zero;Vptr bb Ptrofs.zero;Vlong Int64.zero] E0 mf Vundef ->
 Mem.load Mint32 mf br 120=Some (Vint (bit_int bit)) ->
 Clight2.exec_stmt secp_ge (linear_verify_public_env bl ba bb bk bg br bz) le m
  linear_verify_arithmetic_spine E0 (PTree.set _t'1 (Vint (bit_int bit)) le) mf
  (Out_return (Some (Vint (bit_int bit),tint))).
Proof.
 intros SetCall Neg Mult Add Flag;unfold linear_verify_arithmetic_spine.
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
           (le1:=PTree.set _t'1 (Vint (bit_int bit)) le).
          ++ unfold linear_verify_infinity;eapply linear_verify_direct_call with (dest:=Some _t'1) (v:=Vint (bit_int bit));
              [reflexivity|reflexivity|reflexivity| |].
             ** eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
             ** exact (eval_gej_flag_accessor mf br 0 (bit_int bit) ltac:(lia) ltac:(change (128<=18446744073709551615);lia) Flag).
          ++ apply exec_Sreturn_some;apply eval_Etempvar;apply PTree.gss.
Qed.

Theorem exec_linear_verify_read_spine le lef m m1 m2 m3 mr mf bl ba bb bk bg br bz out :
 Clight2.eval_funcall secp_ge m (Internal f_read_scalar)
  [Vptr bk Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m1 Vundef ->
 Clight2.eval_funcall secp_ge m1 (Internal f_read_ge)
  [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m2 Vundef ->
 Clight2.eval_funcall secp_ge m2 (Internal f_read_scalar)
  [Vptr bg Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m3 Vundef ->
 Clight2.eval_funcall secp_ge m3 (Internal f_read_ge)
  [Vptr bb Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
 Clight2.exec_stmt secp_ge (linear_verify_public_env bl ba bb bk bg br bz) le mr
  (Ssequence linear_verify_guards linear_verify_branch) E0 lef mf out ->
 Clight2.exec_stmt secp_ge (linear_verify_public_env bl ba bb bk bg br bz) le m
  linear_verify_rest E0 lef mf out.
Proof.
 intros ScalarA PointA ScalarG PointB Suffix;unfold linear_verify_rest.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le).
 - eapply exec_scalar_add_read;[reflexivity|reflexivity|reflexivity|exact ScalarA].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le).
   + eapply exec_linear_verify_ge_read;[reflexivity|exact PointA].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m3) (le1:=le).
     * eapply exec_scalar_add_read;[reflexivity|reflexivity|reflexivity|exact ScalarG].
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le).
       -- eapply exec_linear_verify_ge_read;[reflexivity|exact PointB].
       -- exact Suffix.
Qed.
Lemma exec_linear_verify_branch_true le lef m mf bl ba bb bk bg br bz out :
 le!_t'3=Some (Vint Int.one) ->
 Clight2.exec_stmt secp_ge (linear_verify_public_env bl ba bb bk bg br bz) le m
  linear_verify_arithmetic_spine E0 lef mf out ->
 Clight2.exec_stmt secp_ge (linear_verify_public_env bl ba bb bk bg br bz) le m
  linear_verify_branch E0 lef mf out.
Proof.
 intros Temp Body;unfold linear_verify_branch;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
 - apply eval_Etempvar;exact Temp.
 - reflexivity.
 - exact Body.
Qed.
Lemma exec_linear_verify_branch_false le m bl ba bb bk bg br bz :
 le!_t'3=Some (Vint Int.zero) ->
 Clight2.exec_stmt secp_ge (linear_verify_public_env bl ba bb bk bg br bz) le m
  linear_verify_branch E0 le m (Out_return (Some (Vint Int.zero,tint))).
Proof.
 intro Temp;unfold linear_verify_branch;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
 - apply eval_Etempvar;exact Temp.
 - reflexivity.
 - apply exec_Sreturn_some;constructor.
Qed.

Require Import C.jet_secp_frame_preserve C.jet_secp_field_io_preserve C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Lemma linear_verify_point_reader_closed : closed_stmtb field_io_helpers (fn_body f_read_ge)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma linear_verify_point_reader_preserved m args t mf result :
 Clight2.eval_funcall secp_ge m (Internal f_read_ge) args t mf result -> readonly_preserved m mf.
Proof.
 apply function_preserved_from_body;[|reflexivity].
 intros e le mi trace lef mo out Run Plain.
 exact (proj1 (internal_exec_preserved _ _ field_io_helpers_ok)
  e le mi _ trace lef mo out Run Plain linear_verify_point_reader_closed).
Qed.
