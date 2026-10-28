(** The original public linear-combination wrapper: five fresh locals, private frame copy,
    exact call spine, and all local frees. Execution premises here are
    discharged by the lifecycle theorem, not public proof assumptions. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Integers Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jets_secp C.jet_secp_linkage C.jet_clight_internal_preserve C.jet_secp_strauss_zero_generator C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem
 C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv C.jet_encoding
 C.jet_secp_frame C.jet_secp_linear_startup C.jet_secp_strauss_complete_program.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Require Import C.jet_readBit_layout C.jet_secp_linear_public_support C.jet_secp_checked_scale_validity
 C.jet_secp_curve_statements C.jet_secp_scalar_add_body C.jet_secp_fns.
Definition checked_linear_temps v_env bd base bs sbase :=
 PTree.set _env v_env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
 (PTree.set _dst (Vptr bd (Ptrofs.repr base))
 (create_undef_temps (fn_temps f_simplicity_linear_combination_1)))).
Lemma checked_linear_entry_ok : fn_okb f_simplicity_linear_combination_1=true.
Proof. reflexivity. Qed.
Lemma checked_linear_entry_transport v_env m bd base bs sbase mi bl br ba bk bg :
 function_entry2 secp_ge f_simplicity_off_curve_linear_combination_1
 [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m
 (linear_public_env bl br ba bk bg) (linear_public_temps v_env bd base bs sbase) mi ->
 function_entry2 secp_ge f_simplicity_linear_combination_1
 [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m
 (linear_public_env bl br ba bk bg) (checked_linear_temps v_env bd base bs sbase) mi.
Proof.
 intro Entry;inversion Entry as [Vars Params Apart Alloc Bind].
 destruct (fn_okb_true _ checked_linear_entry_ok) as (VarsC & ParamsC & ApartC).
 constructor;[exact VarsC|exact ParamsC|exact ApartC|exact Alloc|reflexivity].
Qed.
Lemma checked_variable_temps e le le' m id ty loc ofs bf :
 eval_lvalue secp_ge e le m (Evar id ty) loc ofs bf ->
 eval_lvalue secp_ge e le' m (Evar id ty) loc ofs bf.
Proof. intro Var;inversion Var;subst;eauto using eval_Evar_local,eval_Evar_global. Qed.
Lemma checked_temp_value e le m id ty v :
 eval_expr secp_ge e le m (Etempvar id ty) v -> le!id=Some v.
Proof.
 intro Temp;inversion Temp;subst;try assumption.
 match goal with LV:eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _=>inversion LV end.
Qed.
Lemma checked_linear_copy_transport le le' mi md bl br ba bk bg :
 le'!_src=le!_src ->
 Clight2.exec_stmt secp_ge (linear_public_env bl br ba bk bg) le mi linear_public_copy E0 le md Out_normal ->
 Clight2.exec_stmt secp_ge (linear_public_env bl br ba bk bg) le' mi linear_public_copy E0 le' md Out_normal.
Proof.
 intros Source Copy;unfold linear_public_copy in *;inversion Copy;subst.
 eapply exec_Sassign.
 - eapply checked_variable_temps;exact H1.
 - apply eval_Etempvar;rewrite Source;eapply checked_temp_value;exact H2.
 - exact H6.
 - exact H7.
Qed.

Theorem checked_linear_public_prepare v_env m0 bd base bs sbase bw edge cursor N bi inedge rc :
 linear_startup m0 -> write_frame_at m0 bd base bw edge cursor N ->
 frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi inedge rc ->
 exists mi md bl br ba bk bg,
 function_entry2 secp_ge f_simplicity_linear_combination_1
  [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m0
  (linear_public_env bl br ba bk bg) (checked_linear_temps v_env bd base bs sbase) mi /\
 Clight2.exec_stmt secp_ge (linear_public_env bl br ba bk bg) (checked_linear_temps v_env bd base bs sbase)
  mi linear_public_copy E0 (checked_linear_temps v_env bd base bs sbase) md Out_normal /\
 (forall b hi,In (b,hi) (linear_public_storage bl br ba bk bg) -> Mem.range_perm md b 0 hi Cur Freeable) /\
 frame_fields_at md bl 0 bi inedge rc /\
 NoDup (linear_public_locals bl br ba bk bg) /\
 (forall b,Mem.valid_block m0 b -> ~In b (linear_public_locals bl br ba bk bg)) /\
 xsep (extA m0 bd bw bi) [(br,0);(ba,0);(bk,0);(bl,0);(bg,0)] /\
 finv m0 bd base bw edge cursor N bi md false [] /\ linear_startup md /\
 lframe (fun b _=>~In b (linear_public_locals bl br ba bk bg)) m0 md.
Proof.
 intros Ready Output Base Align Source.
 destruct (linear_public_prepare v_env m0 bd base bs sbase bw edge cursor N bi inedge rc
  Ready Output Base Align Source)
  as (mi & md & bl & br & ba & bk & bg & Entry & Copy & Owned & Fields & Separate & Old & Sep & Fin & ReadyF & Frame).
 exists mi,md,bl,br,ba,bk,bg;split.
 - eapply checked_linear_entry_transport;exact Entry.
 - split.
   + eapply checked_linear_copy_transport with (le:=linear_public_temps v_env bd base bs sbase);[reflexivity|exact Copy].
   + split;[exact Owned|];split;[exact Fields|];split;[exact Separate|];split;[exact Old|];
     split;[exact Sep|];split;[exact Fin|];split;assumption.
Qed.

Definition checked_linear_curve_stmt := Scall (Some _t'1)
 (Evar _simplicity_gej_is_valid_var (Tfunction (Tcons (tptr (Tstruct __6123 noattr)) Tnil) tbool cc_default))
 [Eaddrof (Evar _a__1 (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr))].
Lemma exec_checked_linear_curve le m mf bl br ba bk bg bit :
 Clight2.eval_funcall secp_ge m (Internal f_simplicity_gej_is_valid_var) [Vptr ba Ptrofs.zero]
 E0 mf (Vint (bit_int bit)) ->
 Clight2.exec_stmt secp_ge (linear_public_env bl br ba bk bg) le m checked_linear_curve_stmt E0
 (PTree.set _t'1 (Vint (bit_int bit)) le) mf Out_normal.
Proof.
 intro Call;destruct C.jet_secp_checked_scale_validity.checked_curve_symbol as (b & Symbol & Function).
 unfold checked_linear_curve_stmt.
 eapply exec_Scall with (vf:=Vptr b Ptrofs.zero) (vargs:=[Vptr ba Ptrofs.zero])
  (f:=Internal f_simplicity_gej_is_valid_var) (vres:=Vint (bit_int bit)).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact Symbol]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
 - exact Function.
 - reflexivity.
 - exact Call.
Qed.

Definition checked_linear_branch := Sifthenelse (Etempvar _t'1 tbool)
 (Ssequence linear_multiply
  (Ssequence linear_write (Sreturn (Some (Econst_int Int.one tint)))))
 (Sreturn (Some (Econst_int Int.zero tint))).
Definition checked_linear_rest := Ssequence (scalar_add_read_stmt _na__1)
 (Ssequence linear_point_read (Ssequence (scalar_add_read_stmt _ng__2)
  (Ssequence checked_linear_curve_stmt checked_linear_branch))).
Lemma checked_linear_body_source :
 fn_body f_simplicity_linear_combination_1=Ssequence linear_public_copy checked_linear_rest.
Proof. reflexivity. Qed.
Lemma exec_checked_linear_rest_true le md mr mq mp mv mn mw bd base bl br ba bk bg :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 Clight2.eval_funcall secp_ge md (Internal f_read_scalar)
  [Vptr bk Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
 Clight2.eval_funcall secp_ge mr (Internal f_read_gej)
  [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mq Vundef ->
 Clight2.eval_funcall secp_ge mq (Internal f_read_scalar)
  [Vptr bg Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mp Vundef ->
 Clight2.eval_funcall secp_ge mp (Internal f_simplicity_gej_is_valid_var)
  [Vptr ba Ptrofs.zero] E0 mv (Vint Int.one) ->
 Clight2.eval_funcall secp_ge mv (Internal f_secp256k1_ecmult)
  [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bk Ptrofs.zero;Vptr bg Ptrofs.zero] E0 mn Vundef ->
 Clight2.eval_funcall secp_ge mn (Internal f_write_gej)
  [Vptr bd (Ptrofs.repr base);Vptr br Ptrofs.zero] E0 mw Vundef ->
 Clight2.exec_stmt secp_ge (linear_public_env bl br ba bk bg) le md checked_linear_rest E0
  (PTree.set _t'1 (Vint Int.one) le) mw (Out_return (Some (Vint Int.one,tint))).
Proof.
 intros Dst Scalar Point Generator Valid Mult Write;unfold checked_linear_rest.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le).
 - eapply exec_scalar_add_read;[reflexivity|reflexivity|reflexivity|exact Scalar].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mq) (le1:=le);[eapply exec_linear_point_read;exact Point|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mp) (le1:=le).
   + eapply exec_scalar_add_read;[reflexivity|reflexivity|reflexivity|exact Generator].
   + { eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mv) (le1:=PTree.set _t'1 (Vint Int.one) le).
   + exact (exec_checked_linear_curve le mp mv bl br ba bk bg true Valid).
   + unfold checked_linear_branch;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
     * apply eval_Etempvar;apply PTree.gss.
     * reflexivity.
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn) (le1:=PTree.set _t'1 (Vint Int.one) le);
        [eapply exec_linear_multiply;exact Mult|].
       eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mw) (le1:=PTree.set _t'1 (Vint Int.one) le).
       -- eapply exec_linear_write;[rewrite PTree.gso by discriminate;exact Dst|exact Write].
       -- apply exec_Sreturn_some;constructor.
   }
Qed.
Lemma exec_checked_linear_rest_false le md mr mq mp mv bl br ba bk bg :
 Clight2.eval_funcall secp_ge md (Internal f_read_scalar)
  [Vptr bk Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
 Clight2.eval_funcall secp_ge mr (Internal f_read_gej)
  [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mq Vundef ->
 Clight2.eval_funcall secp_ge mq (Internal f_read_scalar)
  [Vptr bg Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mp Vundef ->
 Clight2.eval_funcall secp_ge mp (Internal f_simplicity_gej_is_valid_var)
  [Vptr ba Ptrofs.zero] E0 mv (Vint Int.zero) ->
 Clight2.exec_stmt secp_ge (linear_public_env bl br ba bk bg) le md checked_linear_rest E0
  (PTree.set _t'1 (Vint Int.zero) le) mv (Out_return (Some (Vint Int.zero,tint))).
Proof.
 intros Scalar Point Generator Valid;unfold checked_linear_rest.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le).
 - eapply exec_scalar_add_read;[reflexivity|reflexivity|reflexivity|exact Scalar].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mq) (le1:=le);[eapply exec_linear_point_read;exact Point|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mp) (le1:=le).
   + eapply exec_scalar_add_read;[reflexivity|reflexivity|reflexivity|exact Generator].
   + { eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mv) (le1:=PTree.set _t'1 (Vint Int.zero) le).
   + exact (exec_checked_linear_curve le mp mv bl br ba bk bg false Valid).
   + unfold checked_linear_branch;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
     * apply eval_Etempvar;apply PTree.gss.
     * reflexivity.
     * apply exec_Sreturn_some;constructor.
   }
Qed.
