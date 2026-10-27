(** Complete original lambda-table lookup with distinct coordinate sources. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_ge_set_xy_sources C.jet_secp_table_get_control C.jet_secp_table_get_lambda_control
 C.jet_secp_table_get_negate C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_field_negate_separate C.jet_secp_multiply_normalize_bridge
 C.jet_clight_internal_frame C.jet_clight_internal_permissions C.jet_clight_internal_preserve
 C.jet_secp_closed_helpers C.jet_secp_slice_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma table_get_lambda_closed :
 closed_stmtb secp_closed_helpers (fn_body f_secp256k1_ecmult_table_get_ge_lambda)=true.
Proof. reflexivity. Qed.

Theorem eval_table_get_ge_lambda negative j m bd bt bx x y : 0<=j<8 -> bd<>bt -> bd<>bx ->
 Mem.range_perm m bt 0 704 Cur Freeable -> Mem.range_perm m bx 0 320 Cur Freeable ->
 Mem.range_perm m bd 0 88 Cur Freeable ->
 fe_at m bx (40*j) (words5 x) -> fe_at m bt (88*j+40) (words5 y) -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_table_get_ge_lambda)
 [Vptr bd Ptrofs.zero;Vptr bt Ptrofs.zero;Vptr bx Ptrofs.zero;
  Vint (Int.repr (table_get_digit negative j));Vint (Int.repr 5)] E0 mf Vundef /\
 fe_at mf bd 0 (words5 x) /\ fe_at mf bd 40 (words5 (if negative then negate_sep_words y else y)) /\
 Mem.load Mint32 mf bd 80=Some (Vint Int.zero) /\
 Mem.range_perm mf bd 0 88 Cur Freeable /\ Mem.range_perm mf bt 0 704 Cur Freeable /\
 Mem.range_perm mf bx 0 320 Cur Freeable /\ keeps_permissions m mf /\
 lframe (fun b _=>b<>bd) m mf /\ readonly_preserved m mf.
Proof.
 intros Range SeparateT SeparateX FreeT FreeX FreeD X Y.
 set (le:=table_get_lambda_temps bd bt bx negative j).
 assert (R:le!_r=Some (Vptr bd Ptrofs.zero)) by reflexivity.
 assert (Pre:le!_pre=Some (Vptr bt Ptrofs.zero)) by reflexivity.
 assert (AX:le!_x=Some (Vptr bx Ptrofs.zero)) by reflexivity.
 assert (N:le!_n=Some (Vint (Int.repr (table_get_digit negative j)))) by reflexivity.
 destruct (eval_ge_set_xy_sources x y m bd bx (40*j) bt (88*j+40) SeparateX SeparateT X Y FreeD)
  as (mc & ConstructCall & XC & YC & FlagC & FreeC & PermC & FrameC & ReadonlyC).
 assert (Construct:Clight2.exec_stmt secp_ge empty_env le m (table_get_lambda_construct negative) E0 le mc Out_normal).
 { unfold table_get_lambda_construct;eapply exec_curve_call with
   (vargs:=[Vptr bd Ptrofs.zero;Vptr bx (Ptrofs.repr (40*j));Vptr bt (Ptrofs.repr (88*j+40))]) (v:=Vundef).
   - unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
   - reflexivity.
   - eapply eval_Econs with (v1:=Vptr bd Ptrofs.zero);[apply eval_Etempvar;exact R|reflexivity|].
     eapply eval_Econs with (v1:=Vptr bx (Ptrofs.repr (40*j)));
      [exact (eval_table_get_lambda_x empty_env le m bx negative j Range AX N)|reflexivity|].
     eapply eval_Econs with (v1:=Vptr bt (Ptrofs.repr (88*j+40)));
      [exact (eval_table_get_lambda_y empty_env le m bt negative j Range Pre N)|reflexivity|constructor].
   - exact ConstructCall. }
 assert (Branch:exists mf,
  Clight2.exec_stmt secp_ge empty_env le m table_get_lambda_choice E0 le mf Out_normal /\
  fe_at mf bd 0 (words5 x) /\ fe_at mf bd 40 (words5 (if negative then negate_sep_words y else y)) /\
  Mem.load Mint32 mf bd 80=Some (Vint Int.zero) /\ Mem.range_perm mf bd 0 88 Cur Freeable /\
  lframe (fun b _=>b<>bd) m mf).
 { destruct negative.
   - destruct (exec_table_get_negate le mc bd y R YC FreeC) as (mf & Negate & YF & FreeF & FrameN).
     assert (XF:fe_at mf bd 0 (words5 x)).
     { eapply curve_keep_field_range;[reflexivity|exact XC|exact FrameN|].
       intros pos Pos;right;left;lia. }
     assert (FlagF:Mem.load Mint32 mf bd 80=Some (Vint Int.zero)).
     { rewrite (proj1 FrameN Mint32 bd 80);[exact FlagC| |intros pos Pos;right;right;change (80<=pos<80+4) in Pos;lia].
       eapply Mem.perm_valid_block;apply (FreeC 0);lia. }
     exists mf;split.
     + unfold table_get_lambda_choice;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);
       [exact (eval_table_get_guard empty_env le m true j Range N)|reflexivity|].
       eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Construct|exact Negate].
     + split;[exact XF|];split;[exact YF|];split;[exact FlagF|];split;[exact FreeF|].
       eapply lframe_trans;[exact FrameC|].
       eapply lframe_implies;[exact FrameN|intros b pos Different _;left;exact Different].
   - exists mc;split.
     + unfold table_get_lambda_choice;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);
       [exact (eval_table_get_guard empty_env le m false j Range N)|reflexivity|exact Construct].
     + split;[exact XC|];split;[exact YC|];split;[exact FlagC|];split;assumption. }
 destruct Branch as (mf & Choice & XF & YF & FlagF & FreeF & FrameF).
 assert (Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_table_get_ge_lambda)
  [Vptr bd Ptrofs.zero;Vptr bt Ptrofs.zero;Vptr bx Ptrofs.zero;
   Vint (Int.repr (table_get_digit negative j));Vint (Int.repr 5)] E0 mf Vundef).
 { eapply eval_funcall_internal with (e:=empty_env) (le1:=le) (le2:=le) (m1:=m) (m2:=mf) (out:=Out_normal).
   - apply table_get_lambda_entry.
   - rewrite table_get_lambda_body_source.
     do 3 (eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m);
      [eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (out1:=Out_normal) (out2:=Out_break);constructor|]).
     exact Choice.
   - reflexivity.
   - reflexivity. }
 assert (Keep:keeps_permissions m mf) by
  (eapply secp_internal_keeps_permissions;[exact table_get_lambda_closed|reflexivity|exact Call]).
 exists mf;split;[exact Call|];split;[exact XF|];split;[exact YF|];split;[exact FlagF|];split;[exact FreeF|];split.
 - intros pos Pos;apply Keep,FreeT;exact Pos.
 - split;[intros pos Pos;apply Keep,FreeX;exact Pos|];split;[exact Keep|];split;[exact FrameF|].
   eapply secp_closed_function_preserved;[exact table_get_lambda_closed|reflexivity|exact Call].
Qed.
