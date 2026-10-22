(** Actual skip_ge: two original skip_fe calls, not a substituted skipBits(512). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_mem C.jet_output_layout C.jet_frame_inv C.jet_secp_linkage C.jets_secp C.jet_secp_field_skip.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition affine_skip_fe_stmt := Scall None (Evar _skip_fe (type_of_function f_skip_fe))
 [Etempvar _dst (tptr (Tstruct _frameItem noattr))].
Lemma affine_skip_ge_source : fn_body f_skip_ge=Ssequence affine_skip_fe_stmt affine_skip_fe_stmt.
Proof. reflexivity. Qed.
Lemma affine_skip_fe_link : exists bf, Genv.find_symbol secp_ge _skip_fe=Some bf /\
 Genv.find_funct_ptr secp_ge bf=Some (Internal f_skip_fe).
Proof. exists (secp_symbol_block _skip_fe);split;reflexivity. Qed.
Lemma exec_affine_skip_field le m mf bd base :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 Clight2.eval_funcall secp_ge m (Internal f_skip_fe) [Vptr bd (Ptrofs.repr base)] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge empty_env le m affine_skip_fe_stmt E0 le mf Out_normal.
Proof.
 intros HD Skip;destruct affine_skip_fe_link as (bf & HS & HF).
 unfold affine_skip_fe_stmt;eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
  (vargs:=[Vptr bd (Ptrofs.repr base)]) (f:=Internal f_skip_fe) (vres:=Vundef).
 - reflexivity.
 - eapply eval_Elvalue.
   + eapply eval_Evar_global;[reflexivity|exact HS].
   + apply deref_loc_reference;reflexivity.
 - eapply eval_Econs;[apply eval_Etempvar;exact HD|reflexivity|constructor].
 - exact HF.
 - reflexivity.
 - exact Skip.
Qed.

Theorem eval_secp_skip_ge_from_prefix m0 bd base bw edge cursor N bi written0 outs0 m :
 write_frame_at m0 bd base bw edge cursor N -> Z.of_nat (length outs0)+512<=N ->
 finv m0 bd base bw edge cursor N bi m written0 outs0 -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_skip_ge) [Vptr bd (Ptrofs.repr base)] E0 mf Vundef /\
 finv m0 bd base bw edge cursor N bi mf true (outs0++repeat None 512) /\
 lframe (fun b _=>b<>bd) m mf.
Proof.
 intros Output Cap Inv.
 destruct (eval_secp_skip_fe_from_prefix m0 bd base bw edge cursor N bi written0 outs0 m
  Output ltac:(lia) Inv) as (mi & Skip1 & Inv1 & Frame1).
 destruct (eval_secp_skip_fe_from_prefix m0 bd base bw edge cursor N bi true (outs0++repeat None 256) mi
  Output ltac:(rewrite app_length,repeat_length,Nat2Z.inj_add;lia) Inv1)
  as (mf & Skip2 & Final & Frame2).
 exists mf;split.
 - eapply eval_funcall_internal with (e:=empty_env)
   (le1:=PTree.set _dst (Vptr bd (Ptrofs.repr base)) (PTree.empty val))
   (le2:=PTree.set _dst (Vptr bd (Ptrofs.repr base)) (PTree.empty val))
   (m1:=m) (m2:=mf) (out:=Out_normal).
   + constructor.
     * cbn;repeat constructor;cbn;intuition discriminate.
     * cbn;repeat constructor;cbn;intuition discriminate.
     * intros i j HI HJ HE;cbn in HJ;contradiction.
     * constructor.
     * reflexivity.
   + rewrite affine_skip_ge_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
     * apply exec_affine_skip_field with (bd:=bd) (base:=base);[apply PTree.gss|exact Skip1].
     * apply exec_affine_skip_field with (bd:=bd) (base:=base);[apply PTree.gss|exact Skip2].
   + reflexivity.
   + reflexivity.
 - split.
   + replace (outs0++repeat None 512) with ((outs0++repeat None 256)++repeat None 256)
      by (rewrite <-app_assoc;reflexivity).
     exact Final.
   + eapply lframe_trans;[exact Frame1|exact Frame2].
Qed.
