(** The actual A-then-B short circuit in linear_verify_1. The B guard is
    executed only when A is valid; all point readback comes from real calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_sx_mem C.jet_readBit_layout C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_point_three_reads
 C.jet_secp_curve_literal C.jet_secp_affine_validity_readback C.jet_secp_curve_statements
 C.jet_secp_linear_verify_public_support C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_ge_is_on_curve.

Definition linear_verify_guard_call var dest :=
 curve_call _secp256k1_ge_is_valid_var f_secp256k1_ge_is_valid_var (Some dest)
 [Eaddrof (Evar var (Tstruct __6121 noattr)) (tptr (Tstruct __6121 noattr))].
Definition linear_verify_guards := Ssequence (linear_verify_guard_call _a__1 _t'2)
 (Sifthenelse (Etempvar _t'2 tint)
  (Ssequence (linear_verify_guard_call _b _t'4)
    (Sset _t'3 (Ecast (Etempvar _t'4 tint) tbool)))
  (Sset _t'3 (Econst_int Int.zero tint))).
Definition linear_verify_guard_temps le (a b:bool) :=
 if a then PTree.set _t'3 (Vint (bit_int b))
  (PTree.set _t'4 (Vint (bit_int b)) (PTree.set _t'2 (Vint Int.one) le))
 else PTree.set _t'3 (Vint Int.zero) (PTree.set _t'2 (Vint Int.zero) le).
Lemma linear_verify_guard_symbol :
 Genv.find_symbol secp_ge _secp256k1_ge_is_valid_var=
  Some (secp_symbol_block _secp256k1_ge_is_valid_var) /\
 Genv.find_funct secp_ge (Vptr (secp_symbol_block _secp256k1_ge_is_valid_var) Ptrofs.zero)=
  Some (Internal f_secp256k1_ge_is_valid_var).
Proof. split;reflexivity. Qed.
Lemma exec_linear_verify_guard_call e le m mf var dest b bit :
 e!var=Some (b,Tstruct __6121 noattr) -> e!_secp256k1_ge_is_valid_var=None ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_is_valid_var)
  [Vptr b Ptrofs.zero] E0 mf (Vint (bit_int bit)) ->
 Clight2.exec_stmt secp_ge e le m (linear_verify_guard_call var dest) E0
  (PTree.set dest (Vint (bit_int bit)) le) mf Out_normal.
Proof.
 intros Local Global Call;unfold linear_verify_guard_call,curve_call.
 destruct linear_verify_guard_symbol as [Symbol Function].
 eapply exec_Scall with (vf:=Vptr (secp_symbol_block _secp256k1_ge_is_valid_var) Ptrofs.zero)
  (f:=Internal f_secp256k1_ge_is_valid_var) (vargs:=[Vptr b Ptrofs.zero]) (vres:=Vint (bit_int bit)).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[exact Global|exact Symbol]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Local|reflexivity|constructor].
 - exact Function.
 - reflexivity.
 - exact Call.
Qed.
Lemma linear_verify_guard_result le a b :
 (linear_verify_guard_temps le a b)!_t'3=Some (Vint (bit_int (andb a b))).
Proof. destruct a;apply PTree.gss. Qed.

Theorem exec_linear_verify_guards le m ma mf bl ba bb bk bg br bz a b :
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_is_valid_var)
  [Vptr ba Ptrofs.zero] E0 ma (Vint (bit_int a)) ->
 (if a then Clight2.eval_funcall secp_ge ma (Internal f_secp256k1_ge_is_valid_var)
   [Vptr bb Ptrofs.zero] E0 mf (Vint (bit_int b)) else mf=ma) ->
 Clight2.exec_stmt secp_ge (linear_verify_public_env bl ba bb bk bg br bz) le m
  linear_verify_guards E0 (linear_verify_guard_temps le a b) mf Out_normal.
Proof.
 intros CallA CallB;unfold linear_verify_guards;destruct a.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ma) (le1:=PTree.set _t'2 (Vint Int.one) le).
   + eapply exec_linear_verify_guard_call with (bit:=true);[reflexivity|reflexivity|exact CallA].
   + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
     * apply eval_Etempvar;apply PTree.gss.
     * reflexivity.
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
        (le1:=PTree.set _t'4 (Vint (bit_int b)) (PTree.set _t'2 (Vint Int.one) le)).
       -- eapply exec_linear_verify_guard_call with (bit:=b);[reflexivity|reflexivity|exact CallB].
       -- apply exec_Sset;eapply eval_Ecast;[apply eval_Etempvar;apply PTree.gss|].
          destruct b;reflexivity.
 - subst mf;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ma) (le1:=PTree.set _t'2 (Vint Int.zero) le).
   + eapply exec_linear_verify_guard_call with (bit:=false);[reflexivity|reflexivity|exact CallA].
   + eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
     * apply eval_Etempvar;apply PTree.gss.
     * reflexivity.
     * apply exec_Sset;constructor.
Qed.

Theorem eval_linear_verify_guards le m bl ba bb bk bg br bz ax ay bxword byword :
 ba<>bb ->
 fe_at m ba 0 (point_canonical_limbs ax) -> fe_at m ba 40 (point_canonical_limbs ay) ->
 Mem.load Mint32 m ba 80=Some (Vint Int.zero) -> Mem.range_perm m ba 0 88 Cur Freeable ->
 fe_at m bb 0 (point_canonical_limbs bxword) -> fe_at m bb 40 (point_canonical_limbs byword) ->
 Mem.load Mint32 m bb 80=Some (Vint Int.zero) -> Mem.range_perm m bb 0 88 Cur Freeable ->
 exists mf,
 Clight2.exec_stmt secp_ge (linear_verify_public_env bl ba bb bk bg br bz) le m
  linear_verify_guards E0
  (linear_verify_guard_temps le (Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay)))
   (Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (bxword,byword)))) mf Out_normal /\
 fe_at mf ba 0 (point_canonical_limbs ax) /\ fe_at mf ba 40 (point_canonical_limbs ay) /\
 Mem.load Mint32 mf ba 80=Some (Vint Int.zero) /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 fe_at mf bb 0 (point_canonical_limbs bxword) /\ fe_at mf bb 40 (point_canonical_limbs byword) /\
 Mem.load Mint32 mf bb 80=Some (Vint Int.zero) /\ Mem.range_perm mf bb 0 88 Cur Freeable /\
 lframe (fun b _=>b<>ba /\ b<>bb) m mf /\ readonly_preserved m mf.
Proof.
 intros Separate XA YA FlagA FA XB YB FlagB FB.
 destruct (eval_affine_validity_literal_readback ax ay m ba XA YA FA FlagA)
  as (ma & CallA & XAA & YAA & FlagAA & FAA & FrameA & ReadA).
 assert (XBA:fe_at ma bb 0 (point_canonical_limbs bxword))
  by (eapply field_at_lframe;[exact XB|exact FrameA|intros;congruence]).
 assert (YBA:fe_at ma bb 40 (point_canonical_limbs byword))
  by (eapply field_at_lframe;[exact YB|exact FrameA|intros;congruence]).
 assert (FBA:Mem.range_perm ma bb 0 88 Cur Freeable)
  by (eapply curve_keep_free;[clear;lia|exact FB|exact FrameA|intros;congruence]).
 assert (ValidB:Mem.valid_block m bb) by (eapply Mem.perm_valid_block;apply (FB 0);lia).
 assert (FlagBA:Mem.load Mint32 ma bb 80=Some (Vint Int.zero)).
 { rewrite (proj1 FrameA Mint32 bb 80 ValidB ltac:(intros;congruence));exact FlagB. }
 destruct (Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))) eqn:GuardA.
 - destruct (eval_affine_validity_literal_readback bxword byword ma bb XBA YBA FBA FlagBA)
    as (mf & CallB & XBF & YBF & FlagBF & FBF & FrameB & ReadB).
   assert (XAF:fe_at mf ba 0 (point_canonical_limbs ax))
    by (eapply field_at_lframe;[exact XAA|exact FrameB|intros;exact Separate]).
   assert (YAF:fe_at mf ba 40 (point_canonical_limbs ay))
    by (eapply field_at_lframe;[exact YAA|exact FrameB|intros;exact Separate]).
   assert (FAF:Mem.range_perm mf ba 0 88 Cur Freeable)
    by (eapply curve_keep_free;[clear;lia|exact FAA|exact FrameB|intros;exact Separate]).
   assert (ValidA:Mem.valid_block ma ba) by (eapply Mem.perm_valid_block;apply (FAA 0);lia).
   assert (FlagAF:Mem.load Mint32 mf ba 80=Some (Vint Int.zero)).
   { rewrite (proj1 FrameB Mint32 ba 80 ValidA ltac:(intros;exact Separate));exact FlagAA. }
   exists mf;split.
   + eapply (exec_linear_verify_guards le m ma mf bl ba bb bk bg br bz true
      (Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (bxword,byword))));assumption.
   + split;[exact XAF|];split;[exact YAF|];split;[exact FlagAF|];split;[exact FAF|];
     split;[exact XBF|];split;[exact YBF|];split;[exact FlagBF|];split;[exact FBF|];split.
     * eapply lframe_trans.
       -- eapply lframe_implies;[exact FrameA|intros b pos [NA NB] Valid;exact NA].
       -- eapply lframe_implies;[exact FrameB|intros b pos [NA NB] Valid;exact NB].
     * eapply preserved_trans;[exact ReadA|exact ReadB].
 - exists ma;split.
   + eapply (exec_linear_verify_guards le m ma ma bl ba bb bk bg br bz false
      (Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (bxword,byword))));[exact CallA|reflexivity].
   + split;[exact XAA|];split;[exact YAA|];split;[exact FlagAA|];split;[exact FAA|];
     split;[exact XBA|];split;[exact YBA|];split;[exact FlagBA|];split;[exact FBA|];split;[|exact ReadA].
     eapply lframe_implies;[exact FrameA|intros b pos [NA NB] Valid;exact NA].
Qed.
