(** Instantiate the original rounded-product function with either actual
    split-lambda global. The final storage is the literal rounded coefficient;
    all input representation and counting/rounding obligations are discharged. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_word_repr C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_scalar_constant C.jet_secp_split_multipliers
 C.jet_secp_scalar_borrowed_inputs C.jet_secp_scalar_mul_reader_bridge
 C.jet_secp_scalar_mul_borrowed_alloc C.jet_secp_scalar_mul512_low
 C.jet_secp_scalar_mul_writer_bridge C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_shift384_function C.jet_secp_split_round_literal
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_scalar_add_reader_support C.jet_secp_statement_prefix C.jet_secp_curve_statements C.jet_secp_split_coefficient C.jet_secp_split_rounding_calls
 C.jet_elements_taptweak_curve_transport C.jet_elements_taptweak_load_body C.jet_elements_taptweak_pure.
Require Import C.jet_elements_taptweak_split_constants.
Lemma elements_taptweak_has_scalar_mul_shift_var:
 In (_secp256k1_scalar_mul_shift_var,f_secp256k1_scalar_mul_shift_var) elements_taptweak_curve_helpers.
Proof.
 assert (Found:find(fun it=>Pos.eqb(fst it)_secp256k1_scalar_mul_shift_var)elements_taptweak_curve_helpers=
 Some(_secp256k1_scalar_mul_shift_var,f_secp256k1_scalar_mul_shift_var))by(vm_compute;reflexivity).
 apply find_some in Found;exact(proj1 Found).
Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_multiplier_block.
Theorem eval_elements_taptweak_split_coefficient first k m bk bc : 0<=k<2^256 -> elements_taptweak_multipliers_ready m ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of k)) ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m bc 0 32 Cur Freeable -> bc<>bk ->
 exists mf,Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_scalar_mul_shift_var)
 [Vptr bc Ptrofs.zero;Vptr bk Ptrofs.zero;Vptr (elements_taptweak_multiplier_block first) Ptrofs.zero;Vint (Int.repr 384)] E0 mf Vundef /\
 scalar_at mf bc 0 (map Int64.repr (scalar_limbs_of (split_coefficient first k))) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of k)) /\
 Mem.range_perm mf bc 0 32 Cur Freeable /\ Mem.range_perm mf bk 0 32 Cur Freeable /\
 elements_taptweak_multipliers_ready mf /\ keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun b _=>b<>bc /\ b<>bk /\ b<>elements_taptweak_multiplier_block first) m mf.
Proof.
 intros Range Ready Input FreeK FreeC Separate.
 pose proof (Ready first) as Global.
 assert (KB:bk<>elements_taptweak_multiplier_block first) by (eapply scalar_constant_separate;[exact Global|exact FreeK]).
 assert (CB:bc<>elements_taptweak_multiplier_block first) by (eapply scalar_constant_separate;[exact Global|exact FreeC]).
 assert (GlobalInput:scalar_at m (elements_taptweak_multiplier_block first) 0
  (map Int64.repr (scalar_limbs_of (split_multiplier_value first)))).
 { rewrite split_multiplier_limbs;exact (proj1 Global). }
 pose proof (scalar_borrowed_inputs_from_storage k (split_multiplier_value first) m bk
  (elements_taptweak_multiplier_block first) Input GlobalInput FreeK KB) as Inputs.
 destruct (eval_scalar_mul_shift384_borrowed (scalar_mul_reader_rho k (split_multiplier_value first))
  [(bk,0);(elements_taptweak_multiplier_block first,0)] m bc Inputs FreeC
  ltac:(intros [|[|r]] R;[exact Separate|exact CB|lia]))
  as (mf & Call & Output & InputsF & FreeCF & Keep & Preserve & Frame).
 destruct (scalar_mul_reader_input_values k (split_multiplier_value first) Range
  ltac:(pose proof (split_multiplier_bounds first);lia)) as [InputValue GlobalValue].
 unfold shift384_output_value in Output;rewrite InputValue,GlobalValue in Output.
 destruct (scalar_borrowed_inputs_source k (split_multiplier_value first) mf bk (elements_taptweak_multiplier_block first) InputsF)
  as [InputF FreeKF].
 exists mf;split.
 { exact(elements_taptweak_curve_transport _ _ m _ _ mf _ elements_taptweak_has_scalar_mul_shift_var Call). }
 split;[exact Output|];split;[exact InputF|];split;[exact FreeCF|];split;
 [exact FreeKF|];split;[eapply elements_taptweak_multipliers_readonly;[exact Ready|exact Preserve]|];
 split;[exact Keep|];split;[exact Preserve|].
 eapply lframe_implies;[exact Frame|].
 intros b ofs (NotC & NotK & NotG) Valid;split;[exact NotC|].
 intros (r & sh & d & ch & Nth & Cell & Eq & Bytes);destruct r as [|[|r]].
 - apply NotK;exact Eq.
 - apply NotG;exact Eq.
 - cbn [scalar_mul_borrowed_inputs map nth_error] in Nth;destruct r;discriminate Nth.
Qed.

Theorem eval_elements_taptweak_split_coefficient_literal first (k:Ty.tySem (Word 8)) m bk bc : elements_taptweak_multipliers_ready m ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k))) ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m bc 0 32 Cur Freeable -> bc<>bk ->
 exists mf,Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_scalar_mul_shift_var)
 [Vptr bc Ptrofs.zero;Vptr bk Ptrofs.zero;Vptr (elements_taptweak_multiplier_block first) Ptrofs.zero;Vint (Int.repr 384)] E0 mf Vundef /\
 scalar_at mf bc 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (@literal_split_coefficient first Alg.CoreFunSem k)))) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k))) /\
 Mem.range_perm mf bc 0 32 Cur Freeable /\ Mem.range_perm mf bk 0 32 Cur Freeable /\
 elements_taptweak_multipliers_ready mf /\ keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun b _=>b<>bc /\ b<>bk /\ b<>elements_taptweak_multiplier_block first) m mf.
Proof.
 intros Ready Input FK FC Separate;rewrite literal_split_coefficient_numeric.
 apply eval_elements_taptweak_split_coefficient;[apply word_toZ_range|exact Ready|exact Input|exact FK|exact FC|exact Separate].
Qed.
Definition elements_taptweak_rounding_frame bk bc1 bc2 b (_:Z):=b<>bc1 /\b<>bc2 /\b<>bk /\
 b<>elements_taptweak_multiplier_block true /\b<>elements_taptweak_multiplier_block false.
Lemma exec_elements_taptweak_split_coefficient_call (first:bool) bc1 bc2 le m mf bk : le!_k=Some (Vptr bk Ptrofs.zero) ->
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_scalar_mul_shift_var)
 [Vptr (if first then bc1 else bc2) Ptrofs.zero;Vptr bk Ptrofs.zero;
  Vptr (elements_taptweak_multiplier_block first) Ptrofs.zero;Vint (Int.repr 384)] E0 mf Vundef ->
 Clight2.exec_stmt elements_taptweak_ge (split_local_env bc1 bc2) le m (split_coefficient_statement first) E0 le mf Out_normal.
Proof.
 intros K Call;rewrite split_coefficient_call_source.
 eapply (exec_elements_taptweak_arith_call _secp256k1_scalar_mul_shift_var f_secp256k1_scalar_mul_shift_var None _
  [Vptr (if first then bc1 else bc2) Ptrofs.zero;Vptr bk Ptrofs.zero;
   Vptr (elements_taptweak_multiplier_block first) Ptrofs.zero;Vint (Int.repr 384)] Vundef).
 - exact elements_taptweak_has_scalar_mul_shift_var.
 - reflexivity.
 - eapply eval_Econs with (v1:=Vptr (if first then bc1 else bc2) Ptrofs.zero);
   [apply eval_Eaddrof;apply eval_Evar_local;destruct first;reflexivity|reflexivity|].
   eapply eval_Econs;[apply eval_Etempvar;exact K|reflexivity|].
   eapply eval_Econs with (v1:=Vptr (elements_taptweak_multiplier_block first) Ptrofs.zero);
    [apply eval_Eaddrof;apply eval_Evar_global;
    [destruct first;reflexivity|apply elements_taptweak_multiplier_symbol]|reflexivity|].
   eapply eval_Econs;[constructor|reflexivity|constructor].
 - exact Call.
Qed.

Lemma exec_elements_taptweak_split_initial_noops e le m :
 Clight2.exec_stmt elements_taptweak_ge e le m (statement_sequence (firstn 3 (fst split_parts)) Sskip) E0 le m Out_normal.
Proof.
 repeat (eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le);
  [eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le)
   (out1:=Out_normal) (out2:=Out_break);constructor|]);constructor.
Qed.

Theorem exec_elements_taptweak_split_rounding_prefix (k:Ty.tySem (Word 8)) le m bk bc1 bc2 :
 elements_taptweak_multipliers_ready m -> le!_k=Some (Vptr bk Ptrofs.zero) ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k))) ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m bc1 0 32 Cur Freeable ->
 Mem.range_perm m bc2 0 32 Cur Freeable -> bc1<>bc2 -> bc1<>bk -> bc2<>bk ->
 exists mf,Clight2.exec_stmt elements_taptweak_ge (split_local_env bc1 bc2) le m split_rounding_prefix E0 le mf Out_normal /\
 scalar_at mf bc1 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (@literal_split_coefficient true Alg.CoreFunSem k)))) /\
 scalar_at mf bc2 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (@literal_split_coefficient false Alg.CoreFunSem k)))) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k))) /\
 Mem.range_perm mf bc1 0 32 Cur Freeable /\ Mem.range_perm mf bc2 0 32 Cur Freeable /\
 Mem.range_perm mf bk 0 32 Cur Freeable /\ elements_taptweak_multipliers_ready mf /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (elements_taptweak_rounding_frame bk bc1 bc2) m mf.
Proof.
 intros Ready K Input FK F1 F2 Separate C1K C2K.
 destruct (eval_elements_taptweak_split_coefficient_literal true k m bk bc1 Ready Input FK F1 C1K)
  as (m1 & Call1 & Out1 & Input1 & F11 & FK1 & Ready1 & Keep1 & Preserve1 & Frame1).
 assert (F21:Mem.range_perm m1 bc2 0 32 Cur Freeable) by (intros pos Range;apply Keep1,F2;exact Range).
 destruct (eval_elements_taptweak_split_coefficient_literal false k m1 bk bc2 Ready1 Input1 FK1 F21 C2K)
  as (mf & Call2 & Out2 & InputF & F2F & FKF & ReadyF & Keep2 & Preserve2 & Frame2).
 assert (C1G2:bc1<>elements_taptweak_multiplier_block false) by
  (eapply scalar_constant_separate;[apply Ready1|exact F11]).
 assert (Out1F:scalar_at mf bc1 0
  (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (@literal_split_coefficient true Alg.CoreFunSem k))))).
 { eapply scalar_at_lframe;[exact Out1|exact Frame2|];intros;repeat split;assumption. }
 exists mf;split.
 - change (Clight2.exec_stmt elements_taptweak_ge (split_local_env bc1 bc2) le m
    (statement_sequence (firstn 3 (fst split_parts)) (Ssequence (split_coefficient_statement true)
     (Ssequence (split_coefficient_statement false) Sskip))) E0 le mf Out_normal).
   eapply exec_statement_prefix_then_last;[apply exec_elements_taptweak_split_initial_noops|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le).
   + apply exec_elements_taptweak_split_coefficient_call with (bk:=bk);assumption.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
     * apply exec_elements_taptweak_split_coefficient_call with (bk:=bk);assumption.
     * constructor.
 - split;[exact Out1F|];split;[exact Out2|];split;[exact InputF|];split.
   + intros pos Range;apply Keep2,F11;exact Range.
   + split;[exact F2F|];split;[exact FKF|];split;[exact ReadyF|];split.
     * intros b pos kind perm Perm;apply Keep2,Keep1;exact Perm.
     * split;[eapply preserved_trans;[exact Preserve1|exact Preserve2]|].
       eapply lframe_trans.
       -- eapply lframe_implies;[exact Frame1|];intros b pos (Not1 & Not2 & NotK & NotG1 & NotG2) Valid;exact(conj Not1(conj NotK NotG1)).
       -- eapply lframe_implies;[exact Frame2|];intros b pos (Not1 & Not2 & NotK & NotG1 & NotG2) Valid;exact(conj Not2(conj NotK NotG2)).
Qed.
