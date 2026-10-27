(** The actual split Scall followed by both original signed window-5 blocks.
    The helper executions, digits and preserved caller state are derived. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_memset_model
 C.jet_secp_curve_statements C.jet_secp_strauss_wnaf_calls C.jet_secp_wnaf_slice_frame
 C.jet_secp_statement_prefix C.jet_secp_generator_preprocess
 C.jet_secp_wnaf_loop C.jet_secp_wnaf5_input C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_signed_array
 C.jet_secp_split_literal_function C.jet_secp_split_literal C.jet_secp_split_constants
 C.jet_secp_split_function C.jet_secp_split_multipliers C.jet_secp_scalar_constant
 C.jet_secp_scalar_lambda_global C.jet_secp_canonical_scalar C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_add_reader_support
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Local Opaque secp_ge canonical_scalar_normalize literal_scalar_split_lambda.
Set Default Timeout 10.

Lemma strauss_split_call_source : strauss_split_call=
 curve_call _secp256k1_scalar_split_lambda f_secp256k1_scalar_split_lambda None
 [Eaddrof (Evar _na_1 (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
  Eaddrof (Evar _na_lam (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
  Ebinop Oadd (Etempvar _na (tptr (Tstruct __5826 noattr))) (Etempvar _np tulong)
   (tptr (Tstruct __5826 noattr))].
Proof. reflexivity. Qed.

Lemma strauss_split_owned_constant_separate m bx b words :
 scalar_constant_state b words m -> Mem.perm m bx 0 Cur Freeable -> bx<>b.
Proof.
 intros [_ NoWrite] Owned Same;apply (NoWrite 0);rewrite <-Same.
 apply Mem.perm_cur_max;eapply Mem.perm_implies;[exact Owned|constructor].
Qed.

Lemma strauss_split_owned_frame m bk br1 br2 bx :
 split_constants_ready m -> Mem.perm m bx 0 Cur Freeable ->
 bx<>bk -> bx<>br1 -> bx<>br2 -> forall pos,split_function_frame bk br1 br2 bx pos.
Proof.
 intros Ready Owned K R1 R2 pos;unfold split_function_frame.
 split;[exact K|];split;[exact R1|];split;[exact R2|];repeat split;
 eapply strauss_split_owned_constant_separate;[|exact Owned| |exact Owned| |exact Owned| |exact Owned| |exact Owned].
 - exact (proj1 Ready Datatypes.true).
 - exact (proj1 Ready Datatypes.false).
 - exact (proj1 (proj2 Ready) Datatypes.true).
 - exact (proj1 (proj2 Ready) Datatypes.false).
 - exact (proj2 (proj2 Ready)).
Qed.

Theorem exec_strauss_split_literal e le m raw bk br1 br2 :
 e!_na_1=Some (br1,Tstruct __5826 noattr) -> e!_na_lam=Some (br2,Tstruct __5826 noattr) ->
 e!_secp256k1_scalar_split_lambda=None -> le!_na=Some (Vptr bk Ptrofs.zero) ->
 le!_np=Some (Vlong Int64.zero) -> split_constants_ready m ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m br1 0 32 Cur Freeable ->
 Mem.range_perm m br2 0 32 Cur Freeable -> NoDup [bk;br1;br2] ->
 let halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw in
 exists mf,Clight2.exec_stmt secp_ge e le m strauss_split_call E0 le mf Out_normal /\
 scalar_at mf br1 0 (map Int64.repr (scalar_limbs_of
  (wnaf5_input_scalar (fst (fst halves)) (snd (fst halves))))) /\
 scalar_at mf br2 0 (map Int64.repr (scalar_limbs_of
  (wnaf5_input_scalar (fst (snd halves)) (snd (snd halves))))) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) /\
 Mem.range_perm mf br1 0 32 Cur Freeable /\ Mem.range_perm mf br2 0 32 Cur Freeable /\
 Mem.range_perm mf bk 0 32 Cur Freeable /\ split_constants_ready mf /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (split_function_frame bk br1 br2) m mf.
Proof.
 intros Low High Symbol NA NP Ready Input FK F1 F2 Separate;cbv zeta.
 destruct (eval_scalar_split_lambda_literal raw m bk br1 br2 Ready Input FK F1 F2 Separate)
  as (mf & Call & Rest);exists mf;split;[|exact Rest].
 rewrite strauss_split_call_source;eapply exec_curve_call with
  (vargs:=[Vptr br1 Ptrofs.zero;Vptr br2 Ptrofs.zero;Vptr bk Ptrofs.zero]) (v:=Vundef).
 - unfold secp_pure;repeat first [left;reflexivity|right].
 - exact Symbol.
 - eapply eval_Econs with (v1:=Vptr br1 Ptrofs.zero).
   + apply eval_Eaddrof;apply eval_Evar_local;exact Low.
   + reflexivity.
   + eapply eval_Econs with (v1:=Vptr br2 Ptrofs.zero).
     * apply eval_Eaddrof;apply eval_Evar_local;exact High.
     * reflexivity.
     * eapply eval_Econs with (v1:=Vptr bk Ptrofs.zero);[|reflexivity|constructor].
       eapply eval_Ebinop with (v1:=Vptr bk Ptrofs.zero) (v2:=Vlong Int64.zero);
        [apply eval_Etempvar;exact NA|apply eval_Etempvar;exact NP|].
       assert (Size:sizeof (genv_cenv secp_ge) (Tstruct __5826 noattr)=32) by reflexivity.
       change (Some (Vptr bk (Ptrofs.add Ptrofs.zero
        (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv secp_ge) (Tstruct __5826 noattr)))
         (Ptrofs.of_int64 Int64.zero))))=Some (Vptr bk Ptrofs.zero)).
       rewrite Size;reflexivity.
 - exact Call.
Qed.

Definition strauss_split_wnaf_prepare := Ssequence strauss_split_call strauss_wnaf_prepare.

Lemma exec_strauss_split_wnaf_then_rest e le m l1 m1 lf mf out :
 Clight2.exec_stmt secp_ge e le m strauss_split_wnaf_prepare E0 l1 m1 Out_normal ->
 Clight2.exec_stmt secp_ge e l1 m1 strauss_after_wnaf E0 lf mf out ->
 Clight2.exec_stmt secp_ge e le m generator_preprocess_after_check E0 lf mf out.
Proof.
 intros Prefix Rest;rewrite strauss_wnaf_source.
 change (Clight2.exec_stmt secp_ge e le m
  (statement_sequence [strauss_split_call;strauss_wnaf_half Datatypes.false;
   strauss_wnaf_half Datatypes.true] strauss_after_wnaf) E0 lf mf out).
 eapply exec_statement_prefix_then_last;[exact Prefix|exact Rest].
Qed.

Theorem exec_strauss_split_wnaf_prepare (Model:memset_model) e le m raw bk br1 br2 bs bp :
 e!_na_1=Some (br1,Tstruct __5826 noattr) -> e!_na_lam=Some (br2,Tstruct __5826 noattr) ->
 e!_secp256k1_scalar_split_lambda=None -> e!_secp256k1_ecmult_wnaf=None ->
 le!_na=Some (Vptr bk Ptrofs.zero) -> le!_np=Some (Vlong Int64.zero) ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_no=Some (Vlong Int64.zero) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) -> split_constants_ready m ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m br1 0 32 Cur Freeable ->
 Mem.range_perm m br2 0 32 Cur Freeable -> Mem.range_perm m bs 0 24 Cur Freeable ->
 Mem.range_perm m bp 0 1040 Cur Freeable -> NoDup [bk;br1;br2;bs;bp] ->
 let halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw in
 exists mf last1 last2 digits1 digits2,
 Clight2.exec_stmt secp_ge e le m strauss_split_wnaf_prepare E0
  (strauss_wnaf_prepare_temps le bp (last1+1) (last2+1)) mf Out_normal /\
 wnaf_array_state mf bp 0 129 5 (wnaf5_input_sign (fst (fst halves))) 129 last1 digits1 /\
 wnaf_array_state mf bp 516 129 5 (wnaf5_input_sign (fst (snd halves))) 129 last2 digits2 /\
 0<=last1+1<=129 /\ 0<=last2+1<=129 /\
 Mem.load Mint32 mf bp 1032=Some (Vint (Int.repr (last1+1))) /\
 Mem.load Mint32 mf bp 1036=Some (Vint (Int.repr (last2+1))) /\
 Mem.load Mptr mf bs 16=Some (Vptr bp Ptrofs.zero) /\
 scalar_at mf br1 0 (map Int64.repr (scalar_limbs_of
  (wnaf5_input_scalar (fst (fst halves)) (snd (fst halves))))) /\
 scalar_at mf br2 0 (map Int64.repr (scalar_limbs_of
  (wnaf5_input_scalar (fst (snd halves)) (snd (snd halves))))) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) /\
 Mem.range_perm mf bp 0 1040 Cur Freeable /\ split_constants_ready mf /\
 keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun old pos=>split_function_frame bk br1 br2 old pos /\
  wnaf_slice_outside bp 0 260 old pos) m mf /\
 map wnaf5_literal_value (literal_wnaf5_digits (fst halves))=
  rev (map (fun i=>wnaf5_input_sign (fst (fst halves))*digits1 (Z.of_nat i)) (seq 0 129)) /\
 map wnaf5_literal_value (literal_wnaf5_digits (snd halves))=
  rev (map (fun i=>wnaf5_input_sign (fst (snd halves))*digits2 (Z.of_nat i)) (seq 0 129)).
Proof.
 intros Low High SplitSymbol WnafSymbol NA NP State No Pointer Ready Input FK F1 F2 FS FP Separate;
  cbv zeta.
 assert (D:bk<>br1 /\ bk<>br2 /\ bk<>bs /\ bk<>bp /\ br1<>br2 /\
  br1<>bs /\ br1<>bp /\ br2<>bs /\ br2<>bp /\ bs<>bp).
 { repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence. }
 assert (Three:NoDup [bk;br1;br2]).
 { repeat rewrite NoDup_cons_iff;cbn [In];repeat split;try constructor;intuition congruence. }
 assert (StateFrame:forall pos,split_function_frame bk br1 br2 bs pos).
 { apply (strauss_split_owned_frame m);[exact Ready|apply (FS 0);lia| | |];intuition congruence. }
 destruct (exec_strauss_split_literal e le m raw bk br1 br2 Low High SplitSymbol NA NP
  Ready Input FK F1 F2 Three)
  as (ms & Split & Source1 & Source2 & SourceK & F1S & F2S & FKS & ReadyS & KeepS & ReadonlyS & FrameS).
 assert (StateValid:Mem.valid_block m bs).
 { eapply Mem.perm_valid_block;apply (FS 0);lia. }
 assert (PointerS:Mem.load Mptr ms bs 16=Some (Vptr bp Ptrofs.zero)).
 { rewrite (proj1 FrameS Mptr bs 16 StateValid ltac:(intros;apply StateFrame));exact Pointer. }
 assert (FPS:Mem.range_perm ms bp 0 1040 Cur Freeable).
 { intros pos Range;apply KeepS,FP;exact Range. }
 destruct (exec_strauss_wnaf_prepare Model e le ms bs bp br1 br2
  (fst (fst (@literal_scalar_split_lambda Alg.CoreFunSem raw)))
  (fst (snd (@literal_scalar_split_lambda Alg.CoreFunSem raw)))
  (snd (fst (@literal_scalar_split_lambda Alg.CoreFunSem raw)))
  (snd (snd (@literal_scalar_split_lambda Alg.CoreFunSem raw)))
  Low High WnafSymbol State No PointerS ltac:(tauto) ltac:(tauto) ltac:(tauto) FPS Source1 Source2)
  as (mf & last1 & last2 & digits1 & digits2 & Wnaf & Array1 & Array2 & Bound1 & Bound2 &
   Count1 & Count2 & PointerF & Source1F & Source2F & FPF & FrameW & KeepW & ReadonlyW & Literal1 & Literal2).
 assert (SourceKF:scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw))))).
 { eapply scalar_at_lframe;[exact SourceK|exact FrameW|intros;left;tauto]. }
 assert (Frame:lframe (fun old pos=>split_function_frame bk br1 br2 old pos /\
  wnaf_slice_outside bp 0 260 old pos) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameS|intros old pos [Part _] _;exact Part].
   - eapply lframe_implies;[exact FrameW|intros old pos [_ Part] _;exact Part]. }
 exists mf,last1,last2,digits1,digits2;split.
 - unfold strauss_split_wnaf_prepare;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);
   [exact Split|exact Wnaf].
 - split;[exact Array1|];split;[exact Array2|];split;[exact Bound1|];split;[exact Bound2|];
   split;[exact Count1|];split;[exact Count2|];split;[exact PointerF|];
   split;[exact Source1F|];split;[exact Source2F|];split;[exact SourceKF|];split;[exact FPF|];split.
   + eapply split_constants_readonly;[exact ReadyS|exact ReadonlyW].
   + split.
     * eapply keeps_permissions_trans;[exact KeepS|exact KeepW].
     * split.
       -- eapply preserved_trans;[exact ReadonlyS|exact ReadonlyW].
       -- split;[exact Frame|];split.
          ++ exact (eq_trans (f_equal (fun half=>map wnaf5_literal_value (literal_wnaf5_digits half))
              (@surjective_pairing _ _ (fst (@literal_scalar_split_lambda Alg.CoreFunSem raw)))) Literal1).
          ++ exact (eq_trans (f_equal (fun half=>map wnaf5_literal_value (literal_wnaf5_digits half))
              (@surjective_pairing _ _ (snd (@literal_scalar_split_lambda Alg.CoreFunSem raw)))) Literal2).
Qed.
