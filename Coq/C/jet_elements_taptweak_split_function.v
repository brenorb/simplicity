(** Entire linked scalar_split_lambda call and exact literal signed halves.
    Both private coefficients and initially unrestricted outputs are derived
    from the original calls; source-unit global blocks are not assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_add_reader_support
 C.jet_secp_scalar_lambda_global C.jet_secp_split_multipliers C.jet_secp_split_constants
 C.jet_secp_split_round_literal C.jet_secp_split_rounding_calls C.jet_secp_split_rounding_entry
 C.jet_secp_split_arithmetic_calls C.jet_secp_split_arithmetic C.jet_secp_statement_prefix
 C.jet_secp_slice_permissions C.jet_secp_closed_helpers C.jet_clight_internal_frame
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_elements_taptweak_pure C.jet_secp_split_function C.jet_transport.
Require Import C.jet_elements_taptweak_split_constants C.jet_elements_taptweak_split_rounding
 C.jet_elements_taptweak_split_entry C.jet_elements_taptweak_split_arithmetic.
Lemma elements_taptweak_scalar_size:
 sizeof elements_taptweak_ge(Tstruct __5826 noattr)=32.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_multiplier_block
 elements_taptweak_basis_block elements_taptweak_lambda_block.
Definition elements_taptweak_split_function_frame bk br1 br2 b (_:Z):=
 b<>bk /\b<>br1 /\b<>br2 /\b<>elements_taptweak_multiplier_block true /\b<>elements_taptweak_multiplier_block false /\
 b<>elements_taptweak_basis_block true /\b<>elements_taptweak_basis_block false /\b<>elements_taptweak_lambda_block.
Lemma elements_taptweak_split_function_blocks bc1 bc2:
 blocks_of_env elements_taptweak_ge(split_local_env bc1 bc2)=[(bc2,0,32);(bc1,0,32)].
Proof.
 change ([(bc2,0,sizeof elements_taptweak_ge(Tstruct __5826 noattr));
 (bc1,0,sizeof elements_taptweak_ge(Tstruct __5826 noattr))]=[(bc2,0,32);(bc1,0,32)]).
 rewrite elements_taptweak_scalar_size;reflexivity.
Qed.
Require Import C.jet_secp_split_literal C.jet_secp_split_numeric C.jet_secp_wnaf5_input.
Theorem eval_elements_taptweak_scalar_split_lambda (k:Ty.tySem (Word 8)) m bk br1 br2 :
 0<= @toZ (WordToZ 8) k<canonical_group_order -> elements_taptweak_split_ready m ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k))) ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m br1 0 32 Cur Freeable ->
 Mem.range_perm m br2 0 32 Cur Freeable -> NoDup [bk;br1;br2] ->
 exists mf,Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_scalar_split_lambda)
 [Vptr br1 Ptrofs.zero;Vptr br2 Ptrofs.zero;Vptr bk Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf br1 0 (map Int64.repr (scalar_limbs_of (split_first_value (@toZ (WordToZ 8) k)))) /\
 scalar_at mf br2 0 (map Int64.repr (scalar_limbs_of (split_second_value (@toZ (WordToZ 8) k)))) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k))) /\
 Mem.range_perm mf br1 0 32 Cur Freeable /\ Mem.range_perm mf br2 0 32 Cur Freeable /\
 Mem.range_perm mf bk 0 32 Cur Freeable /\ elements_taptweak_split_ready mf /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (elements_taptweak_split_function_frame bk br1 br2) m mf.
Proof.
 intros Range Ready Input FK FR1 FR2 Separate.
 destruct (elements_taptweak_split_entry_rounding k (Vptr br1 Ptrofs.zero) (Vptr br2 Ptrofs.zero) bk m
  (proj1 Ready) Input FK)
  as (bc1 & bc2 & mi & mp & Entry & Prefix & C1 & C2 & InputP & FC1 & FC2 & FKP & GlobalsP &
      C12 & C1K & C2K & Fresh1 & Fresh2 & KeepP & PreserveP & FrameP).
 rewrite !literal_split_coefficient_numeric in C1,C2.
 assert (ReadyP:elements_taptweak_split_ready mp) by (eapply elements_taptweak_split_readonly;[exact Ready|exact PreserveP]).
 assert (V1:Mem.valid_block m br1) by (eapply Mem.perm_valid_block;apply (FR1 0);lia).
 assert (V2:Mem.valid_block m br2) by (eapply Mem.perm_valid_block;apply (FR2 0);lia).
 assert (C1R1:bc1<>br1) by (intro Eq;apply Fresh1;rewrite Eq;exact V1).
 assert (C1R2:bc1<>br2) by (intro Eq;apply Fresh1;rewrite Eq;exact V2).
 assert (C2R1:bc2<>br1) by (intro Eq;apply Fresh2;rewrite Eq;exact V1).
 assert (C2R2:bc2<>br2) by (intro Eq;apply Fresh2;rewrite Eq;exact V2).
 assert (Distinct:NoDup [bk;br1;br2;bc1;bc2]).
 { repeat rewrite NoDup_cons_iff in Separate;repeat rewrite NoDup_cons_iff;
   cbn [In] in Separate|-*;intuition congruence. }
 set (le:=split_entry_temps (Vptr br1 Ptrofs.zero) (Vptr br2 Ptrofs.zero) bk).
 destruct (exec_elements_taptweak_split_arithmetic (@toZ (WordToZ 8) k) le mp bk br1 br2 bc1 bc2
  Range ReadyP eq_refl eq_refl eq_refl InputP C1 C2 FKP
  ltac:(eapply keeps_range_permissions;[exact KeepP|exact FR1])
  ltac:(eapply keeps_range_permissions;[exact KeepP|exact FR2]) FC1 FC2 Distinct)
  as (mb & Suffix & First & Second & InputB & FC1B & FC2B & KeepB & PreserveB & ReadyB & FrameB).
 destruct (free_list_exists [(bc2,0,32);(bc1,0,32)] mb) as (mf & Freed & Unchanged).
 { repeat constructor;cbn;intuition congruence. }
 { intros b lo hi [Eq|[Eq|[]]];injection Eq as <- <- <-;assumption. }
 assert (FreeFrame:lframe (fun b _=>b<>bc1 /\ b<>bc2) mb mf).
 { apply lframe_unchanged;eapply Mem.unchanged_on_implies;[exact Unchanged|].
   intros b pos [Not1 Not2] Valid;change (~(bc2=b \/ bc1=b \/ False));intuition congruence. }
 assert (Call:Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_scalar_split_lambda)
  [Vptr br1 Ptrofs.zero;Vptr br2 Ptrofs.zero;Vptr bk Ptrofs.zero] E0 mf Vundef).
 { eapply eval_funcall_internal with (e:=split_local_env bc1 bc2) (le1:=le) (le2:=le)
   (m1:=mi) (m2:=mb) (out:=Out_normal).
   - exact Entry.
   - rewrite split_whole_source;eapply exec_statement_prefix_then_last;[exact Prefix|exact Suffix].
   - constructor.
   - rewrite elements_taptweak_split_function_blocks;exact Freed. }
 assert(Keep:keeps_permissions m mf).
 { intros b pos kind perm Perm.
   eapply free_list_avoids;[exact Freed| |apply KeepB,KeepP;exact Perm].
   intros lo hi [Eq|[Eq|[]]];injection Eq as Same _ _;subst b.
   - apply Fresh2;eapply Mem.perm_valid_block;exact Perm.
   - apply Fresh1;eapply Mem.perm_valid_block;exact Perm. }
 assert(Preserve:readonly_preserved m mf).
 { eapply preserved_trans;[exact PreserveP|].
   eapply preserved_trans;[exact PreserveB|eapply freelist_preserved;exact Freed]. }
 exists mf;split;[exact Call|];split.
 - eapply scalar_at_lframe;[exact First|exact FreeFrame|];intros;split;congruence.
 - split.
   + eapply scalar_at_lframe;[exact Second|exact FreeFrame|];intros;split;congruence.
   + split.
     * eapply scalar_at_lframe;[exact InputB|exact FreeFrame|];intros;split;congruence.
     * split;[eapply keeps_range_permissions;[exact Keep|exact FR1]|];split;
       [eapply keeps_range_permissions;[exact Keep|exact FR2]|];split;
       [eapply keeps_range_permissions;[exact Keep|exact FK]|];split;
       [eapply elements_taptweak_split_readonly;[exact Ready|exact Preserve]|];split;[exact Keep|];split;[exact Preserve|].
       set (P:=fun b ofs=>Mem.valid_block m b /\ elements_taptweak_split_function_frame bk br1 br2 b ofs).
       assert (Frame:lframe P m mf).
       { eapply lframe_trans with (m2:=mp).
         - eapply lframe_implies;[exact FrameP|];intros b pos [Valid Outside] ValidP;unfold elements_taptweak_split_entry_frame.
         destruct Outside as(NotK & NotR1 & NotR2 & NotG1 & NotG2 & _).
         exact(conj NotK(conj NotG1 NotG2)).
         - eapply lframe_trans with (m2:=mb).
           + eapply lframe_implies;[exact FrameB|].
             intros b ofs [Valid Outside] ValidP;unfold elements_taptweak_arithmetic_frame.
             unfold elements_taptweak_split_function_frame in Outside;destruct Outside as (K & R1 & R2 & G1 & G2 & B1 & B2 & L).
             assert(NotC1:b<>bc1)by(intro Eq;apply Fresh1;rewrite <-Eq;exact Valid).
             assert(NotC2:b<>bc2)by(intro Eq;apply Fresh2;rewrite <-Eq;exact Valid).
             exact(conj K(conj R1(conj R2(conj NotC1(conj NotC2(conj B1(conj B2 L))))))).
           + eapply lframe_implies;[exact FreeFrame|];intros b ofs [Valid Outside] ValidB.
             split;[intro Eq;apply Fresh1;rewrite <-Eq;exact Valid|
                    intro Eq;apply Fresh2;rewrite <-Eq;exact Valid]. }
       eapply lframe_implies;[exact Frame|];intros b ofs Outside Valid;split;[exact Valid|exact Outside].
Qed.
Theorem eval_elements_taptweak_scalar_split_lambda_literal (raw:Ty.tySem (Word 8)) m bk br1 br2 :
 elements_taptweak_split_ready m ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m br1 0 32 Cur Freeable ->
 Mem.range_perm m br2 0 32 Cur Freeable -> NoDup [bk;br1;br2] ->
 let halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw in
 exists mf,Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_scalar_split_lambda)
 [Vptr br1 Ptrofs.zero;Vptr br2 Ptrofs.zero;Vptr bk Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf br1 0 (map Int64.repr (scalar_limbs_of
  (wnaf5_input_scalar (fst (fst halves)) (snd (fst halves))))) /\
 scalar_at mf br2 0 (map Int64.repr (scalar_limbs_of
  (wnaf5_input_scalar (fst (snd halves)) (snd (snd halves))))) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) /\
 Mem.range_perm mf br1 0 32 Cur Freeable /\ Mem.range_perm mf br2 0 32 Cur Freeable /\
 Mem.range_perm mf bk 0 32 Cur Freeable /\ elements_taptweak_split_ready mf /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (elements_taptweak_split_function_frame bk br1 br2) m mf.
Proof.
 intros Ready Input FK FR1 FR2 Separate;cbv zeta.
 pose (k:=@canonical_scalar_normalize Alg.CoreFunSem raw).
 assert (K:0<= @toZ (WordToZ 8) k<canonical_group_order).
 { unfold k;rewrite canonical_scalar_normalize_numeric;apply Z.mod_pos_bound.
   pose proof canonical_group_order_range;lia. }
 destruct (eval_elements_taptweak_scalar_split_lambda k m bk br1 br2 K Ready Input FK FR1 FR2 Separate)
  as (mf & Call & First & Second & Rest).
 pose proof (literal_scalar_split_lambda_residues raw) as Bridge.
 change (wnaf5_input_scalar
   (fst (fst (@literal_scalar_split_lambda Alg.CoreFunSem raw)))
   (snd (fst (@literal_scalar_split_lambda Alg.CoreFunSem raw)))=split_first_value (@toZ (WordToZ 8) k) /\
  wnaf5_input_scalar
   (fst (snd (@literal_scalar_split_lambda Alg.CoreFunSem raw)))
   (snd (snd (@literal_scalar_split_lambda Alg.CoreFunSem raw)))=split_second_value (@toZ (WordToZ 8) k)) in Bridge.
 destruct Bridge as [FirstValue SecondValue].
 exists mf;split;[exact Call|];split.
 - exact (eq_rect _ (fun v:Z=>scalar_at mf br1 0 (map Int64.repr (scalar_limbs_of v)))
    First _ (eq_sym FirstValue)).
 - split.
   + exact (eq_rect _ (fun v:Z=>scalar_at mf br2 0 (map Int64.repr (scalar_limbs_of v)))
      Second _ (eq_sym SecondValue)).
   + exact Rest.
Qed.

