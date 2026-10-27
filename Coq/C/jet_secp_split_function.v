(** Complete original scalar_split_lambda execution on a canonical input.
    Both private coefficients and both initially unrestricted outputs are
    established by the actual calls. Literal signed-half correspondence is
    a separate remaining obligation; these results identify the C values. *)
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
Local Opaque secp_ge split_basis_block split_multiplier_block scalar_lambda_block.

Definition split_function_frame bk br1 br2 b (_:Z) :=
 b<>bk /\ b<>br1 /\ b<>br2 /\ b<>split_multiplier_block true /\ b<>split_multiplier_block false /\
 b<>split_basis_block true /\ b<>split_basis_block false /\ b<>scalar_lambda_block.

Lemma split_function_blocks bc1 bc2 : blocks_of_env secp_ge (split_local_env bc1 bc2)=
 [(bc2,0,32);(bc1,0,32)].
Proof. reflexivity. Qed.
Lemma split_function_closed : closed_stmtb secp_closed_helpers (fn_body f_secp256k1_scalar_split_lambda)=true.
Proof. timeout 10 (vm_compute;reflexivity). Qed.

Theorem eval_scalar_split_lambda (k:Ty.tySem (Word 8)) m bk br1 br2 :
 0<= @toZ (WordToZ 8) k<canonical_group_order -> split_constants_ready m ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k))) ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m br1 0 32 Cur Freeable ->
 Mem.range_perm m br2 0 32 Cur Freeable -> NoDup [bk;br1;br2] ->
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_split_lambda)
 [Vptr br1 Ptrofs.zero;Vptr br2 Ptrofs.zero;Vptr bk Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf br1 0 (map Int64.repr (scalar_limbs_of (split_first_value (@toZ (WordToZ 8) k)))) /\
 scalar_at mf br2 0 (map Int64.repr (scalar_limbs_of (split_second_value (@toZ (WordToZ 8) k)))) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k))) /\
 Mem.range_perm mf br1 0 32 Cur Freeable /\ Mem.range_perm mf br2 0 32 Cur Freeable /\
 Mem.range_perm mf bk 0 32 Cur Freeable /\ split_constants_ready mf /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (split_function_frame bk br1 br2) m mf.
Proof.
 intros Range Ready Input FK FR1 FR2 Separate.
 destruct (scalar_split_entry_rounding k (Vptr br1 Ptrofs.zero) (Vptr br2 Ptrofs.zero) bk m
  (proj1 Ready) Input FK)
  as (bc1 & bc2 & mi & mp & Entry & Prefix & C1 & C2 & InputP & FC1 & FC2 & FKP & GlobalsP &
      C12 & C1K & C2K & Fresh1 & Fresh2 & KeepP & PreserveP & FrameP).
 rewrite !literal_split_coefficient_numeric in C1,C2.
 assert (ReadyP:split_constants_ready mp) by (eapply split_constants_readonly;[exact Ready|exact PreserveP]).
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
 destruct (exec_split_arithmetic (@toZ (WordToZ 8) k) le mp bk br1 br2 bc1 bc2
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
 assert (Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_split_lambda)
  [Vptr br1 Ptrofs.zero;Vptr br2 Ptrofs.zero;Vptr bk Ptrofs.zero] E0 mf Vundef).
 { eapply eval_funcall_internal with (e:=split_local_env bc1 bc2) (le1:=le) (le2:=le)
   (m1:=mi) (m2:=mb) (out:=Out_normal).
   - exact Entry.
   - rewrite split_whole_source;eapply exec_statement_prefix_then_last;[exact Prefix|exact Suffix].
   - constructor.
   - rewrite split_function_blocks;exact Freed. }
 assert (Keep:keeps_permissions m mf) by
  (eapply secp_internal_keeps_permissions;[exact split_function_closed|reflexivity|exact Call]).
 assert (Preserve:readonly_preserved m mf) by
  (eapply (secp_closed_function_preserved f_secp256k1_scalar_split_lambda);
   [exact split_function_closed|reflexivity|exact Call]).
 exists mf;split;[exact Call|];split.
 - eapply scalar_at_lframe;[exact First|exact FreeFrame|];intros;split;congruence.
 - split.
   + eapply scalar_at_lframe;[exact Second|exact FreeFrame|];intros;split;congruence.
   + split.
     * eapply scalar_at_lframe;[exact InputB|exact FreeFrame|];intros;split;congruence.
     * split;[eapply keeps_range_permissions;[exact Keep|exact FR1]|];split;
       [eapply keeps_range_permissions;[exact Keep|exact FR2]|];split;
       [eapply keeps_range_permissions;[exact Keep|exact FK]|];split;
       [eapply split_constants_readonly;[exact Ready|exact Preserve]|];split;[exact Keep|];split;[exact Preserve|].
       set (P:=fun b ofs=>Mem.valid_block m b /\ split_function_frame bk br1 br2 b ofs).
       assert (Frame:lframe P m mf).
       { eapply lframe_trans with (m2:=mp).
         - eapply lframe_implies;[exact FrameP|];unfold P,split_function_frame,split_entry_frame;intros;tauto.
         - eapply lframe_trans with (m2:=mb).
           + eapply lframe_implies;[exact FrameB|].
             intros b ofs [Valid Outside] ValidP;unfold split_arithmetic_frame.
             unfold split_function_frame in Outside;destruct Outside as (K & R1 & R2 & G1 & G2 & B1 & B2 & L).
             repeat split;try assumption;intro Eq;subst b;contradiction.
           + eapply lframe_implies;[exact FreeFrame|];intros b ofs [Valid Outside] ValidB.
             split;intro Eq;subst b;contradiction. }
       eapply lframe_implies;[exact Frame|];intros b ofs Outside Valid;split;[exact Valid|exact Outside].
Qed.
