(** Actual scalar_split_lambda entry and its first two calls. Both coefficient
    objects are freshly allocated by the original function entry. Their exact
    literal values and ownership are established, not caller premises. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_split_multipliers
 C.jet_secp_split_rounding_calls C.jet_secp_split_round_literal C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_add_reader_support
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge split_multiplier_block.

Definition split_entry_temps v1 v2 bk := PTree.set _k (Vptr bk Ptrofs.zero)
 (PTree.set _r2 v2 (PTree.set _r1 v1 (PTree.empty val))).
Definition split_entry_frame bk b (_:Z) := b<>bk /\ b<>split_multiplier_block true /\ b<>split_multiplier_block false.

Lemma split_function_entry v1 v2 bk m ma mi bc1 bc2 :
 Mem.alloc m 0 32=(ma,bc1) -> Mem.alloc ma 0 32=(mi,bc2) ->
 function_entry2 secp_ge f_secp256k1_scalar_split_lambda [v1;v2;Vptr bk Ptrofs.zero]
  m (split_local_env bc1 bc2) (split_entry_temps v1 v2 bk) mi.
Proof.
 intros Alloc1 Alloc2;assert (Ok:fn_okb f_secp256k1_scalar_split_lambda=true) by reflexivity.
 destruct (fn_okb_true _ Ok) as (Vars & Params & Disjoint).
 constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
 eapply alloc_variables_cons with (m1:=ma) (b1:=bc1);[exact Alloc1|].
 eapply alloc_variables_cons with (m1:=mi) (b1:=bc2);[exact Alloc2|constructor].
Qed.

Theorem scalar_split_entry_rounding (k:Ty.tySem (Word 8)) v1 v2 bk m :
 split_multipliers_ready m ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k))) ->
 Mem.range_perm m bk 0 32 Cur Freeable ->
 exists bc1 bc2 mi mf,
 function_entry2 secp_ge f_secp256k1_scalar_split_lambda [v1;v2;Vptr bk Ptrofs.zero]
  m (split_local_env bc1 bc2) (split_entry_temps v1 v2 bk) mi /\
 Clight2.exec_stmt secp_ge (split_local_env bc1 bc2) (split_entry_temps v1 v2 bk) mi
  split_rounding_prefix E0 (split_entry_temps v1 v2 bk) mf Out_normal /\
 scalar_at mf bc1 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (@literal_split_coefficient true Alg.CoreFunSem k)))) /\
 scalar_at mf bc2 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (@literal_split_coefficient false Alg.CoreFunSem k)))) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k))) /\
 Mem.range_perm mf bc1 0 32 Cur Freeable /\ Mem.range_perm mf bc2 0 32 Cur Freeable /\
 Mem.range_perm mf bk 0 32 Cur Freeable /\ split_multipliers_ready mf /\
 bc1<>bc2 /\ bc1<>bk /\ bc2<>bk /\ ~Mem.valid_block m bc1 /\ ~Mem.valid_block m bc2 /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (split_entry_frame bk) m mf.
Proof.
 intros Ready Input FK;destruct (Mem.alloc m 0 32) as (ma & bc1) eqn:Alloc1.
 destruct (Mem.alloc ma 0 32) as (mi & bc2) eqn:Alloc2.
 assert (Frame1:lframe (fun _ _=>True) m ma) by (apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc1).
 assert (Frame2:lframe (fun _ _=>True) ma mi) by (apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc2).
 assert (FrameI:lframe (fun _ _=>True) m mi) by (eapply lframe_trans;[exact Frame1|exact Frame2]).
 assert (PreserveI:readonly_preserved m mi) by
  (eapply preserved_trans;[eapply alloc_preserved;exact Alloc1|eapply alloc_preserved;exact Alloc2]).
 assert (ReadyI:split_multipliers_ready mi) by (eapply split_multipliers_readonly;[exact Ready|exact PreserveI]).
 assert (InputI:scalar_at mi bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k)))).
 { eapply scalar_at_lframe;[exact Input|exact FrameI|intros;exact I]. }
 assert (FKI:Mem.range_perm mi bk 0 32 Cur Freeable).
 { intros pos Range;eapply Mem.perm_alloc_1;[exact Alloc2|];eapply Mem.perm_alloc_1;[exact Alloc1|apply FK;exact Range]. }
 assert (F1:Mem.range_perm mi bc1 0 32 Cur Freeable).
 { intros pos Range;eapply Mem.perm_alloc_1;[exact Alloc2|eapply Mem.perm_alloc_2;[exact Alloc1|exact Range]]. }
 assert (F2:Mem.range_perm mi bc2 0 32 Cur Freeable) by (intros pos Range;eapply Mem.perm_alloc_2;[exact Alloc2|exact Range]).
 assert (Fresh1:~Mem.valid_block m bc1) by (eapply Mem.fresh_block_alloc;exact Alloc1).
 assert (Fresh2A:~Mem.valid_block ma bc2) by (eapply Mem.fresh_block_alloc;exact Alloc2).
 assert (Fresh2:~Mem.valid_block m bc2) by (intro Valid;apply Fresh2A;exact (proj2 (proj2 Frame1) bc2 Valid)).
 assert (VK:Mem.valid_block m bk) by (eapply Mem.perm_valid_block;apply (FK 0);lia).
 assert (C1K:bc1<>bk) by (intro Eq;apply Fresh1;rewrite Eq;exact VK).
 assert (C2K:bc2<>bk) by (intro Eq;apply Fresh2;rewrite Eq;exact VK).
 assert (Separate:bc1<>bc2) by (intro Eq;apply Fresh2A;rewrite <-Eq;eapply Mem.valid_new_block;exact Alloc1).
 destruct (exec_split_rounding_prefix k (split_entry_temps v1 v2 bk) mi bk bc1 bc2 ReadyI eq_refl
  InputI FKI F1 F2 Separate C1K C2K) as (mf & Run & Out1 & Out2 & InputF & F1F & F2F & FKF & ReadyF & KeepF & PreserveF & FrameF).
 exists bc1,bc2,mi,mf;split;[eapply split_function_entry;[exact Alloc1|exact Alloc2]|].
 split;[exact Run|];split;[exact Out1|];split;[exact Out2|];split;[exact InputF|];split;[exact F1F|];
 split;[exact F2F|];split;[exact FKF|];split;[exact ReadyF|];split;[exact Separate|];split;[exact C1K|];
 split;[exact C2K|];split;[exact Fresh1|];split;[exact Fresh2|];split.
 - intros b pos kind perm Perm;apply KeepF;eapply Mem.perm_alloc_1;[exact Alloc2|];
   eapply Mem.perm_alloc_1;[exact Alloc1|exact Perm].
 - split;[eapply preserved_trans;[exact PreserveI|exact PreserveF]|].
   set (P:=fun b ofs=>Mem.valid_block m b /\ split_entry_frame bk b ofs).
   assert (Frame:lframe P m mf).
   { eapply lframe_trans with (m2:=mi).
     - eapply lframe_implies;[exact FrameI|];intros;exact I.
     - eapply lframe_implies;[exact FrameF|];intros b ofs [Valid Outside] ValidI.
       destruct Outside as (NotK & NotG1 & NotG2);unfold split_rounding_frame;repeat split;try assumption;
       intro Eq;subst b;contradiction. }
   eapply lframe_implies;[exact Frame|];intros b ofs Outside Valid;split;[exact Valid|exact Outside].
Qed.
