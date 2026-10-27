(** All original statements after scalar_mul_512: quotient settings, four
    stores, bit-383 load and actual conditional-add call. The product array
    is an incoming representation, to be supplied by the existing full-product
    call when composing the enclosing function. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix
 C.jet_secp_scalar_shift384_control C.jet_secp_scalar_shift384_copy C.jet_secp_scalar_shift384_stores
 C.jet_secp_scalar_shift384_round C.jet_secp_scalar_shift384_numeric C.jet_secp_scalar_cadd_numeric
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage C.jet_clight_internal_permissions.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition shift384_suffix := statement_sequence (firstn 3 (skipn 2 (fst shift384_parts)))
 (statement_sequence (map shift384_copy_statement (seq 0 4))
 (Ssequence shift384_round_load shift384_round_call)).
Lemma shift384_suffix_source : fn_body f_secp256k1_scalar_mul_shift_var=
 Ssequence (Sloop Sskip Sbreak) (Ssequence shift384_product_statement shift384_suffix).
Proof. reflexivity. Qed.

Theorem exec_shift384_suffix w e le m br bl : br<>bl ->
 e!_l=Some (bl,tarray tulong 8) -> e!_secp256k1_scalar_cadd_bit=None ->
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_shift=Some (Vint (Int.repr 384)) ->
 shift384_product w bl m -> Mem.range_perm m br 0 32 Cur Freeable ->
 exists le' mf,Clight2.exec_stmt secp_ge e le m shift384_suffix E0 le' mf Out_normal /\
 scalar_at mf br 0 (map Int64.repr (scalar_limbs_of ((shift384_product_value w+2^383)/2^384))) /\
 shift384_product w bl mf /\ Mem.range_perm mf br 0 32 Cur Freeable /\
 keeps_permissions m mf /\ lframe (fun b _=>b<>br) m mf.
Proof.
 intros Separate Local Global R Shift Product Free.
 assert (Settings:shift384_fixed (shift384_settings_temps le) br).
 { unfold shift384_fixed,shift384_settings_temps;repeat split;
   repeat rewrite PTree.gso by discriminate;first [assumption|apply PTree.gss]. }
 destruct (exec_shift384_copies w e (shift384_settings_temps le) m br bl
  Separate Local Settings Product Free) as (lc & mc & Copies & Fixed & Copied & ProductC & FreeC & KeepC & FrameC).
 destruct Fixed as (RC & ShiftC & LowC & LimbsC).
 assert (Load:Mem.load Mint64 mc bl 40=Some (Vlong (w 5%nat))) by exact (ProductC 5%nat ltac:(lia)).
 assert (Stored:scalar_at mc br 0 (map Int64.repr (scalar_limbs_of (shift384_quotient w)))).
 { rewrite shift384_quotient_limbs;exact Copied. }
 destruct (eval_scalar_cadd_value (shift384_quotient w) (shift384_round_flag (w 5%nat)) mc br
  ltac:(pose proof (shift384_quotient_bounds w);lia) Stored FreeC)
  as (mf & Call & Output & Free' & Keep' & Readonly & Frame').
 assert (Rounded:scalar_at mf br 0
  (map Int64.repr (scalar_limbs_of ((shift384_product_value w+2^383)/2^384)))).
 { rewrite shift384_rounded_value in Output.
   rewrite Z.mod_small in Output;[exact Output|pose proof (shift384_rounded_bounds w);lia]. }
 assert (Valid:Mem.valid_block mc bl).
 { eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
   [eapply Mem.load_valid_access;exact Load|constructor]. }
 assert (ProductF:shift384_product w bl mf).
 { intros j J;rewrite (proj1 Frame' Mint64 bl (8*Z.of_nat j) Valid);
   [apply ProductC;exact J|intros;congruence]. }
 set (lr:=PTree.set _t'11 (Vlong (w 5%nat)) lc).
 exists lr,mf;split.
 - unfold shift384_suffix;eapply exec_statement_prefix_then_last.
   + apply exec_shift384_settings;exact Shift.
   + eapply exec_statement_prefix_then_last;[exact Copies|].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=lr).
     * apply (exec_shift384_round_load e lc mc bl (w 5%nat));assumption.
     * eapply exec_shift384_round_call with (word:=w 5%nat).
       -- exact Global.
       -- unfold lr;rewrite PTree.gso by discriminate;exact RC.
       -- unfold lr;rewrite PTree.gso by discriminate;exact ShiftC.
       -- unfold lr;apply PTree.gss.
       -- exact Call.
 - split;[exact Rounded|];split;[exact ProductF|];split;[exact Free'|];split.
   + intros b pos k p Perm;apply Keep',KeepC;exact Perm.
   + eapply lframe_trans;[exact FrameC|exact Frame'].
Qed.
