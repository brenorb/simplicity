(** Entire original affine-to-native-storage function, including both frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_curve_statements C.jet_secp_field_read_preservation C.jet_secp_curve_frame C.jet_secp_fe_nv
 C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_affine_storage C.jet_secp_table_decode C.jet_secp_storage_numeric C.jet_secp_fe_inv_prefix
 C.jet_clight_internal_preserve C.jet_clight_internal_permissions C.jet_secp_ge_storage_body.
Require Import C.jet_secp_ge_storage_entry.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Theorem eval_ge_to_storage_owned wx wy m bin bout:
 square_input_bounds wx ->square_input_bounds wy ->
 fe_at m bin 0 (words5 wx) ->fe_at m bin 40 (words5 wy) ->
 Mem.range_perm m bout 0 64 Cur Freeable ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_to_storage)
 [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
 affine_storage_readable mf bout 0 (ge_storage_words wx wy) /\
 field_storage_value (ge_storage_words wx wy)=fe_inv_value wx /\
 field_storage_value (fun i=>ge_storage_words wx wy (4+i)%nat)=fe_inv_value wy /\
 Mem.range_perm mf bout 0 64 Cur Freeable /\lframe (fun b _=>b<>bout) m mf /\readonly_preserved m mf.
Proof.
 intros BoundsX BoundsY InputX InputY Free.
 assert (VO:Mem.valid_block m bout) by (eapply Mem.perm_valid_block;apply (Free 0);lia).
 assert (VI:Mem.valid_block m bin).
 { destruct InputX as (_ & _ & _ & Perm & _);eapply Mem.perm_valid_block;apply (Perm 0);lia. }
 destruct (ge_storage_entry_owned m (Vptr bout Ptrofs.zero) (Vptr bin Ptrofs.zero))
 as (mi & bx & b_y & Entry & Separate & Fresh & OwnedI & FrameI & KeepI & ReadI).
 assert (InputsI:(fe_at mi bin 0 (words5 wx)) /\ (fe_at mi bin 40 (words5 wy))).
 { split;eapply field_at_lframe;[exact InputX|exact FrameI|intros;exact I|
  exact InputY|exact FrameI|intros;exact I]. }
 destruct InputsI as [XI YI].
 assert (OutFresh:~In bout [bx;b_y]) by (apply Fresh;exact VO).
 assert (SourceFresh:~In bin [bx;b_y]) by (apply Fresh;exact VI).
 assert (AllSeparate:NoDup [bout;bx;b_y]) by (constructor;assumption).
 assert (OwnedAll:forall b hi,In (b,hi) [(bout,64);(bx,40);(b_y,40)] ->Mem.range_perm mi b 0 hi Cur Freeable).
 { intros b hi [Same|Slot].
   - inversion Same;subst b hi;intros pos Range;apply KeepI,Free;exact Range.
   - assert (Size:hi=40) by (clear -Slot;cbn [In] in Slot;intuition congruence);subst hi.
     apply OwnedI;clear -Slot;cbn [In] in *;intuition congruence. }
 destruct (exec_ge_to_storage_body wx wy (ge_storage_env bx b_y)
  (ge_storage_temps (Vptr bout Ptrofs.zero) (Vptr bin Ptrofs.zero)) mi bin bout bx b_y
  eq_refl eq_refl eq_refl eq_refl (ge_storage_plain bx b_y) eq_refl eq_refl
  ltac:(intro Same;apply SourceFresh;left;congruence)
  ltac:(intro Same;apply SourceFresh;right;left;congruence) AllSeparate BoundsX BoundsY XI YI OwnedAll)
 as (mb & Body & Storage & OwnedB & FrameB & ReadB).
 destruct (free_list_exists [(b_y,0,40);(bx,0,40)] mb) as (mf & Frees & UnchangedF).
 - clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;
   repeat constructor;cbn;intuition congruence.
 - intros b lo hi Slot;cbn [In] in Slot;repeat destruct Slot as [Slot|Slot];
   try contradiction;inversion Slot;subst b lo hi;apply OwnedB;clear;cbn [In];tauto.
 - assert (FrameF:lframe (fun b _=>~In b [bx;b_y]) mb mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact UnchangedF|].
     intros b pos Outside _;clear -Outside;cbn [map fst In] in *;tauto. }
   assert (StorageF:affine_storage_readable mf bout 0 (ge_storage_words wx wy)).
   { eapply affine_storage_readable_lframe;[exact Storage|exact FrameF|intros;exact OutFresh]. }
   assert (FreeF:Mem.range_perm mf bout 0 64 Cur Freeable).
   { eapply curve_keep_free;[lia|apply OwnedB;clear;cbn [In];tauto|exact FrameF|intros;exact OutFresh]. }
   exists mf;split.
   + eapply eval_funcall_internal with (e:=ge_storage_env bx b_y)
     (le1:=ge_storage_temps (Vptr bout Ptrofs.zero) (Vptr bin Ptrofs.zero))
     (le2:=ge_storage_temps (Vptr bout Ptrofs.zero) (Vptr bin Ptrofs.zero))
     (m1:=mi) (m2:=mb) (out:=Out_normal).
     * exact Entry.
     * exact Body.
     * reflexivity.
     * rewrite ge_storage_blocks;exact Frees.
   + split;[exact StorageF|].
     destruct (ge_storage_words_values wx wy) as [ValueX ValueY].
     split;[exact ValueX|];split;[exact ValueY|];split;[exact FreeF|];split.
     * eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\b<>bout).
       { eapply lframe_trans.
         - eapply lframe_implies;[exact FrameI|intros;exact I].
         - eapply lframe_trans.
           + eapply lframe_implies;[exact FrameB|].
             intros b pos [Valid Outside] _;split;[exact Outside|];split;
             intro Same;apply (Fresh b Valid);rewrite Same;cbn [In];tauto.
           + eapply lframe_implies;[exact FrameF|].
             intros b pos [Valid _] _;apply Fresh;exact Valid. }
       intros b pos Outside Valid;split;assumption.
     * eapply preserved_trans;[exact ReadI|];eapply preserved_trans;[exact ReadB|].
       eapply freelist_preserved;exact Frees.
Qed.
