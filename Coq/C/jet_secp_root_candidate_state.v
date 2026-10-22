(** In-place square blocks and the caller-owned result square used by the
    original square-root candidate suffix. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_square_separate_caller C.jet_secp_square_inplace_storage
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_root_square_loop
 C.jet_secp_root_stage C.jet_secp_root_chain_owned C.jet_secp_fns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words.

Lemma root_single_preserves e m mf s id bd out :
 root_locals_separated e -> root_locals_owned e m -> root_values_at e m s ->
 In id root_private_ids -> e!id=Some (bd,curve_fe_type) -> square_input_bounds out ->
 fe_at mf bd 0 (words5 out) -> Mem.range_perm mf bd 0 40 Cur Freeable ->
 lframe (fun b _=>b<>bd) m mf ->
 root_locals_owned e mf /\ root_values_at e mf (PTree.set id out s).
Proof.
 intros Sep Owned Store ID ED BO O FO Frame;split.
 - intros j HJ;destruct (Pos.eq_dec j id) as [->|JD].
   + exists bd;split;assumption.
   + destruct (Owned j HJ) as (b & EB & FB);exists b;split;[exact EB|].
     eapply curve_keep_free;[lia|exact FB|exact Frame|];intros;exact (Sep j id b bd HJ ID EB ED JD).
 - intros j w HW;destruct (Pos.eq_dec j id) as [->|JD].
   + rewrite PTree.gss in HW;injection HW as <-;split;[exact ID|];split;[exact BO|].
     exists bd;split;assumption.
   + rewrite PTree.gso in HW by exact JD.
     destruct (Store j w HW) as (HJ & BW & b & EB & W);split;[exact HJ|];split;[exact BW|].
     exists b;split;[exact EB|].
     eapply curve_keep_field_range;[reflexivity|exact W|exact Frame|];intros;exact (Sep j id b bd HJ ID EB ED JD).
Qed.

Theorem exec_root_squares_state n e le m s id bd w :
 Z.of_nat n<=88 -> root_locals_separated e -> root_locals_owned e m -> root_values_at e m s ->
 s!id=Some w -> e!id=Some (bd,curve_fe_type) -> e!_secp256k1_fe_sqr=None -> exists mf lef,
 Clight2.exec_stmt secp_ge e le m (root_square_for id (Z.of_nat n)) E0 lef mf Out_normal /\
 root_locals_owned e mf /\ root_values_at e mf (PTree.set id (root_square_words n w) s) /\
 (forall k,k<>_j -> lef!k=le!k) /\ lframe (fun b _=>b<>bd) m mf.
Proof.
 intros HN Sep Owned Store SW ED EQ.
 destruct (Store id w SW) as (ID & BW & bd' & ED' & W);rewrite ED in ED';injection ED' as <-.
 destruct (Owned id ID) as (bd' & ED' & FD);rewrite ED in ED';injection ED' as <-.
 destruct (exec_root_square_for_owned n id e le m bd w HN ED EQ BW W FD)
   as (mf & lef & Run & O & FO & BO & JF & Temps & Frame).
 destruct (root_single_preserves e m mf s id bd (root_square_words n w)
   Sep Owned Store ID ED BO O FO Frame) as [OwnedF StoreF].
 exists mf,lef;split;[exact Run|];split;[exact OwnedF|];split;[exact StoreF|];split;assumption.
Qed.

Theorem exec_root_inplace_square_state e le m s id bd w :
 root_locals_separated e -> root_locals_owned e m -> root_values_at e m s ->
 s!id=Some w -> e!id=Some (bd,curve_fe_type) -> e!_secp256k1_fe_sqr=None -> exists mf,
 Clight2.exec_stmt secp_ge e le m (root_square_call id) E0 le mf Out_normal /\
 root_locals_owned e mf /\ root_values_at e mf (PTree.set id (square_words w) s) /\
 lframe (fun b _=>b<>bd) m mf.
Proof.
 intros Sep Owned Store SW ED EQ.
 destruct (Store id w SW) as (ID & BW & bd' & ED' & W);rewrite ED in ED';injection ED' as <-.
 destruct (Owned id ID) as (bd' & ED' & FD);rewrite ED in ED';injection ED' as <-.
 destruct (exec_root_square_owned e le m id bd w ED EQ BW W FD) as (mf & Run & O & FO & BO & Frame).
 destruct (root_single_preserves e m mf s id bd (square_words w)
   Sep Owned Store ID ED BO O FO Frame) as [OwnedF StoreF].
 exists mf;split;[exact Run|];split;[exact OwnedF|];split;assumption.
Qed.

Definition root_square_out_stmt dest id := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
 [dest;curve_local_address id].
Theorem exec_root_square_out_state e le m s id bs br dest w :
 root_locals_owned e m -> root_values_at e m s -> s!id=Some w -> e!id=Some (bs,curve_fe_type) ->
 root_chain_frame e br 0 -> e!_secp256k1_fe_sqr=None ->
 typeof dest=tptr curve_fe_type -> eval_expr secp_ge e le m dest (Vptr br Ptrofs.zero) ->
 Mem.range_perm m br 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (root_square_out_stmt dest id) E0 le mf Out_normal /\
 root_locals_owned e mf /\ root_values_at e mf s /\
 fe_at mf br 0 (words5 (square_words w)) /\ Mem.range_perm mf br 0 40 Cur Freeable /\
 lframe (fun b _=>b<>br /\ b<>bs) m mf.
Proof.
 intros Owned Store SW ES Outside EQ TD ED FR.
 destruct (Store id w SW) as (ID & BW & bs' & ES' & W);rewrite ES in ES';injection ES' as <-.
 destruct (Owned id ID) as (bs' & ES' & FS);rewrite ES in ES';injection ES' as <-.
 assert (RS : br<>bs) by (intro HE;subst br;exact (Outside id ID ES)).
 destruct (eval_square_separate_from_storage w m br bs BW FR W FS RS)
   as (mf & Square & O & FO & S & FSO & Val & BO & Frame).
 assert (OwnedF : root_locals_owned e mf).
 { intros j HJ;destruct (Owned j HJ) as (b & EB & FB);exists b;split;[exact EB|].
   destruct (Pos.eq_dec b bs) as [->|NS];[exact FSO|].
   eapply curve_keep_free;[lia|exact FB|exact Frame|];intros;split;[|exact NS].
   intro HE;subst b;exact (Outside j HJ EB). }
 assert (StoreF : root_values_at e mf s).
 { intros j v HV;destruct (Store j v HV) as (HJ & BV & b & EB & V);split;[exact HJ|];split;[exact BV|].
   exists b;split;[exact EB|];destruct (Pos.eq_dec b bs) as [->|NS].
   - rewrite (root_field_words_unique m bs v w V W);exact S.
   - eapply curve_keep_field_range;[reflexivity|exact V|exact Frame|];intros;split;[|exact NS].
     intro HE;subst b;exact (Outside j HJ EB). }
 exists mf;split.
 - unfold root_square_out_stmt;eapply exec_curve_call with (vargs:=[Vptr br Ptrofs.zero;Vptr bs Ptrofs.zero]) (v:=Vundef).
   + unfold secp_pure;repeat (first [left;reflexivity|right]).
   + exact EQ.
   + eapply eval_Econs;[exact ED|rewrite TD;reflexivity|].
     eapply eval_Econs;[apply eval_curve_local;exact ES|reflexivity|constructor].
   + exact Square.
 - split;[exact OwnedF|];split;[exact StoreF|];split;[exact O|];split;assumption.
Qed.
