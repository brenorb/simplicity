(** Original separate-square and in-place-multiply calls updating the square-root
    helper's private-field invariant. Sources remain readable and owned. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_square_separate_caller C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_root_stage C.jet_secp_root_chain_owned C.jet_secp_field_pair_multiply C.jet_secp_fns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words field_pair_product.

Lemma root_call_preserves e m mf s id bd bs source out :
 root_locals_separated e -> root_locals_owned e m -> root_values_at e m s ->
 In id root_private_ids -> e!id=Some (bd,curve_fe_type) -> square_input_bounds out ->
 fe_at mf bd 0 (words5 out) -> Mem.range_perm mf bd 0 40 Cur Freeable ->
 fe_at m bs 0 (words5 source) -> fe_at mf bs 0 (words5 source) -> Mem.range_perm mf bs 0 40 Cur Freeable ->
 lframe (fun b _=>b<>bd /\ b<>bs) m mf ->
 root_locals_owned e mf /\ root_values_at e mf (PTree.set id out s).
Proof.
 intros Sep Owned Store ID ED BO O FO S SF FS Frame;split.
 - intros j HJ;destruct (Pos.eq_dec j id) as [->|JD].
   + exists bd;split;assumption.
   + destruct (Owned j HJ) as (b & EB & FB);exists b;split;[exact EB|].
     destruct (Pos.eq_dec b bs) as [->|BS];[exact FS|].
     eapply curve_keep_free;[lia|exact FB|exact Frame|];intros;split;
       [exact (Sep j id b bd HJ ID EB ED JD)|exact BS].
 - intros j w HW;destruct (Pos.eq_dec j id) as [->|JD].
   + rewrite PTree.gss in HW;injection HW as <-;split;[exact ID|];split;[exact BO|].
     exists bd;split;assumption.
   + rewrite PTree.gso in HW by exact JD.
     destruct (Store j w HW) as (HJ & BW & b & EB & W);split;[exact HJ|];split;[exact BW|].
     exists b;split;[exact EB|];destruct (Pos.eq_dec b bs) as [->|BS].
     * rewrite (root_field_words_unique m bs w source W S);exact SF.
     * eapply curve_keep_field_range;[reflexivity|exact W|exact Frame|];intros;split;
         [exact (Sep j id b bd HJ ID EB ED JD)|exact BS].
Qed.

Definition root_square_stmt dst source := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
 [curve_local_address dst;source].
Definition root_multiply_stmt dst source := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [curve_local_address dst;curve_local_address dst;source].

Theorem exec_root_square_state e le m s id bd bs source w :
 root_locals_separated e -> root_locals_owned e m -> root_values_at e m s ->
 In id root_private_ids -> e!id=Some (bd,curve_fe_type) -> e!_secp256k1_fe_sqr=None ->
 typeof source=tptr curve_fe_type -> eval_expr secp_ge e le m source (Vptr bs Ptrofs.zero) ->
 bd<>bs -> square_input_bounds w -> fe_at m bs 0 (words5 w) -> Mem.range_perm m bs 0 40 Cur Freeable ->
 exists mf, Clight2.exec_stmt secp_ge e le m (root_square_stmt id source) E0 le mf Out_normal /\
 root_locals_owned e mf /\ root_values_at e mf (PTree.set id (square_words w) s) /\
 fe_at mf bs 0 (words5 w) /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
 lframe (fun b _=>b<>bd /\ b<>bs) m mf.
Proof.
 intros Sep Owned Store ID ED EQ TS ES DS BW W FW.
 destruct (Owned id ID) as (bd' & ED' & FD);rewrite ED in ED';injection ED' as <-.
 destruct (eval_square_separate_from_storage w m bd bs BW FD W FW DS)
   as (mf & Square & O & FO & S & FS & Val & BO & Frame).
 destruct (root_call_preserves e m mf s id bd bs w (square_words w)
   Sep Owned Store ID ED BO O FO W S FS Frame) as [OwnedF StoreF].
 exists mf;split.
 - unfold root_square_stmt;eapply exec_curve_call with (vargs:=[Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero]) (v:=Vundef).
   + unfold secp_pure;repeat (first [left;reflexivity|right]).
   + exact EQ.
   + eapply eval_Econs;[apply eval_curve_local;exact ED|reflexivity|].
     eapply eval_Econs;[exact ES|rewrite TS;reflexivity|constructor].
   + exact Square.
 - split;[exact OwnedF|];split;[exact StoreF|];split;[exact S|];split;assumption.
Qed.

Theorem exec_root_multiply_state e le m s id bd bs source w v :
 root_locals_separated e -> root_locals_owned e m -> root_values_at e m s ->
 In id root_private_ids -> e!id=Some (bd,curve_fe_type) -> e!_secp256k1_fe_mul=None ->
 typeof source=tptr curve_fe_type -> eval_expr secp_ge e le m source (Vptr bs Ptrofs.zero) ->
 bd<>bs -> s!id=Some w -> square_input_bounds v ->
 fe_at m bs 0 (words5 v) -> Mem.range_perm m bs 0 40 Cur Freeable ->
 exists mf, Clight2.exec_stmt secp_ge e le m (root_multiply_stmt id source) E0 le mf Out_normal /\
 root_locals_owned e mf /\ root_values_at e mf (PTree.set id (field_pair_product w v) s) /\
 fe_at mf bs 0 (words5 v) /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
 lframe (fun b _=>b<>bd /\ b<>bs) m mf.
Proof.
 intros Sep Owned Store ID ED EM TS ES DS SW BV V FV.
 destruct (Store id w SW) as (_ & BW & bd' & ED' & W);rewrite ED in ED';injection ED' as <-.
 destruct (Owned id ID) as (bd' & ED' & FD);rewrite ED in ED';injection ED' as <-.
 destruct (eval_field_pair_multiply w v m bd bs BW BV DS W V FD FV)
   as (mf & Multiply & O & S & FO & FS & Val & BO & Tight & Frame).
 destruct (root_call_preserves e m mf s id bd bs v (field_pair_product w v)
   Sep Owned Store ID ED BO O FO V S FS Frame) as [OwnedF StoreF].
 exists mf;split.
 - unfold root_multiply_stmt;eapply exec_curve_call with
   (vargs:=[Vptr bd Ptrofs.zero;Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero]) (v:=Vundef).
   + unfold secp_pure;repeat (first [left;reflexivity|right]).
   + exact EM.
   + eapply eval_Econs;[apply eval_curve_local;exact ED|reflexivity|].
     eapply eval_Econs;[apply eval_curve_local;exact ED|reflexivity|].
     eapply eval_Econs;[exact ES|rewrite TS;reflexivity|constructor].
   + exact Multiply.
 - split;[exact OwnedF|];split;[exact StoreF|];split;[exact S|];split;assumption.
Qed.
