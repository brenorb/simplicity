(** The two original square-root suffix calls at the affine-Y address. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_sx_state C.jet_sx_rep C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_square_affine_y C.jet_secp_square_affine_y_caller
 C.jet_secp_curve_square C.jet_secp_curve_square_caller
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_root_square_loop
 C.jet_secp_root_stage C.jet_secp_root_chain_owned C.jet_secp_root_call_state
 C.jet_secp_root_candidate_state C.jet_secp_fns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words.

Definition root_y_outside (br bs b : block) (pos : Z) := b<>bs /\ (b<>br \/ pos<40 \/ 80<=pos).
Lemma affine_y_square_outside br bs b pos : root_y_outside br bs b pos ->
 ~foot [(br,0);(bs,0)] (map rshape affine_y_square_regs) b pos.
Proof.
 intros [NS NR] (r & sh & d & ch & Nth & Cell & Block & Range).
 destruct r as [|[|r]].
 - injection Nth as <-;cbn [rshape fst snd affine_y_square_regs rcells map cshape In] in Cell.
   repeat destruct Cell as [Cell|Cell];try contradiction;injection Cell as <- <-;
    cbn [bas blk lay nth fst snd size_chunk] in Block,Range;destruct NR as [NR|[NR|NR]];congruence || lia.
 - apply NS;exact Block.
 - destruct r;discriminate Nth.
Qed.

Lemma curve_y_square_outside br bd b pos : root_y_outside br bd b pos ->
 ~foot [(bd,0);(br,0)] (map rshape (curve_square_regs true)) b pos.
Proof.
 intros [ND NR] (r & sh & d & ch & Nth & Cell & Block & Range).
 destruct r as [|[|r]].
 - apply ND;exact Block.
 - injection Nth as <-.
   cbn [rshape fst snd curve_square_regs curve_square_input curve_square_offset rcells u64_cells vars5 map cshape In] in Cell.
   repeat destruct Cell as [Cell|Cell];try contradiction;injection Cell as <- <-;
    cbn [bas blk lay nth fst snd size_chunk] in Block,Range;destruct NR as [NR|[NR|NR]];congruence || lia.
 - destruct r;discriminate Nth.
Qed.

Theorem exec_root_square_from_affine_y_state e le m s id bd br source w :
 root_locals_separated e -> root_locals_owned e m -> root_values_at e m s ->
 In id root_private_ids -> e!id=Some (bd,curve_fe_type) -> root_chain_frame e br 0 ->
 e!_secp256k1_fe_sqr=None -> typeof source=tptr curve_fe_type ->
 eval_expr secp_ge e le m source (Vptr br (Ptrofs.repr 40)) ->
 square_input_bounds w -> fe_at m br 40 (words5 w) -> Mem.range_perm m br 0 88 Cur Freeable ->
 exists mf, Clight2.exec_stmt secp_ge e le m (root_square_stmt id source) E0 le mf Out_normal /\
 root_locals_owned e mf /\ root_values_at e mf (PTree.set id (square_words w) s) /\
 fe_at mf br 40 (words5 w) /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe (root_y_outside br bd) m mf.
Proof.
 intros Sep Owned Store ID ED Outside EQ TS ES BW W FW.
 destruct (Owned id ID) as (bd' & ED' & FD);rewrite ED in ED';injection ED' as <-.
 assert (DR : bd<>br) by (intro HE;subst bd;exact (Outside id ID ED)).
 destruct (eval_curve_square_from_storage true w m bd br BW FD W FW DR)
  as (mf & Square & O & FO & S & FS & Val & BO & Frame0).
 assert (Frame : lframe (root_y_outside br bd) m mf).
 { eapply lframe_implies;[exact Frame0|];intros;apply curve_y_square_outside;assumption. }
 assert (OwnedF : root_locals_owned e mf).
 { intros j HJ;destruct (Pos.eq_dec j id) as [->|JD].
   - exists bd;split;assumption.
   - destruct (Owned j HJ) as (b & EB & FB);exists b;split;[exact EB|].
     eapply curve_keep_free;[lia|exact FB|exact Frame|];intros;split.
     + exact (Sep j id b bd HJ ID EB ED JD).
     + left;intro HE;subst b;exact (Outside j HJ EB). }
 assert (StoreF : root_values_at e mf (PTree.set id (square_words w) s)).
 { intros j v HV;destruct (Pos.eq_dec j id) as [->|JD].
   - rewrite PTree.gss in HV;injection HV as <-;split;[exact ID|].
     split;[intros i HI;pose proof (BO i HI);destruct (Nat.eqb i 4);lia|].
     exists bd;split;assumption.
   - rewrite PTree.gso in HV by exact JD.
     destruct (Store j v HV) as (HJ & BV & b & EB & V);split;[exact HJ|];split;[exact BV|].
     exists b;split;[exact EB|].
     eapply curve_keep_field_range;[reflexivity|exact V|exact Frame|];intros;split.
     + exact (Sep j id b bd HJ ID EB ED JD).
     + left;intro HE;subst b;exact (Outside j HJ EB). }
 exists mf;split.
 - unfold root_square_stmt;eapply exec_curve_call with
    (vargs:=[Vptr bd Ptrofs.zero;Vptr br (Ptrofs.repr 40)]) (v:=Vundef).
   + unfold secp_pure;repeat (first [left;reflexivity|right]).
   + exact EQ.
   + eapply eval_Econs;[apply eval_curve_local;exact ED|reflexivity|].
     eapply eval_Econs;[exact ES|rewrite TS;reflexivity|constructor].
   + exact Square.
 - split;[exact OwnedF|];split;[exact StoreF|];split;[exact S|];split;assumption.
Qed.

Theorem exec_root_square_out_affine_y_state e le m s id bs br dest w :
 root_locals_owned e m -> root_values_at e m s -> s!id=Some w -> e!id=Some (bs,curve_fe_type) ->
 root_chain_frame e br 0 -> e!_secp256k1_fe_sqr=None ->
 typeof dest=tptr curve_fe_type -> eval_expr secp_ge e le m dest (Vptr br (Ptrofs.repr 40)) ->
 Mem.range_perm m br 0 88 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (root_square_out_stmt dest id) E0 le mf Out_normal /\
 root_locals_owned e mf /\ root_values_at e mf s /\
 fe_at mf br 40 (words5 (square_words w)) /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe (root_y_outside br bs) m mf.
Proof.
 intros Owned Store SW ES Outside EQ TD ED FR.
 destruct (Store id w SW) as (ID & BW & bs' & ES' & W);rewrite ES in ES';injection ES' as <-.
 destruct (Owned id ID) as (bs' & ES' & FS);rewrite ES in ES';injection ES' as <-.
 assert (RS : br<>bs) by (intro HE;subst br;exact (Outside id ID ES)).
 destruct (eval_square_affine_y_from_storage w m br bs BW FR W FS RS)
  as (mf & Square & O & FO & S & FSO & Val & BO & Frame0).
 assert (Frame : lframe (root_y_outside br bs) m mf).
 { eapply lframe_implies;[exact Frame0|];intros;apply affine_y_square_outside;assumption. }
 assert (OwnedF : root_locals_owned e mf).
 { intros j HJ;destruct (Owned j HJ) as (b & EB & FB);exists b;split;[exact EB|].
   destruct (Pos.eq_dec b bs) as [->|NS];[exact FSO|].
   eapply curve_keep_free;[lia|exact FB|exact Frame|];intros;split;[exact NS|left].
   intro HE;subst b;exact (Outside j HJ EB). }
 assert (StoreF : root_values_at e mf s).
 { intros j v HV;destruct (Store j v HV) as (HJ & BV & b & EB & V);split;[exact HJ|];split;[exact BV|].
   exists b;split;[exact EB|];destruct (Pos.eq_dec b bs) as [->|NS].
   - rewrite (root_field_words_unique m bs v w V W);exact S.
   - eapply curve_keep_field_range;[reflexivity|exact V|exact Frame|];intros;split;[exact NS|left].
     intro HE;subst b;exact (Outside j HJ EB). }
 exists mf;split.
 - unfold root_square_out_stmt;eapply exec_curve_call with
    (vargs:=[Vptr br (Ptrofs.repr 40);Vptr bs Ptrofs.zero]) (v:=Vundef).
   + unfold secp_pure;repeat (first [left;reflexivity|right]).
   + exact EQ.
   + eapply eval_Econs;[exact ED|rewrite TD;reflexivity|].
     eapply eval_Econs;[apply eval_curve_local;exact ES|reflexivity|constructor].
   + exact Square.
 - split;[exact OwnedF|];split;[exact StoreF|];split;[exact O|];split;assumption.
Qed.
