(** Whole original gej_double on distinct owned points, including its three
    actual local allocations, flag copy, arithmetic, void result and frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_double_statements C.jet_secp_double_function C.jet_secp_double_separate_body
 C.jet_secp_double_separate_tail C.jet_secp_double_all_calls C.jet_secp_square_columns
 C.jet_secp_multiply_normalize_bridge C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_closed_helpers C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition double_separate_entry_temps br ba := PTree.set _a (Vptr ba Ptrofs.zero)
 (PTree.set _r (Vptr br Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_gej_double))).

Local Ltac allocated_valid := first [assumption |
 match goal with A:Mem.alloc _ _ _=(?mm,?bb) |- Mem.valid_block ?mm ?bb =>
  eapply Mem.valid_new_block;exact A end |
 match goal with A:Mem.alloc _ _ _=(?mm,_) |- Mem.valid_block ?mm _ =>
  eapply Mem.valid_block_alloc;[exact A|allocated_valid] end].
Local Ltac allocated_distinct := first [assumption |
 match goal with A:Mem.alloc _ _ _=(_,?bb) |- ?ba<>?bb =>
  let Eq:=fresh "Eq" in intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ A);
   rewrite <-Eq;allocated_valid end |
 match goal with A:Mem.alloc _ _ _=(_,?ba) |- ?ba<>?bb =>
  let Eq:=fresh "Eq" in intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ A);
   rewrite Eq;allocated_valid end].

Theorem eval_double_separate_function x y z m br ba flag :
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> br<>ba ->
 Mem.load Mint32 m ba 120=Some (Vint flag) ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_double)
  [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 (double_output_x_words x y)) /\
 fe_at mf br 40 (words5 (double_output_y_words x y)) /\
 fe_at mf br 80 (words5 (double_output_z_words y z)) /\
 Mem.load Mint32 mf br 120=Some (Vint flag) /\ Mem.load Mint32 mf ba 120=Some (Vint flag) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 square_input_bounds (double_output_x_words x y) /\
 square_input_bounds (double_output_y_words x y) /\
 square_input_bounds (double_output_z_words y z) /\
 lframe (fun b pos=>(b<>br \/ pos<0 \/ 124<=pos) /\ (b<>ba \/ pos<0 \/ 120<=pos)) m mf /\
 readonly_preserved m mf.
Proof.
 intros BX BY BZ RA Flag X Y ZAt RF AF.
 assert (RV:Mem.valid_block m br) by (eapply Mem.perm_valid_block;exact (RF 0 ltac:(lia))).
 assert (AV:Mem.valid_block m ba) by (eapply Mem.perm_valid_block;exact (AF 0 ltac:(lia))).
 destruct (Mem.alloc m 0 40) as [ml bl] eqn:AL.
 destruct (Mem.alloc ml 0 40) as [ms bs] eqn:AS.
 destruct (Mem.alloc ms 0 40) as [mi bt] eqn:AT.
 assert (Old:forall b,Mem.valid_block m b -> b<>bl /\ b<>bs /\ b<>bt).
 { intros b Valid;repeat split;allocated_distinct. }
 destruct (Old br RV) as (RL & RS & RT).
 destruct (Old ba AV) as (APL & APS & APT).
 assert (LS:bl<>bs) by allocated_distinct.
 assert (LT:bl<>bt) by allocated_distinct.
 assert (ST:bs<>bt) by allocated_distinct.
 assert (FAlloc:lframe (fun _ _=>True) m mi).
 { eapply lframe_trans.
   - apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact AL.
   - eapply lframe_trans;apply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption. }
 assert (XI:fe_at mi ba 0 (words5 x)) by (eapply field_at_lframe;[exact X|exact FAlloc|];intros;exact I).
 assert (YI:fe_at mi ba 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact FAlloc|];intros;exact I).
 assert (ZI:fe_at mi ba 80 (words5 z)) by (eapply field_at_lframe;[exact ZAt|exact FAlloc|];intros;exact I).
 assert (RFI:Mem.range_perm mi br 0 128 Cur Freeable) by
   (eapply curve_keep_free;[lia|exact RF|exact FAlloc|];intros;exact I).
 assert (AFI:Mem.range_perm mi ba 0 128 Cur Freeable) by
   (eapply curve_keep_free;[lia|exact AF|exact FAlloc|];intros;exact I).
 assert (FI:Mem.load Mint32 mi ba 120=Some (Vint flag)) by
   (rewrite (proj1 FAlloc Mint32 ba 120 AV ltac:(intros;exact I));exact Flag).
 assert (LFI:Mem.range_perm mi bl 0 40 Cur Freeable).
 { intros pos Range;eapply Mem.perm_alloc_1;[exact AT|].
   eapply Mem.perm_alloc_1;[exact AS|];eapply Mem.perm_alloc_2;[exact AL|exact Range]. }
 assert (SFI:Mem.range_perm mi bs 0 40 Cur Freeable).
 { intros pos Range;eapply Mem.perm_alloc_1;[exact AT|];eapply Mem.perm_alloc_2;[exact AS|exact Range]. }
 assert (TFI:Mem.range_perm mi bt 0 40 Cur Freeable) by
   (intros pos Range;eapply Mem.perm_alloc_2;[exact AT|exact Range]).
 set (le:=double_separate_entry_temps br ba).
 destruct (exec_double_separate_body le x y z mi br ba bs bl bt flag
   eq_refl eq_refl BX BY BZ RA RS RL RT APS APL APT (not_eq_sym LS) ST LT
   FI XI YI ZI RFI AFI SFI LFI TFI)
  as (mo & Body & RXO & RYO & RZO & RFlag & AFlag & AXO & AYO & AZO &
      RFO & AFO & SFO & LFO & TFO & BXF & BYF & BZF & FBody).
 destruct (free_list_exists [(bs,0,40);(bl,0,40);(bt,0,40)] mo) as (mf & Free & Unchanged).
 - cbn;repeat constructor;cbn;intuition congruence.
 - intros b lo hi [Slot|[Slot|[Slot|Slot]]];try contradiction;inversion Slot;subst;assumption.
 - assert (FFree:lframe (fun b _=>b<>bl /\ b<>bs /\ b<>bt) mo mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
     intros b pos (NL & NS & NT) Valid;cbn;intuition congruence. }
   assert (RXF:fe_at mf br 0 (words5 (double_output_x_words x y))) by
    (eapply field_at_lframe;[exact RXO|exact FFree|];intros;repeat split;assumption).
   assert (RYF:fe_at mf br 40 (words5 (double_output_y_words x y))) by
    (eapply field_at_lframe;[exact RYO|exact FFree|];intros;repeat split;assumption).
   assert (RZF:fe_at mf br 80 (words5 (double_output_z_words y z))) by
    (eapply field_at_lframe;[exact RZO|exact FFree|];intros;repeat split;assumption).
   assert (AXF:fe_at mf ba 0 (words5 x)) by
    (eapply field_at_lframe;[exact AXO|exact FFree|];intros;repeat split;assumption).
   assert (AYF:fe_at mf ba 40 (words5 y)) by
    (eapply field_at_lframe;[exact AYO|exact FFree|];intros;repeat split;assumption).
   assert (AZF:fe_at mf ba 80 (words5 z)) by
    (eapply field_at_lframe;[exact AZO|exact FFree|];intros;repeat split;assumption).
   assert (RFF:Mem.range_perm mf br 0 128 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact RFO|exact FFree|];intros;repeat split;assumption).
   assert (AFF:Mem.range_perm mf ba 0 128 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact AFO|exact FFree|];intros;repeat split;assumption).
   assert (RVO:Mem.valid_block mo br) by (eapply Mem.perm_valid_block;exact (RFO 0 ltac:(lia))).
   assert (AVO:Mem.valid_block mo ba) by (eapply Mem.perm_valid_block;exact (AFO 0 ltac:(lia))).
   assert (RFlagF:Mem.load Mint32 mf br 120=Some (Vint flag)) by
    (rewrite (proj1 FFree Mint32 br 120 RVO ltac:(intros;repeat split;assumption));exact RFlag).
   assert (AFlagF:Mem.load Mint32 mf ba 120=Some (Vint flag)) by
    (rewrite (proj1 FFree Mint32 ba 120 AVO ltac:(intros;repeat split;assumption));exact AFlag).
   assert (Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_double)
     [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef).
   { eapply eval_funcall_internal with (e:=double_helper_env bl bs bt) (le1:=le)
       (le2:=PTree.set _t'1 (Vint flag) le) (m1:=mi) (m2:=mo) (out:=Out_normal).
     - destruct (fn_okb_true _ double_function_ok) as (Vars & Params & Disjoint).
       constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
       eapply alloc_variables_cons with (m1:=ml) (b1:=bl);[exact AL|].
       eapply alloc_variables_cons with (m1:=ms) (b1:=bs);[exact AS|].
       eapply alloc_variables_cons with (m1:=mi) (b1:=bt);[exact AT|constructor].
     - exact Body.
     - reflexivity.
     - rewrite double_function_blocks;exact Free. }
   exists mf;split;[exact Call|];split;[exact RXF|];split;[exact RYF|];split;[exact RZF|];
    split;[exact RFlagF|];split;[exact AFlagF|];split;[exact AXF|];split;[exact AYF|];
    split;[exact AZF|];split;[exact RFF|];split;[exact AFF|];split;[exact BXF|];
    split;[exact BYF|];split;[exact BZF|];split.
   + assert (Full:lframe (fun b pos=>Mem.valid_block m b /\
       (b<>br \/ pos<0 \/ 124<=pos) /\ (b<>ba \/ pos<0 \/ 120<=pos)) m mf).
     { eapply lframe_trans.
       - eapply lframe_implies;[exact FAlloc|];intros;exact I.
       - eapply lframe_trans.
         + eapply lframe_implies;[exact FBody|].
           intros b pos (Valid & NR & NA) ValidI;destruct (Old b Valid) as (NL & NS & NT).
           unfold double_separate_body_frame;repeat split;assumption.
         + eapply lframe_implies;[exact FFree|].
           intros b pos (Valid & NR & NA) ValidO;exact (Old b Valid). }
     eapply lframe_implies;[exact Full|].
     intros b pos (NR & NA) Valid;repeat split;assumption.
   + eapply (secp_closed_function_preserved f_secp256k1_gej_double);
      [reflexivity|reflexivity|exact Call].
Qed.
