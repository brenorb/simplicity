(** Whole original ge_set_gej_zinv at an arbitrary aligned affine entry.
    Retain entry, both allocations, arithmetic, flag copy, return and releases;
    no nonzero-factor or on-curve premise is added. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_ge_zinv_factor C.jet_secp_ge_zinv_statements C.jet_secp_ge_zinv_arithmetic
 C.jet_secp_ge_zinv_indexed_product C.jet_secp_ge_zinv_indexed_arithmetic C.jet_secp_ge_zinv_function
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_curve_statements
 C.jet_secp_double_statements C.jet_secp_double_flag C.jet_secp_statement_prefix
 C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge C.jet_secp_local_regions
 C.jet_secp_closed_helpers C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition ge_zinv_indexed_entry_temps point br base ba bf :=
 PTree.set _zi (Vptr bf (Ptrofs.repr (ge_zinv_factor_offset point)))
 (PTree.set _a (Vptr ba Ptrofs.zero) (PTree.set _r (Vptr br (Ptrofs.repr base))
  (create_undef_temps (fn_temps f_secp256k1_ge_set_gej_zinv)))).
Definition ge_zinv_indexed_frame (br:block) (base:Z) (ba bf b:block) (pos:Z) :=
 b<>bf /\ (b<>br \/ pos<base \/ base+84<=pos) /\ (b<>ba \/ pos<0 \/ 80<=pos).

Local Ltac allocated_valid := first [assumption |
 match goal with Alloc:Mem.alloc _ _ _=(?mm,?bb) |- Mem.valid_block ?mm ?bb =>
  eapply Mem.valid_new_block;exact Alloc end |
 match goal with Alloc:Mem.alloc _ _ _=(?mm,_) |- Mem.valid_block ?mm _ =>
  eapply Mem.valid_block_alloc;[exact Alloc|allocated_valid] end].
Local Ltac allocated_distinct := first [assumption |
 match goal with Alloc:Mem.alloc _ _ _=(_,?bb) |- ?ba<>?bb =>
  let Eq:=fresh "Eq" in intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ Alloc);
   rewrite <-Eq;allocated_valid end |
 match goal with Alloc:Mem.alloc _ _ _=(_,?ba) |- ?ba<>?bb =>
  let Eq:=fresh "Eq" in intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ Alloc);
   rewrite Eq;allocated_valid end].

Theorem eval_ge_set_gej_zinv_indexed point base size x y zi m br ba bf flag :
 0<=base -> (8|base) -> base+88<=size -> size<=Ptrofs.max_unsigned -> br<>ba -> br<>bf -> ba<>bf ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds zi ->
 Mem.load Mint32 m ba 120=Some (Vint flag) ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) ->
 fe_at m bf (ge_zinv_factor_offset point) (words5 zi) ->
 Mem.range_perm m br 0 size Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable ->
 Mem.range_perm m bf 0 (ge_zinv_factor_size point) Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_gej_zinv)
  [Vptr br (Ptrofs.repr base);Vptr ba Ptrofs.zero;Vptr bf (Ptrofs.repr (ge_zinv_factor_offset point))] E0 mf Vundef /\
 fe_at mf br (base+0) (words5 (ge_zinv_x_words x zi)) /\ fe_at mf br (base+40) (words5 (ge_zinv_y_words y zi)) /\
 Mem.load Mint32 mf br (base+80)=Some (Vint flag) /\ Mem.load Mint32 mf ba 120=Some (Vint flag) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\
 fe_at mf bf (ge_zinv_factor_offset point) (words5 zi) /\
 Mem.range_perm mf br 0 size Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 Mem.range_perm mf bf 0 (ge_zinv_factor_size point) Cur Freeable /\
 square_input_bounds (ge_zinv_x_words x zi) /\ square_input_bounds (ge_zinv_y_words y zi) /\
 lframe (ge_zinv_indexed_frame br base ba bf) m mf /\ readonly_preserved m mf.
Proof.
 intros Base Align Fit Max RA RB AB BX BY BZI Flag X Y Factor RF AF FF.
 assert (FactorSize:0<ge_zinv_factor_size point) by (destruct point;cbn [ge_zinv_factor_size];lia).
 assert (RV:Mem.valid_block m br) by (eapply Mem.perm_valid_block;exact (RF 0 ltac:(lia))).
 assert (AV:Mem.valid_block m ba) by (eapply Mem.perm_valid_block;exact (AF 0 ltac:(lia))).
 assert (FV:Mem.valid_block m bf) by (eapply Mem.perm_valid_block;exact (FF 0 ltac:(lia))).
 destruct (Mem.alloc m 0 40) as (ma,b2) eqn:Alloc2.
 destruct (Mem.alloc ma 0 40) as (mi,b3) eqn:Alloc3.
 assert (Old:forall b,Mem.valid_block m b -> b<>b2 /\ b<>b3).
 { intros b Valid;split;allocated_distinct. }
 destruct (Old br RV) as (R2 & R3).
 destruct (Old ba AV) as (A2 & A3).
 destruct (Old bf FV) as (F2 & F3).
 assert (S23:b2<>b3) by allocated_distinct.
 assert (Sep:NoDup [br;ba;bf;b2;b3]).
 { repeat rewrite NoDup_cons_iff;cbn [In];repeat split;try apply NoDup_nil;intuition congruence. }
 assert (FAlloc:lframe (fun _ _=>True) m mi).
 { eapply lframe_trans;apply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption. }
 assert (XI:fe_at mi ba 0 (words5 x)) by (eapply field_at_lframe;[exact X|exact FAlloc|];intros;exact I).
 assert (YI:fe_at mi ba 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact FAlloc|];intros;exact I).
 assert (ZI:fe_at mi bf (ge_zinv_factor_offset point) (words5 zi)) by
  (eapply field_at_lframe;[exact Factor|exact FAlloc|];intros;exact I).
 assert (RFI:Mem.range_perm mi br 0 size Cur Freeable) by
  (eapply curve_keep_free;[lia|exact RF|exact FAlloc|];intros;exact I).
 assert (AFI:Mem.range_perm mi ba 0 128 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact AF|exact FAlloc|];intros;exact I).
 assert (FFI:Mem.range_perm mi bf 0 (ge_zinv_factor_size point) Cur Freeable) by
  (eapply curve_keep_free;[exact FactorSize|exact FF|exact FAlloc|];intros;exact I).
 assert (FlagI:Mem.load Mint32 mi ba 120=Some (Vint flag)) by
  (rewrite (proj1 FAlloc Mint32 ba 120 AV ltac:(intros;exact I));exact Flag).
 assert (B2F:Mem.range_perm mi b2 0 40 Cur Freeable) by
  (intros pos Range;eapply Mem.perm_alloc_1;[exact Alloc3|];eapply Mem.perm_alloc_2;[exact Alloc2|exact Range]).
 assert (B3F:Mem.range_perm mi b3 0 40 Cur Freeable) by
  (intros pos Range;eapply Mem.perm_alloc_2;[exact Alloc3|exact Range]).
 set (le:=ge_zinv_indexed_entry_temps point br base ba bf).
 destruct (exec_ge_zinv_indexed_arithmetic le point base size x y zi mi br ba bf b2 b3
   eq_refl eq_refl eq_refl Base Align Fit Max Sep BX BY BZI XI YI ZI RFI AFI FFI B2F B3F)
  as (mo & Arithmetic & RXO & RYO & AXO & AYO & ZO & RFO & AFO & FFO & B2O & B3O & BXO & BYO & FrameA).
 assert (AVO:Mem.valid_block mo ba) by (eapply Mem.perm_valid_block;exact (AFO 0 ltac:(lia))).
 assert (AVI:Mem.valid_block mi ba) by (eapply Mem.perm_valid_block;exact (AFI 0 ltac:(lia))).
 assert (FlagO:Mem.load Mint32 mo ba 120=Some (Vint flag)).
 { rewrite (proj1 FrameA Mint32 ba 120 AVI);[exact FlagI|].
   intros pos Range;change (120<=pos<124) in Range;unfold ge_zinv_indexed_arithmetic_frame;
    repeat split;try congruence;[left;congruence|right;right;lia]. }
 assert (Access:Mem.valid_access mo Mint32 br (base+80) Writable).
 { split;[intros pos Range;apply (freeable_range_writable mo br 0 size RFO);
     change (base+80<=pos<base+80+4) in Range;lia|change (4|base+80);destruct Align as [k Eq];exists (2*k+20);lia]. }
 destruct (Mem.valid_access_store mo Mint32 br (base+80) (Vint flag) Access) as (ms & Store).
 assert (FrameS:lframe (fun b pos=>b<>br \/ pos<base+80 \/ base+84<=pos) mo ms).
 { apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact Store|].
   intros pos Range;change (base+80<=pos<base+80+4) in Range;intros [Same|[Low|High]];[contradiction|lia|lia]. }
 assert (RXS:fe_at ms br (base+0) (words5 (ge_zinv_x_words x zi))) by
  (eapply curve_keep_field_range;[reflexivity|exact RXO|exact FrameS|];intros pos Range;right;left;lia).
 assert (RYS:fe_at ms br (base+40) (words5 (ge_zinv_y_words y zi))) by
  (eapply curve_keep_field_range;[reflexivity|exact RYO|exact FrameS|];intros pos Range;right;left;lia).
 assert (AXS:fe_at ms ba 0 (words5 x)) by (eapply field_at_lframe;[exact AXO|exact FrameS|];intros;left;congruence).
 assert (AYS:fe_at ms ba 40 (words5 y)) by (eapply field_at_lframe;[exact AYO|exact FrameS|];intros;left;congruence).
 assert (ZS:fe_at ms bf (ge_zinv_factor_offset point) (words5 zi)) by
  (eapply field_at_lframe;[exact ZO|exact FrameS|];intros;left;congruence).
 assert (FlagS:Mem.load Mint32 ms ba 120=Some (Vint flag)) by
  (rewrite (proj1 FrameS Mint32 ba 120 AVO ltac:(intros;left;congruence));exact FlagO).
 assert (RFlagS:Mem.load Mint32 ms br (base+80)=Some (Vint flag)) by (exact (Mem.load_store_same _ _ _ _ _ _ Store)).
 assert (RFS:Mem.range_perm ms br 0 size Cur Freeable) by
  (intros pos Range;eapply Mem.perm_store_1;[exact Store|apply RFO;exact Range]).
 assert (AFS:Mem.range_perm ms ba 0 128 Cur Freeable) by
  (intros pos Range;eapply Mem.perm_store_1;[exact Store|apply AFO;exact Range]).
 assert (FFS:Mem.range_perm ms bf 0 (ge_zinv_factor_size point) Cur Freeable) by
  (intros pos Range;eapply Mem.perm_store_1;[exact Store|apply FFO;exact Range]).
 assert (B2S:Mem.range_perm ms b2 0 40 Cur Freeable) by
  (intros pos Range;eapply Mem.perm_store_1;[exact Store|apply B2O;exact Range]).
 assert (B3S:Mem.range_perm ms b3 0 40 Cur Freeable) by
  (intros pos Range;eapply Mem.perm_store_1;[exact Store|apply B3O;exact Range]).
 destruct (free_list_exists [(b2,0,40);(b3,0,40)] ms) as (mf & Free & Unchanged).
 - repeat constructor;cbn;intuition congruence.
 - intros b lo hi [Slot|[Slot|Slot]];try contradiction;inversion Slot;subst;assumption.
 - assert (FrameF:lframe (fun b _=>b<>b2 /\ b<>b3) ms mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
     intros b pos [N2 N3] Valid;cbn;intuition congruence. }
   assert (RXF:fe_at mf br (base+0) (words5 (ge_zinv_x_words x zi))) by
    (eapply field_at_lframe;[exact RXS|exact FrameF|];intros;split;assumption).
   assert (RYF:fe_at mf br (base+40) (words5 (ge_zinv_y_words y zi))) by
    (eapply field_at_lframe;[exact RYS|exact FrameF|];intros;split;assumption).
   assert (AXF:fe_at mf ba 0 (words5 x)) by
    (eapply field_at_lframe;[exact AXS|exact FrameF|];intros;split;assumption).
   assert (AYF:fe_at mf ba 40 (words5 y)) by
    (eapply field_at_lframe;[exact AYS|exact FrameF|];intros;split;assumption).
   assert (ZF:fe_at mf bf (ge_zinv_factor_offset point) (words5 zi)) by
    (eapply field_at_lframe;[exact ZS|exact FrameF|];intros;split;assumption).
   assert (RFF:Mem.range_perm mf br 0 size Cur Freeable) by
    (eapply curve_keep_free;[lia|exact RFS|exact FrameF|];intros;split;assumption).
   assert (AFF:Mem.range_perm mf ba 0 128 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact AFS|exact FrameF|];intros;split;assumption).
   assert (FFF:Mem.range_perm mf bf 0 (ge_zinv_factor_size point) Cur Freeable) by
    (eapply curve_keep_free;[exact FactorSize|exact FFS|exact FrameF|];intros;split;assumption).
   assert (RVS:Mem.valid_block ms br) by (eapply Mem.perm_valid_block;exact (RFS 0 ltac:(lia))).
   assert (AVS:Mem.valid_block ms ba) by (eapply Mem.perm_valid_block;exact (AFS 0 ltac:(lia))).
   assert (FlagF:Mem.load Mint32 mf ba 120=Some (Vint flag)) by
    (rewrite (proj1 FrameF Mint32 ba 120 AVS ltac:(intros;split;assumption));exact FlagS).
   assert (RFlagF:Mem.load Mint32 mf br (base+80)=Some (Vint flag)) by
    (rewrite (proj1 FrameF Mint32 br (base+80) RVS ltac:(intros;split;assumption));exact RFlagS).
   assert (Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_gej_zinv)
     [Vptr br (Ptrofs.repr base);Vptr ba Ptrofs.zero;Vptr bf (Ptrofs.repr (ge_zinv_factor_offset point))] E0 mf Vundef).
   { eapply eval_funcall_internal with (e:=ge_zinv_env b2 b3) (le1:=le)
       (le2:=PTree.set _t'1 (Vint flag) le) (m1:=mi) (m2:=ms) (out:=Out_normal).
     - assert (OK:fn_okb f_secp256k1_ge_set_gej_zinv=true) by reflexivity.
       destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
       constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
       eapply alloc_variables_cons with (m1:=ma) (b1:=b2);[exact Alloc2|].
       eapply alloc_variables_cons with (m1:=mi) (b1:=b3);[exact Alloc3|constructor].
     - rewrite ge_zinv_body_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=le).
       + eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=le)
          (out1:=Out_normal) (out2:=Out_break);constructor.
       + eapply exec_statement_prefix_then_last;[exact Arithmetic|].
         unfold ge_zinv_flag_statement;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0)
          (m1:=mo) (le1:=PTree.set _t'1 (Vint flag) le).
         * apply exec_Sset;eapply eval_Elvalue.
           -- apply eval_double_flag_field;reflexivity.
           -- eapply deref_loc_value with (chunk:=Mint32);[reflexivity|exact FlagO].
         * eapply exec_Sassign with (loc:=br) (ofs:=Ptrofs.repr (base+80)) (bf:=Full) (v2:=Vint flag) (v:=Vint flag).
           -- apply eval_ge_zinv_indexed_field;[right;right;left;reflexivity|exact Base|lia|reflexivity].
           -- apply eval_Etempvar;apply PTree.gss.
           -- reflexivity.
           -- eapply assign_loc_value with (chunk:=Mint32);[reflexivity|].
              cbn [Mem.storev];rewrite Ptrofs.unsigned_repr by lia;exact Store.
     - reflexivity.
     - rewrite ge_zinv_blocks;exact Free. }
   exists mf;split;[exact Call|];split;[exact RXF|];split;[exact RYF|];split;[exact RFlagF|];
    split;[exact FlagF|];split;[exact AXF|];split;[exact AYF|];split;[exact ZF|];
    split;[exact RFF|];split;[exact AFF|];split;[exact FFF|];split;[exact BXO|];split;[exact BYO|];split.
   + assert (Full:lframe (fun b pos=>Mem.valid_block m b /\ ge_zinv_indexed_frame br base ba bf b pos) m mf).
     { eapply lframe_trans.
       - eapply lframe_implies;[exact FAlloc|];intros;exact I.
       - eapply lframe_trans.
         + eapply lframe_implies;[exact FrameA|].
           intros b pos (Valid & NF & NR & NA) ValidI;destruct (Old b Valid) as [N2 N3].
           unfold ge_zinv_indexed_arithmetic_frame;repeat split;try assumption;
            destruct NR as [NR|[NR|NR]];intuition lia.
         + eapply lframe_trans.
           * eapply lframe_implies;[exact FrameS|].
             intros b pos (Valid & NF & NR & NA) ValidO;destruct NR as [NR|[NR|NR]];intuition lia.
           * eapply lframe_implies;[exact FrameF|].
             intros b pos (Valid & Rest) ValidS;exact (Old b Valid). }
     eapply lframe_implies;[exact Full|];intros b pos Outside Valid;split;assumption.
   + eapply (secp_closed_function_preserved f_secp256k1_ge_set_gej_zinv);
      [reflexivity|reflexivity|exact Call].
Qed.
