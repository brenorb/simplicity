(** Whole original Strauss call for scale: both preprocessing branches,
    all private allocations/frees, and the literal conditional result. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_strauss_point_loop C.jet_secp_strauss_digit_guard
 C.jet_secp_generator_digit_control C.jet_secp_generator_loop_control
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge
 C.jet_secp_square_columns C.jet_secp_field_mul_small
 C.jet_secp_globalz_loop C.jet_secp_globalz_pass2 C.jet_secp_globalz_word_walk
 C.jet_secp_scalar_table_literal C.jet_secp_wnaf5_literal C.jet_secp_strauss_wnaf_calls
 C.jet_secp_rescale_literal C.jet_secp_canonical_zero C.jet_secp_double_loose_literal
 C.jet_secp_double_literal C.jet_secp_mixed_xy_literal C.jet_secp_strauss_program
 C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_secp_slice_permissions
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Local Opaque secp_ge rescale_field_output literal_gej_double literal_strauss_step.
Set Default Timeout 10.

Require Import C.jet_secp_strauss_scale_iteration.


Require Import C.jet_secp_strauss_scale_loop C.jet_secp_negate_literal_contract C.jet_secp_globalz_word_walk C.jet_secp_generator_point_stage C.jet_secp_generator_entry C.jet_secp_generator_final C.jet_secp_strauss_final_literal
 C.jet_secp_double_var_owned C.jet_secp_gej_infinity_owned C.jet_secp_literal_infinity C.jet_secp_curve_literal C.jet_secp_generator_loop_literal.
Local Opaque literal_fe_multiply literal_gej_infinity.

Require Import C.jet_clight_readonly_frame C.jet_secp_strauss_generator_zero C.jet_secp_strauss_digit_index C.jet_secp_strauss_scale_point_stage C.jet_secp_strauss_scale_literal
 C.jet_secp_strauss_zero_generator C.jet_secp_generator_main C.jet_secp_generator_digit_index
 C.jet_secp_strauss_complete_program C.jet_secp_split_literal C.jet_secp_wnaf5_input
 C.jet_secp_wnaf5_signed_array C.jet_secp_wnaf_loop C.jet_memset_model.
Local Opaque literal_strauss_body literal_scalar_table5 literal_scalar_split_lambda.



From Coq Require Import ZArith List.
From compcert Require Import Coqlib Memory Values.
Require Import C.jet_sx_mem C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma strauss_restore_readonly_exceptions exceptions P m mf :
 lframe (fun b pos=>P b pos /\ ~In b exceptions) m mf ->
 readonly_preserved m mf ->
 (forall b,In b exceptions -> forall pos,~Mem.perm m b pos Max Writable) ->
 lframe P m mf.
Proof.
 intros Frame Read Readonly.
 pose proof (lframe_unchanged _ _ _ (proj2 Read)) as Protected.
 split.
 - intros chunk b ofs Valid Range.
   destruct (in_dec Pos.eq_dec b exceptions) as [Inside|Outside].
   + apply (proj1 Protected);[exact Valid|].
     intros pos Pos;split;[exact Valid|apply Readonly;exact Inside].
   + apply (proj1 Frame);[exact Valid|].
     intros pos Pos;split;[apply Range;exact Pos|exact Outside].
 - split.
   + intros b pos k p Valid At Perm.
     destruct (in_dec Pos.eq_dec b exceptions) as [Inside|Outside].
     * apply (proj1 (proj2 Protected));[exact Valid|split;[exact Valid|apply Readonly;exact Inside]|exact Perm].
     * apply (proj1 (proj2 Frame));[exact Valid|split;assumption|exact Perm].
   + exact (proj2 (proj2 Frame)).
Qed.


Require Import C.jet_secp_split_constants C.jet_secp_split_multipliers C.jet_secp_scalar_lambda_global
 C.jet_secp_beta_global C.jet_clight_readonly_frame.
Definition strauss_readonly_blocks : list block :=
 [split_multiplier_block true;split_multiplier_block false;
  split_basis_block true;split_basis_block false;scalar_lambda_block;beta_block].
Lemma strauss_readonly_blocks_not_writable m :
 split_constants_ready m -> beta_initialized m ->
 forall b,In b strauss_readonly_blocks -> forall pos,~Mem.perm m b pos Max Writable.
Proof.
 intros [Multipliers [Basis Lambda]] Beta b Inside pos.
 cbn [strauss_readonly_blocks In] in Inside.
 destruct Inside as [At|[At|[At|[At|[At|[At|At]]]]]];try contradiction;subst b.
 - exact (proj2 (Multipliers true) pos).
 - exact (proj2 (Multipliers false) pos).
 - exact (proj2 (Basis true) pos).
 - exact (proj2 (Basis false) pos).
 - exact (proj2 Lambda pos).
 - apply (readonly_bounds_not_writable _ _ _ _ (proj2 Beta)).
Qed.

Require Import C.jet_secp_strauss_beta_prepare C.jet_secp_strauss_first_loop C.jet_secp_generator_globalz_call
 C.jet_secp_generator_preprocess.
Lemma strauss_prepare_reassociate e le m lef mf :
 Clight2.exec_stmt secp_ge e le m strauss_point_prepare E0 lef mf Out_normal ->
 Clight2.exec_stmt secp_ge e le m generator_no_points_phase E0 lef mf Out_normal.
Proof.
 intro Run;unfold strauss_point_prepare,strauss_preprocess_finite_statement in Run.
 inversion Run;subst;clear Run;try contradiction.
 match goal with Inner:exec_stmt function_entry2 _ _ _ _ (Ssequence generator_preprocess_statement generator_globalz_statement) _ _ _ Out_normal |- _ =>
  inversion Inner;subst;clear Inner end;try contradiction.
 all:repeat match goal with
 | H : ?t1 ** ?t2 = E0 |- _ => let Parts:=fresh "Parts" in
  pose proof (Eapp_E0_inv t1 t2 H) as Parts;clear H;destruct Parts as [LeftTrace RightTrace];subst
 | H : E0 = ?t1 ** ?t2 |- _ => let Parts:=fresh "Parts" in
  pose proof (Eapp_E0_inv t1 t2 (eq_sym H)) as Parts;clear H;destruct Parts as [LeftTrace RightTrace];subst
 end.
 rewrite generator_no_points_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[eassumption|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[eassumption|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[eassumption|constructor].
Qed.

Lemma strauss_nodup_append (left right:list block) :
 NoDup left -> NoDup right ->
 (forall b,In b left -> ~In b right) -> NoDup (left++right).
Proof.
 intro Distinct;induction Distinct as [|head tail Absent Distinct IH];intros Other Disjoint.
 - exact Other.
 - cbn [app];constructor.
   + rewrite in_app_iff;intros [Inside|Inside].
     * exact (Absent Inside).
     * exact (Disjoint head (or_introl eq_refl) Inside).
   + apply IH;[exact Other|].
     intros b Inside;apply Disjoint;right;exact Inside.
Qed.


Require Import C.jet_secp_statement_prefix C.jet_secp_point_mul_storage C.jet_secp_field_zero_owned C.jet_secp_odd_table_body C.jet_secp_odd_table_loop C.jet_secp_double_all_calls C.jet_secp_strauss_scale_main C.jet_secp_beta_state C.jet_secp_beta_loop_step
 C.jet_secp_odd_table_literal_walk C.jet_secp_canonical_scalar C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_add_reader_support
 C.jet_secp_generator_initialize C.jet_secp_generator_function C.jet_secp_split_function
 C.jet_secp_wnaf_slice_frame C.jet_secp_beta_loop.

Definition strauss_outer_storage br bk ba bs bp bt bx : list (block*Z) :=
 [(br,128);(bk,32);(ba,128);(bs,24);(bp,1040);(bt,704);(bx,320)].
Lemma strauss_outer_size_positive br bk ba bs bp bt bx b hi :
 In (b,hi) (strauss_outer_storage br bk ba bs bp bt bx) -> 0<hi.
Proof.
 intro Slot;assert (Sizes:In hi (map (@snd block Z) (strauss_outer_storage br bk ba bs bp bt bx))).
 { apply in_map_iff;exists (b,hi);split;[reflexivity|exact Slot]. }
 change (In hi [128;32;128;24;1040;704;320]) in Sizes;cbn [In] in Sizes;intuition lia.
Qed.

Section Generic_eval_strauss_scale_finite.
Context (bng:block).
Theorem eval_strauss_scale_finite_at (Model:memset_model)
 (raw ax ay az:Ty.tySem (Word 8)) x y z m br bk ba bs bp bt bx :
 (zero_scalar_state bng) m -> split_constants_ready m -> beta_initialized m ->
 NoDup [br;bk;ba;bs;bp;bt;bx] ->
 (forall b hi,In (b,hi) (strauss_outer_storage br bk ba bs bp bt bx) ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)<>0 ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az -> field_zero_result z=Int.zero ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 exists mf ox oy oz,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_strauss_wnaf)
  [Vptr bs Ptrofs.zero;Vptr br Ptrofs.zero;Vlong Int64.one;Vptr ba Ptrofs.zero;
   Vptr bk Ptrofs.zero;Vptr bng Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_strauss_body Alg.CoreFunSem ((raw,((ax,ay),az)),@Word.zero 8 Alg.CoreFunSem tt) /\
 (forall b hi,In (b,hi) (strauss_outer_storage br bk ba bs bp bt bx) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 (zero_scalar_state bng) mf /\
 lframe (fun b _=>~In b [br;bk;ba;bs;bp;bt;bx]) m mf.
Proof.
 intros Global Ready Beta OuterSeparate Outer Input Nonzero BX BY BZ X Y Z Flag HX HY HZ Finite PS PT PX.
 assert (OldValid:forall b,In b [br;bk;ba;bs;bp;bt;bx] -> Mem.valid_block m b).
 { intros b Member;change (In b (map (@fst block BinNums.Z) (strauss_outer_storage br bk ba bs bp bt bx))) in Member.
   apply in_map_iff in Member;destruct Member as [[b' hi] [Eq Slot]];cbn [fst] in Eq;subst b'.
   eapply Mem.perm_valid_block;apply (Outer b hi Slot 0);split;[reflexivity|].
   eapply strauss_outer_size_positive;exact Slot. }
 pose proof ((strauss_zero_global_valid_at bng) m Global) as VG.
 destruct (strauss_entry_and_initialize m bs (Vptr br Ptrofs.zero) (Vptr ba Ptrofs.zero)
  (Vptr bk Ptrofs.zero) (Vptr bng Ptrofs.zero))
  as (mi & mp & bd & bz & b0 & b128 & bw0 & bw128 & bj & bn & bl &
   Entry & Init & Denominator & Separate & Old & Owned & FrameI & KeepI & ReadI).
 pose (e:=generator_local_env bd bz b0 b128 bw0 bw128 bj bn bl).
 pose (le:=strauss_entry_temps bs (Vptr br Ptrofs.zero) (Vptr ba Ptrofs.zero)
  (Vptr bk Ptrofs.zero) (Vptr bng Ptrofs.zero)).
 pose (li:=generator_initial_temps le).
 assert (Different:forall b,In b [br;bk;ba;bs;bp;bt;bx] ->
  ~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]).
 { intros b Slot;apply Old,OldValid;exact Slot. }
 assert (PrepSeparate:NoDup [bk;bn;bl;bs;bp;ba;bt;bx;bz;bj]).
 { assert (OldSix:NoDup [bk;bs;bp;ba;bt;bx]).
   { clear -OuterSeparate;repeat rewrite NoDup_cons_iff in OuterSeparate;
     repeat rewrite NoDup_cons_iff;cbn [In] in *;intuition congruence. }
   assert (FreshFour:NoDup [bn;bl;bz;bj]).
   { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;
     repeat rewrite NoDup_cons_iff;cbn [In] in *;intuition congruence. }
   assert (Union:NoDup ([bk;bs;bp;ba;bt;bx]++[bn;bl;bz;bj])).
   { apply strauss_nodup_append;[exact OldSix|exact FreshFour|].
     intros b Slot Inside;apply (Different b);[clear -Slot;cbn [In] in *;tauto|
      clear -Inside;cbn [In] in *;tauto]. }
   eapply NoDup_incl_NoDup with (l:=[bk;bs;bp;ba;bt;bx]++[bn;bl;bz;bj]).
   - exact Union.
   - cbn;lia.
   - intros b;cbn [app In];tauto. }
 assert (MainSeparate:NoDup [br;bs;bp;bt;bx;bd;bz;b0;b128;bw0;bw128;bj;bn;bl]).
 { change (NoDup ([br;bs;bp;bt;bx]++[bd;bz;b0;b128;bw0;bw128;bj;bn;bl])).
   apply strauss_nodup_append.
   - clear -OuterSeparate;repeat rewrite NoDup_cons_iff in OuterSeparate;repeat rewrite NoDup_cons_iff;
     cbn [In] in *;intuition congruence.
   - exact Separate.
   - intros b Slot;apply Different;cbn [In] in Slot|-*;tauto. }
 assert (PrepOwned:forall b hi,In (b,hi) (strauss_preprocess_storage bk bn bl bs bp ba bt bx bz bj) ->
  Mem.range_perm mp b 0 hi Cur Freeable).
 { intros b hi Slot;cbn [strauss_preprocess_storage In] in Slot.
   repeat match type of Slot with _ \/ _ =>destruct Slot as [Slot|Slot] end;try contradiction;
    inversion Slot;subst b hi.
   all:first [solve [apply Owned;clear;cbn [generator_local_storage In];tauto]|
    eapply curve_keep_free;[clear;lia|apply Outer;clear;cbn [strauss_outer_storage In];tauto|exact FrameI|intros;exact I]]. }
 assert (Saved:forall chunk b ofs v,Mem.load chunk m b ofs=Some v -> Mem.load chunk mp b ofs=Some v).
 { intros chunk b ofs v Load;rewrite (proj1 FrameI chunk b ofs);[exact Load| |intros;exact I].
   eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
    [eapply Mem.load_valid_access;exact Load|apply perm_any_N]. }
 assert (InputI:scalar_at mp bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw))))).
 { eapply scalar_at_lframe;[exact Input|exact FrameI|intros;exact I]. }
 assert (XI:fe_at mp ba 0 (words5 x)) by (eapply field_at_lframe;[exact X|exact FrameI|intros;exact I]).
 assert (YI:fe_at mp ba 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact FrameI|intros;exact I]).
 assert (ZI:fe_at mp ba 80 (words5 z)) by (eapply field_at_lframe;[exact Z|exact FrameI|intros;exact I]).
 assert (FlagI:Mem.load Mint32 mp ba 120=Some (Vint Int.zero)) by (apply Saved;exact Flag).
 assert (PSI:Mem.load Mptr mp bs 16=Some (Vptr bp Ptrofs.zero)) by (apply Saved;exact PS).
 assert (PTI:Mem.load Mptr mp bs 8=Some (Vptr bt Ptrofs.zero)) by (apply Saved;exact PT).
 assert (PXI:Mem.load Mptr mp bs 0=Some (Vptr bx Ptrofs.zero)) by (apply Saved;exact PX).
 assert (ReadyI:split_constants_ready mp) by (eapply split_constants_readonly;[exact Ready|exact ReadI]).
 assert (BetaI:beta_initialized mp) by (eapply beta_initialized_preserved;[exact Beta|exact ReadI]).
 assert (NAI:li!_na=Some (Vptr bk Ptrofs.zero)) by (unfold li;rewrite generator_initial_preserves by discriminate;reflexivity).
 assert (AI:li!_a=Some (Vptr ba Ptrofs.zero)) by (unfold li;rewrite generator_initial_preserves by discriminate;reflexivity).
 assert (SI:li!_state=Some (Vptr bs Ptrofs.zero)) by (unfold li;rewrite generator_initial_preserves by discriminate;reflexivity).
 assert (NumI:li!_num=Some (Vlong Int64.one)) by (unfold li;rewrite generator_initial_preserves by discriminate;reflexivity).
 assert (NoI:li!_no=Some (Vlong Int64.zero)) by (unfold li,generator_initial_temps;apply PTree.gss).
 assert (BitsI:li!_bits=Some (Vint Int.zero)).
 { unfold li,generator_initial_temps;rewrite PTree.gso by discriminate;apply PTree.gss. }
 destruct (exec_strauss_point_prepare Model e li mp raw bk bn bl bs bp ba bt bx bz bj x y z ax ay az
  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
  NAI AI SI NumI NoI BitsI PSI PTI PXI ReadyI BetaI InputI Nonzero BX BY BZ XI YI ZI FlagI
  PrepOwned PrepSeparate HX HY HZ Finite)
  as (lp & ms & last1 & lastlam & digits1 & digitslam & xf & yf & Prepare & NP & NoP & IP & BitsP & BitsBound &
   A1 & AL & B1 & BL & C1 & CL & L1 & LL & Table & Bounds & Tight & Aux & AuxBounds & AuxLiteral &
   Inv & InvBounds & Context & XP & YP & ZP & FlagP & PSP & PTP & PXP & InputP &
   OwnedP & ReadyP & BetaP & KeepP & ReadP & FrameP & OtherP).
 assert (RP:lp!_r=Some (Vptr br Ptrofs.zero)).
 { rewrite OtherP by (clear;cbn [In];intuition discriminate).
   unfold li;rewrite generator_initial_preserves by discriminate;reflexivity. }
 assert (SP:lp!_state=Some (Vptr bs Ptrofs.zero)) by (rewrite OtherP by (clear;cbn [In];intuition discriminate);exact SI).
 assert (NGP:lp!_ng=Some (Vptr bng Ptrofs.zero)).
 { rewrite OtherP by (clear;cbn [In];intuition discriminate).
   unfold li;rewrite generator_initial_preserves by discriminate;reflexivity. }
 assert (GlobalP:(zero_scalar_state bng) ms).
 { eapply (strauss_zero_global_preserved_at bng);[|exact ReadP].
   eapply (strauss_zero_global_preserved_at bng);[exact Global|exact ReadI]. }
 assert (LocalP:forall b hi,In (b,hi) (generator_local_storage bd bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm ms b 0 hi Cur Freeable).
 { intros b hi Slot pos P;apply KeepP;apply (Owned b hi Slot);exact P. }
 assert (OuterP:forall b hi,In (b,hi) (strauss_outer_storage br bk ba bs bp bt bx) ->
  Mem.range_perm ms b 0 hi Cur Freeable).
 { intros b hi Slot pos P;apply KeepP,KeepI;apply (Outer b hi Slot);exact P. }
 destruct ((exec_strauss_scale_main_at bng) Model lp ms br bs bp bt bx bd bz b0 b128 bw0 bw128 bj bn bl
  raw ((ax,ay),az) xf yf (beta_aux_values xf)
  (point_mul_words (odd_table_z (odd_table_final_state x y z)) (double_output_z_words y z))
  last1 lastlam digits1 digitslam MainSeparate RP SP NoP BitsP NGP GlobalP PSP PTP PXP C1 CL A1 AL L1 LL
  Table Bounds Tight Aux AuxBounds AuxLiteral InvBounds Inv Context
  (OuterP br 128 ltac:(clear;cbn [strauss_outer_storage In];tauto))
  (OuterP bt 704 ltac:(clear;cbn [strauss_outer_storage In];tauto))
  (OuterP bx 320 ltac:(clear;cbn [strauss_outer_storage In];tauto)) LocalP)
  as (lef & mu & ox & oy & oz & Main & RF & XO & YO & ZO & BXO & BYO & BZO & Literal & FreeRU &
   FreeTU & FreeXU & LocalU & KeepM & GlobalU & FrameM).
 assert (KeepU:keeps_permissions m mu) by
  (eapply keeps_permissions_trans;[exact KeepI|];eapply keeps_permissions_trans;[exact KeepP|exact KeepM]).
 assert (PrepFrame:lframe
  (fun b _=>~In b [br;bk;ba;bs;bp;bt;bx] /\ ~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) mp ms).
 { eapply strauss_restore_readonly_exceptions with (exceptions:=strauss_readonly_blocks);[|exact ReadP|].
   - eapply lframe_implies;[exact FrameP|].
     intros b pos [[OutsideOld OutsideFresh] OutsideRO] Valid.
     unfold split_function_frame,wnaf_slice_outside.
     clear -OutsideOld OutsideFresh OutsideRO.
     cbn [strauss_readonly_blocks In] in *;intuition congruence.
   - apply strauss_readonly_blocks_not_writable;assumption. }
 destruct (free_list_exists
  [(bw128,0,516);(bw0,0,516);(bd,0,88);(bj,0,128);(bz,0,40);(b128,0,32);(b0,0,32);(bn,0,32);(bl,0,32)] mu)
  as (mf & Released & UnchangedF).
 - pose proof Separate as Distinct;repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct.
   clear -Distinct;cbn;repeat constructor;cbn;intuition congruence.
 - intros b lo hi Slot;clear -LocalU Slot;cbn [In] in Slot.
   repeat match type of Slot with _ \/ _=>destruct Slot as [Slot|Slot] end;try contradiction;
    inversion Slot;subst;apply LocalU;clear;cbn [generator_local_storage In];tauto.
 - assert (FrameF:lframe (fun b _=>~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) mu mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact UnchangedF|].
     intros b pos Outside Valid;clear -Outside;cbn [map fst In] in *;intuition congruence. }
   assert (OutsideR:~In br [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) by (apply Different;clear;cbn [In];tauto).
   assert (OutsideG:~In bng [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) by (apply Old;exact VG).
   assert (XF:fe_at mf br 0 (words5 ox)) by (eapply field_at_lframe;[exact XO|exact FrameF|intros;exact OutsideR]).
   assert (YF:fe_at mf br 40 (words5 oy)) by (eapply field_at_lframe;[exact YO|exact FrameF|intros;exact OutsideR]).
   assert (ZF:fe_at mf br 80 (words5 oz)) by (eapply field_at_lframe;[exact ZO|exact FrameF|intros;exact OutsideR]).
   assert (OuterF:forall b hi,In (b,hi) (strauss_outer_storage br bk ba bs bp bt bx) ->
    Mem.range_perm mf b 0 hi Cur Freeable).
   { intros b hi Slot;eapply curve_keep_free with (P:=fun b _=>~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) (m:=mu).
     - eapply strauss_outer_size_positive;exact Slot.
     - intros pos P;apply KeepU;apply (Outer b hi Slot);exact P.
     - exact FrameF.
     - intros pos;apply Old.
       eapply Mem.perm_valid_block;apply (Outer b hi Slot 0);split;[reflexivity|eapply strauss_outer_size_positive;exact Slot]. }
   assert (GlobalF:(zero_scalar_state bng) mf).
   { eapply (strauss_zero_global_unchanged_at bng);[exact GlobalU|].
     eapply Mem.unchanged_on_implies;[exact UnchangedF|].
     intros b pos At Valid;subst b;clear -OutsideG;cbn [map fst In] in *;intuition congruence. }
   assert (Frame:lframe (fun b _=>~In b [br;bk;ba;bs;bp;bt;bx]) m mf).
   { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\ ~In b [br;bk;ba;bs;bp;bt;bx]).
     - eapply lframe_trans;[eapply lframe_implies;[exact FrameI|intros;exact I]|].
       eapply lframe_trans.
       + eapply lframe_implies;[exact PrepFrame|intros b pos [Valid Outside] _;split;[exact Outside|apply Old;exact Valid]].
       + eapply lframe_trans.
         * eapply lframe_implies;[exact FrameM|intros b pos [Valid Outside] _;split;
            [clear -Outside;cbn [In] in Outside;intuition congruence|apply Old;exact Valid]].
         * eapply lframe_implies;[exact FrameF|intros b pos [Valid Outside] _;apply Old;exact Valid].
     - intros b pos Outside Valid;split;assumption. }
   assert (PrepareAll:Clight2.exec_stmt secp_ge e le mi generator_prepare_non_generator E0 lp ms Out_normal).
   { rewrite generator_prepare_non_generator_source;eapply exec_statement_prefix_then_last;
      [exact Init|apply strauss_prepare_reassociate;exact Prepare]. }
   exists mf,ox,oy,oz;split.
   + eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=lef) (m1:=mi) (m2:=mu) (out:=Out_normal).
     * exact Entry.
     * rewrite generator_body_main_source;eapply exec_statement_prefix_then_last;[exact PrepareAll|exact Main].
     * reflexivity.
     * unfold e;rewrite generator_local_blocks;exact Released.
   + split;[exact XF|];split;[exact YF|];split;[exact ZF|];
     split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];
     split;[exact Literal|];split;[exact OuterF|];split;assumption.
Qed.
End Generic_eval_strauss_scale_finite.

Theorem eval_strauss_scale_finite (Model:memset_model)
 (raw ax ay az:Ty.tySem (Word 8)) x y z m br bk ba bs bp bt bx :
 strauss_zero_global_state m -> split_constants_ready m -> beta_initialized m ->
 NoDup [br;bk;ba;bs;bp;bt;bx] ->
 (forall b hi,In (b,hi) (strauss_outer_storage br bk ba bs bp bt bx) ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)<>0 ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az -> field_zero_result z=Int.zero ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 exists mf ox oy oz,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_strauss_wnaf)
  [Vptr bs Ptrofs.zero;Vptr br Ptrofs.zero;Vlong Int64.one;Vptr ba Ptrofs.zero;
   Vptr bk Ptrofs.zero;Vptr strauss_zero_block Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_strauss_body Alg.CoreFunSem ((raw,((ax,ay),az)),@Word.zero 8 Alg.CoreFunSem tt) /\
 (forall b hi,In (b,hi) (strauss_outer_storage br bk ba bs bp bt bx) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 strauss_zero_global_state mf /\
 lframe (fun b _=>~In b [br;bk;ba;bs;bp;bt;bx]) m mf.
Proof. exact (@eval_strauss_scale_finite_at strauss_zero_block Model raw ax ay az x y z m br bk ba bs bp bt bx). Qed.


Require Import C.jet_toZ C.jet_predicate_spec C.jet_secp_canonical_scalar_zero C.jet_secp_literal_gej_predicate C.jet_secp_mixed_xy_flag
 C.jet_secp_literal_infinity C.jet_secp_write_fe_wide_exec C.jet_secp_canonical_normalize.
Local Opaque canonical_scalar_normalize literal_off_curve_scale literal_off_curve_linear_combination_1
 literal_strauss_guard literal_gej_is_infinity literal_fe_zero256.

Local Transparent literal_gej_infinity.
Lemma strauss_scale_zero_result :
 ((rescale_field_output (fun _=>Int64.zero),rescale_field_output (fun _=>Int64.zero)),
  rescale_field_output (fun _=>Int64.zero))=@literal_gej_infinity Alg.CoreFunSem tt.
Proof.
 assert (Zero:rescale_field_output (fun _=>Int64.zero)=@literal_fe_zero256 Alg.CoreFunSem tt).
 { exact zero_field_writer_literal_output. }
 change (((rescale_field_output (fun _=>Int64.zero),rescale_field_output (fun _=>Int64.zero)),
  rescale_field_output (fun _=>Int64.zero))=
 ((@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt),
  @literal_fe_zero256 Alg.CoreFunSem tt)).
 rewrite Zero;reflexivity.
Qed.


Lemma strauss_scale_guarded_value (raw:Ty.tySem (Word 8)) (point:Ty.tySem literal_table_gej) branch :
 Bit.toBool (@literal_strauss_guard Alg.CoreFunSem
  ((raw,point),@Word.zero 8 Alg.CoreFunSem tt))=branch ->
 @literal_off_curve_scale Alg.CoreFunSem (raw,point)=
 if branch then @literal_gej_infinity Alg.CoreFunSem tt else
 @literal_strauss_body Alg.CoreFunSem ((raw,point),@Word.zero 8 Alg.CoreFunSem tt).
Proof.
 intro Guard.
 eapply eq_trans;[exact (literal_off_curve_scale_value raw point)|].
 eapply eq_trans;[exact (literal_off_curve_linear_combination_1_value raw point
  (@Word.zero 8 Alg.CoreFunSem tt))|].
 pose proof (f_equal (fun bit:bool=>if bit then
  @C.jet_secp_generate_program.literal_generate Alg.CoreFunSem (@Word.zero 8 Alg.CoreFunSem tt)
  else @literal_strauss_body Alg.CoreFunSem ((raw,point),@Word.zero 8 Alg.CoreFunSem tt)) Guard) as Choice.
 eapply eq_trans;[exact Choice|];destruct branch;[exact strauss_generate_zero|reflexivity].
Qed.

Section Generic_eval_strauss_scale.
Context (bng:block).
Theorem eval_strauss_scale_at (Model:memset_model)
 (raw ax ay az:Ty.tySem (Word 8)) x y z m br bk ba bs bp bt bx :
 (zero_scalar_state bng) m -> split_constants_ready m -> beta_initialized m ->
 NoDup [br;bk;ba;bs;bp;bt;bx] ->
 (forall b hi,In (b,hi) (strauss_outer_storage br bk ba bs bp bt bx) ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.load Mint32 m ba 120=Some (Vint (bit_int (Bit.toBool
  (@literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az))))) ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 exists mf ox oy oz,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_strauss_wnaf)
  [Vptr bs Ptrofs.zero;Vptr br Ptrofs.zero;Vlong Int64.one;Vptr ba Ptrofs.zero;
   Vptr bk Ptrofs.zero;Vptr bng Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_off_curve_scale Alg.CoreFunSem (raw,((ax,ay),az)) /\
 (forall b hi,In (b,hi) (strauss_outer_storage br bk ba bs bp bt bx) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 (zero_scalar_state bng) mf /\
 lframe (fun b _=>~In b [br;bk;ba;bs;bp;bt;bx]) m mf.
Proof.
 intros Global Ready Beta Separate Owned Input BX BY BZ X Y Z Flag HX HY HZ PS PT PX.
 destruct (Bit.toBool (@literal_strauss_guard Alg.CoreFunSem
  ((raw,((ax,ay),az)),@Word.zero 8 Alg.CoreFunSem tt))) eqn:Guard.
 - assert (Skip:
   @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)=0 \/
   Mem.load Mint32 m ba 120=Some (Vint Int.one)).
   { rewrite literal_strauss_guard_value in Guard;apply Bool.orb_true_iff in Guard.
     destruct Guard as [Infinity|Zero].
     - right;unfold bit_int in Flag;rewrite Infinity in Flag;exact Flag.
     - left;apply Z.eqb_eq;rewrite canonical_scalar_zero_after_normalize;exact Zero. }
   destruct ((eval_strauss_scale_skipped_at bng) Model
    (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw))
    m br bk ba bs bt bx Global ltac:(change (0<=@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)<word_modulus 8);apply word_value_bounds) Input Skip PT PX
    (Owned br 128 ltac:(clear;cbn [strauss_outer_storage In];tauto)))
    as (mf & Call & XO & YO & ZO & FlagO & FreeR & GlobalF & Frame).
   assert (OwnedF:forall b hi,In (b,hi) (strauss_outer_storage br bk ba bs bp bt bx) ->
    Mem.range_perm mf b 0 hi Cur Freeable).
   { intros b hi Slot;destruct (Pos.eq_dec b br) as [Same|Other].
     - subst b;assert (Size:hi=128).
       { clear -Slot Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate.
         cbn [strauss_outer_storage In] in Slot;intuition congruence. }
       subst hi;exact FreeR.
     - eapply curve_keep_free;[eapply strauss_outer_size_positive;exact Slot|
        exact (Owned b hi Slot)|exact Frame|intros;exact Other]. }
   assert (Literal:
    ((rescale_field_output (fun _=>Int64.zero),rescale_field_output (fun _=>Int64.zero)),
     rescale_field_output (fun _=>Int64.zero))=
    @literal_off_curve_scale Alg.CoreFunSem (raw,((ax,ay),az))).
   { eapply eq_trans;[exact strauss_scale_zero_result|].
     symmetry;exact (strauss_scale_guarded_value raw ((ax,ay),az) true Guard). }
   exists mf,(fun _=>Int64.zero),(fun _=>Int64.zero),(fun _=>Int64.zero);
    split;[exact Call|];split;[exact XO|];split;[exact YO|];split;[exact ZO|];
    split;[exact square_zero_bounds|];split;[exact square_zero_bounds|];split;[exact square_zero_bounds|];
    split;[exact Literal|];split;[exact OwnedF|];split;[exact GlobalF|].
   eapply lframe_implies;[exact Frame|].
   intros b pos Outside Valid;clear -Outside;cbn [In] in Outside;intuition congruence.
 - pose proof Guard as Parts;rewrite literal_strauss_guard_value in Parts;
    apply Bool.orb_false_iff in Parts;destruct Parts as [Infinity Zero].
   assert (Nonzero:@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)<>0).
   { apply Z.eqb_neq;rewrite canonical_scalar_zero_after_normalize;exact Zero. }
   assert (Flag0:Mem.load Mint32 m ba 120=Some (Vint Int.zero)).
   { unfold bit_int in Flag;rewrite Infinity in Flag;exact Flag. }
   assert (Finite:field_zero_result z=Int.zero).
   { rewrite (mixed_flag_of_residue z az HZ).
     rewrite <-literal_gej_is_infinity_value with (x:=ax) (y:=ay).
     exact (f_equal bit_int Infinity). }
   destruct ((eval_strauss_scale_finite_at bng) Model raw ax ay az x y z m br bk ba bs bp bt bx
    Global Ready Beta Separate Owned Input Nonzero BX BY BZ X Y Z Flag0 HX HY HZ Finite PS PT PX)
    as (mf & ox & oy & oz & Call & XO & YO & ZO & BXO & BYO & BZO & Literal & OwnedF & GlobalF & Frame).
   exists mf,ox,oy,oz;split;[exact Call|];split;[exact XO|];split;[exact YO|];split;[exact ZO|];
    split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];split.
   + eapply eq_trans;[exact Literal|].
     symmetry;exact (strauss_scale_guarded_value raw ((ax,ay),az) false Guard).
   + split;[exact OwnedF|];split;assumption.
Qed.
End Generic_eval_strauss_scale.

Theorem eval_strauss_scale (Model:memset_model)
 (raw ax ay az:Ty.tySem (Word 8)) x y z m br bk ba bs bp bt bx :
 strauss_zero_global_state m -> split_constants_ready m -> beta_initialized m ->
 NoDup [br;bk;ba;bs;bp;bt;bx] ->
 (forall b hi,In (b,hi) (strauss_outer_storage br bk ba bs bp bt bx) ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.load Mint32 m ba 120=Some (Vint (bit_int (Bit.toBool
  (@literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az))))) ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 exists mf ox oy oz,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_strauss_wnaf)
  [Vptr bs Ptrofs.zero;Vptr br Ptrofs.zero;Vlong Int64.one;Vptr ba Ptrofs.zero;
   Vptr bk Ptrofs.zero;Vptr strauss_zero_block Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_off_curve_scale Alg.CoreFunSem (raw,((ax,ay),az)) /\
 (forall b hi,In (b,hi) (strauss_outer_storage br bk ba bs bp bt bx) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 strauss_zero_global_state mf /\
 lframe (fun b _=>~In b [br;bk;ba;bs;bp;bt;bx]) m mf.
Proof. exact (@eval_strauss_scale_at strauss_zero_block Model raw ax ay az x y z m br bk ba bs bp bt bx). Qed.
