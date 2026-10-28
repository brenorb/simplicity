(** Original one-point descending inner loop, deriving both digit dispatches
    from stored representations and composing its actual counter control. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_strauss_digit_guard C.jet_secp_generator_loop_control.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Local Opaque secp_ge.
Set Default Timeout 10.
Lemma strauss_single_loop_source : generator_nongenerator_statement=
 Ssequence (Sset _np (Ecast (Econst_int Int.zero tint) tulong))
 (Sloop (Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _np tulong) (Etempvar _no tulong) tint) Sskip Sbreak)
  (Ssequence (strauss_digit_dispatch false) (strauss_digit_dispatch true)))
  (Sset _np (Ebinop Oadd (Etempvar _np tulong) (Econst_int Int.one tint) tulong))).
Proof. reflexivity. Qed.
Lemma exec_strauss_single_loop_from_dispatches e le m lm mm lh mh :
 le!_no=Some (Vlong Int64.one) ->
 Clight2.exec_stmt secp_ge e (PTree.set _np (Vlong Int64.zero) le) m
  (strauss_digit_dispatch false) E0 lm mm Out_normal ->
 Clight2.exec_stmt secp_ge e lm mm (strauss_digit_dispatch true) E0 lh mh Out_normal ->
 lh!_np=Some (Vlong Int64.zero) -> lh!_no=Some (Vlong Int64.one) ->
 Clight2.exec_stmt secp_ge e le m generator_nongenerator_statement E0
  (PTree.set _np (Vlong Int64.one) lh) mh Out_normal.
Proof.
 intros No Low High NPf Nof;pose (l0:=PTree.set _np (Vlong Int64.zero) le).
 rewrite strauss_single_loop_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=l0) (m1:=m).
 - apply exec_Sset;eapply eval_Ecast;[constructor|reflexivity].
 - eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0)
    (le1:=lh) (m1:=mh) (out1:=Out_normal)
    (le2:=PTree.set _np (Vlong Int64.one) lh) (m2:=mh).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=l0) (m1:=m).
     * eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|constructor].
       eapply eval_Ebinop with (v1:=Vlong Int64.zero) (v2:=Vlong Int64.one).
       -- apply eval_Etempvar;unfold l0;apply PTree.gss.
       -- apply eval_Etempvar;unfold l0;rewrite PTree.gso by discriminate;exact No.
       -- reflexivity.
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Low|exact High].
   + constructor.
   + apply exec_Sset;eapply eval_Ebinop;
      [apply eval_Etempvar;exact NPf|constructor|reflexivity].
   + eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
     eapply exec_Sseq_2;[|discriminate].
     eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
     eapply eval_Ebinop with (v1:=Vlong Int64.one) (v2:=Vlong Int64.one).
     * apply eval_Etempvar;apply PTree.gss.
     * apply eval_Etempvar;rewrite PTree.gso by discriminate;exact Nof.
     * reflexivity.
Qed.

Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns
 C.jet_secp_field_mul_small C.jet_secp_globalz_loop C.jet_secp_globalz_pass2 C.jet_secp_globalz_word_walk
 C.jet_secp_strauss_wnaf_calls C.jet_secp_wnaf5_literal C.jet_secp_scalar_table_literal C.jet_secp_rescale_literal
 C.jet_secp_canonical_zero C.jet_secp_strauss_digit_add
 C.jet_secp_field_read_preservation C.jet_secp_curve_frame
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.

Definition strauss_point_loop_temps le bp bt bx i bits1 bitslam d1 dlam :=
 PTree.set _np (Vlong Int64.one)
 (strauss_digit_dispatch_temps true
  (strauss_digit_dispatch_temps false (PTree.set _np (Vlong Int64.zero) le) bp bt bx i bits1 d1)
  bp bt bx i bitslam dlam).
Theorem exec_strauss_single_point_loop (d1 dlam:Ty.tySem literal_wnaf5_digit)
 xs ys aux x y z (ax ay az:Ty.tySem (Word 8)) e le m br bs bp bd bt bx i bits1 bitslam :
 0<=i<129 -> 0<=bits1<=129 -> 0<=bitslam<=129 -> NoDup [br;bd;bs;bp;bt;bx] ->
 e!_tmpa=Some (bd,Tstruct __6121 noattr) ->
 e!_secp256k1_ecmult_table_get_ge=None -> e!_secp256k1_ecmult_table_get_ge_lambda=None ->
 e!_secp256k1_gej_add_ge_var=None ->
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_i=Some (Vint (Int.repr i)) -> le!_no=Some (Vlong Int64.one) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 Mem.load Mint32 m bp 1032=Some (Vint (Int.repr bits1)) ->
 Mem.load Mint32 m bp 1036=Some (Vint (Int.repr bitslam)) ->
 (i<bits1 -> Mem.load Mint32 m bp (4*i)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value d1)))) ->
 (i<bitslam -> Mem.load Mint32 m bp (516+4*i)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value dlam)))) ->
 (bits1<=i -> d1=inl tt) -> (bitslam<=i -> dlam=inl tt) ->
 globalz_table_rep m bt xs ys -> globalz_table_bounds xs ys ->
 (forall k,(k<8)%nat -> mul_small_input_bounds (ys k)) ->
 (forall k,(k<8)%nat -> fe_at m bx (40*Z.of_nat k) (words5 (aux k))) ->
 (forall k,(k<8)%nat -> square_input_bounds (aux k)) ->
 (forall k,(k<8)%nat -> rescale_field_output (aux k)=
  @C.jet_secp_beta_spec.literal_fe_multiply_beta Alg.CoreFunSem (rescale_field_output (xs k))) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=((ax,ay),az) ->
 fe_at m br 0 (words5 x) -> fe_at m br 40 (words5 y) -> fe_at m br 80 (words5 z) ->
 Mem.load Mint32 m br 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m bd 0 88 Cur Freeable ->
 Mem.range_perm m bt 0 704 Cur Freeable -> Mem.range_perm m bx 0 320 Cur Freeable ->
 exists mf ox oy oz,
 Clight2.exec_stmt secp_ge e le m generator_nongenerator_statement E0
  (strauss_point_loop_temps le bp bt bx i bits1 bitslam d1 dlam) mf Out_normal /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  strauss_digit_action true dlam xs ys (strauss_digit_action false d1 xs ys ((ax,ay),az)) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf bd 0 88 Cur Freeable /\
 Mem.range_perm mf bt 0 704 Cur Freeable /\ Mem.range_perm mf bx 0 320 Cur Freeable /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (fun b _=>b<>br /\ b<>bd) m mf.
Proof.
 intros Index Len1 LenLam Separate Local Get GetLam Add R State I No PS PT PX Count1 CountLam
  Load1 LoadLam Absent1 AbsentLam Table Bounds Tight Aux AuxBounds AuxLiteral BX BY BZ Repr X Y Z Flag FreeR FreeD FreeT FreeX.
 assert (Sep4:NoDup [br;bd;bt;bx]).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;repeat rewrite NoDup_cons_iff;cbn [In] in Separate|-*;intuition congruence. }
 assert (Protected:forall b,In b [bs;bp;bt;bx] -> b<>br /\ b<>bd).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;
   intros b Member;cbn [In] in Member;intuition congruence. }
 pose (l0:=PTree.set _np (Vlong Int64.zero) le).
 assert (R0:l0!_r=Some (Vptr br Ptrofs.zero)) by (unfold l0;rewrite PTree.gso by discriminate;exact R).
 assert (S0:l0!_state=Some (Vptr bs Ptrofs.zero)) by (unfold l0;rewrite PTree.gso by discriminate;exact State).
 assert (I0:l0!_i=Some (Vint (Int.repr i))) by (unfold l0;rewrite PTree.gso by discriminate;exact I).
 destruct (exec_strauss_digit_dispatch false d1 xs ys aux x y z ax ay az e l0 m br bs bp bd bt bx i bits1
  Index Len1 Sep4 Local Get Add R0 S0 (PTree.gss _ _ _) I0 PS Count1
  ltac:(intro H;exact (Load1 H)) Absent1 PT PX Table Bounds Tight Aux AuxBounds AuxLiteral
  BX BY BZ Repr X Y Z Flag FreeR FreeD FreeT FreeX)
  as (ml & lx & ly & lz & Low & XL & YL & ZL & FlagL & BXL & BYL & BZL & LiteralL &
   FRL & FDL & FTL & FXL & KeepL & ReadonlyL & FrameL).
 pose (ll:=strauss_digit_dispatch_temps false l0 bp bt bx i bits1 d1).
 assert (Saved:forall chunk b ofs value,b<>br /\ b<>bd ->
  Mem.load chunk m b ofs=Some value -> Mem.load chunk ml b ofs=Some value).
 { intros chunk b ofs value Outside Load;rewrite (proj1 FrameL chunk b ofs);[exact Load| |intros;exact Outside].
   eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
    [eapply Mem.load_valid_access;exact Load|apply perm_any_N]. }
 assert (PSL:Mem.load Mptr ml bs 16=Some (Vptr bp Ptrofs.zero)).
 { apply Saved;[apply Protected;clear;cbn [In];tauto|exact PS]. }
 assert (PTL:Mem.load Mptr ml bs 8=Some (Vptr bt Ptrofs.zero)).
 { apply Saved;[apply Protected;clear;cbn [In];tauto|exact PT]. }
 assert (PXL:Mem.load Mptr ml bs 0=Some (Vptr bx Ptrofs.zero)).
 { apply Saved;[apply Protected;clear;cbn [In];tauto|exact PX]. }
 assert (CountL:Mem.load Mint32 ml bp 1036=Some (Vint (Int.repr bitslam))).
 { apply Saved;[apply Protected;clear;cbn [In];tauto|exact CountLam]. }
 assert (LoadL:i<bitslam -> Mem.load Mint32 ml bp (516+4*i)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value dlam)))).
 { intro H;apply Saved;[apply Protected;clear;cbn [In];tauto|apply LoadLam;exact H]. }
 assert (TableL:globalz_table_rep ml bt xs ys).
 { intros k K;destruct (Table k K) as (TX & TY & TF);split.
   - eapply field_at_lframe;[exact TX|exact FrameL|intros;apply Protected;clear;cbn [In];tauto].
   - split.
     + eapply field_at_lframe;[exact TY|exact FrameL|intros;apply Protected;clear;cbn [In];tauto].
     + apply Saved;[apply Protected;clear;cbn [In];tauto|exact TF]. }
 assert (AuxL:forall k,(k<8)%nat -> fe_at ml bx (40*Z.of_nat k) (words5 (aux k))).
 { intros k K;eapply field_at_lframe;[apply Aux;exact K|exact FrameL|intros;apply Protected;clear;cbn [In];tauto]. }
 assert (RL:ll!_r=Some (Vptr br Ptrofs.zero)).
 { unfold ll;rewrite strauss_digit_dispatch_other by (clear;cbn [In];intuition discriminate);exact R0. }
 assert (SL:ll!_state=Some (Vptr bs Ptrofs.zero)).
 { unfold ll;rewrite strauss_digit_dispatch_other by (clear;cbn [In];intuition discriminate);exact S0. }
 assert (IL:ll!_i=Some (Vint (Int.repr i))).
 { unfold ll;rewrite strauss_digit_dispatch_other by (clear;cbn [In];intuition discriminate);exact I0. }
 assert (NPL:ll!_np=Some (Vlong Int64.zero)).
 { unfold ll;rewrite strauss_digit_dispatch_other by (clear;cbn [In];intuition discriminate);unfold l0;apply PTree.gss. }
 destruct (exec_strauss_digit_dispatch true dlam xs ys aux lx ly lz
  (rescale_field_output lx) (rescale_field_output ly) (rescale_field_output lz)
  e ll ml br bs bp bd bt bx i bitslam Index LenLam Sep4 Local GetLam Add RL SL NPL IL PSL CountL LoadL AbsentLam
  PTL PXL TableL Bounds Tight AuxL AuxBounds AuxLiteral BXL BYL BZL eq_refl XL YL ZL FlagL FRL FDL FTL FXL)
  as (mf & ox & oy & oz & High & XO & YO & ZO & FlagO & BXO & BYO & BZO & LiteralH &
   FRF & FDF & FTF & FXF & KeepH & ReadonlyH & FrameH).
 pose (lh:=strauss_digit_dispatch_temps true ll bp bt bx i bitslam dlam).
 assert (NPH:lh!_np=Some (Vlong Int64.zero)).
 { unfold lh;rewrite strauss_digit_dispatch_other by (clear;cbn [In];intuition discriminate);exact NPL. }
 assert (NoH:lh!_no=Some (Vlong Int64.one)).
 { unfold lh,ll;rewrite !strauss_digit_dispatch_other by (clear;cbn [In];intuition discriminate).
   unfold l0;rewrite PTree.gso by discriminate;exact No. }
 exists mf,ox,oy,oz;split.
 - exact (exec_strauss_single_loop_from_dispatches e le m ll ml lh mf No Low High NPH NoH).
 - rewrite LiteralL in LiteralH.
   split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FlagO|];
   split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];split;[exact LiteralH|];
   split;[exact FRF|];split;[exact FDF|];split;[exact FTF|];split;[exact FXF|];split.
   + eapply keeps_permissions_trans;[exact KeepL|exact KeepH].
   + split.
     * eapply preserved_trans;[exact ReadonlyL|exact ReadonlyH].
     * eapply lframe_trans;[exact FrameL|exact FrameH].
Qed.

Lemma strauss_point_loop_other le bp bt bx i bits1 bitslam d1 dlam id :
 ~In id [_np;_n;_t'8;_t'9;_t'10;_t'11;_t'19;_t'20;_t'21;_t'22;_t'23;_t'24;_t'25;_t'26;_t'27;_t'28;_t'29] ->
 (strauss_point_loop_temps le bp bt bx i bits1 bitslam d1 dlam)!id=le!id.
Proof.
 intro Outside;unfold strauss_point_loop_temps.
 rewrite PTree.gso by (intro Eq;apply Outside;subst id;cbn [In];tauto).
 rewrite !strauss_digit_dispatch_other by (cbn [In] in Outside|-*;tauto).
 rewrite PTree.gso by (intro Eq;apply Outside;subst id;cbn [In];tauto);reflexivity.
Qed.

