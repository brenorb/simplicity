(** Both original generator digit dispatches at arbitrary shared Z. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_clight_forward C.jet_clight_readonly_frame C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_generator_globals C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_array
 C.jet_secp_wnaf_literal_values C.jet_secp_add_literal C.jet_secp_generate_literal
 C.jet_secp_rescale_literal C.jet_secp_canonical_zero C.jet_secp_generator_digit_control
 C.jet_secp_generator_dispatch_general.
Require Import C.jet_secp_closed_helpers C.jet_clight_internal_frame
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_generator_pair_general C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_generator_globals C.jet_elements_taptweak_curve_transport.
Require Import C.jet_elements_taptweak_internal C.jet_elements_taptweak_generator_dispatch.
Lemma elements_taptweak_generator_pair_closed:
 closed_stmtb elements_taptweak_curve_helpers
 (Ssequence(generator_digit_dispatch false)(generator_digit_dispatch true))=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge rescale_field_output literal_gej_ge_add literal_generate_small literal_gej_zinv.
Theorem exec_elements_taptweak_generator_pair_scaled d1 d128 x y z inv (ax ay az s:Ty.tySem (Word 8))
 e le m i bits1 bits128 b1 b128 bp ba bb :
 0<=i<129 -> 0<=bits1<=129 -> 0<=bits128<=129 ->
 wnaf_literal_valid d1 -> wnaf_literal_valid d128 -> NoDup [bp;ba;bb;b1;b128] ->
 (forall h,elements_taptweak_generator_table_state h m) ->
 le!_r=Some (Vptr bp Ptrofs.zero) -> le!_i=Some (Vint (Int.repr i)) ->
 le!_bits_ng_1=Some (Vint (Int.repr bits1)) -> le!_bits_ng_128=Some (Vint (Int.repr bits128)) ->
 e!_wnaf_ng_1=Some (b1,tarray tint 129) -> e!_wnaf_ng_128=Some (b128,tarray tint 129) ->
 e!_tmpa=Some (ba,curve_ge_type) -> e!_Z=Some (bb,curve_fe_type) ->
 e!_secp256k1_ecmult_table_get_ge_storage=None -> e!_secp256k1_gej_add_zinv_var=None ->
 e!(generator_table_id false)=None -> e!(generator_table_id true)=None ->
 (i<bits1 -> Mem.load Mint32 m b1 (4*i)=Some (Vint (Int.repr (wnaf_literal_value d1)))) ->
 (i<bits128 -> Mem.load Mint32 m b128 (4*i)=Some (Vint (Int.repr (wnaf_literal_value d128)))) ->
 (bits1<=i -> d1=inl tt) -> (bits128<=i -> d128=inl tt) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> square_input_bounds inv ->
 radix_value inv mod feP=@toZ (WordToZ 8) s mod feP ->
 ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=((ax,ay),az) ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m bb 0 (words5 inv) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bb 0 40 Cur Freeable -> exists mf ox oy oz,
 Clight2.exec_stmt elements_taptweak_ge e le m
  (Ssequence (generator_digit_dispatch false) (generator_digit_dispatch true)) E0
  (generator_digit_temps true (generator_digit_temps false le i bits1 d1) i bits128 d128) mf Out_normal /\
 fe_at mf bp 0 (words5 ox) /\ fe_at mf bp 40 (words5 oy) /\ fe_at mf bp 80 (words5 oz) /\
 Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 fe_at mf bb 0 (words5 inv) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bb 0 40 Cur Freeable /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  generator_digit_action_scaled true s d128 (generator_digit_action_scaled false s d1 ((ax,ay),az)) /\
 (forall h,elements_taptweak_generator_table_state h mf) /\ lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m mf.
Proof.
 intros Index Len1 Len128 Valid1 Valid128 Sep Tables PR PI PL1 PL128 Array1 Array128 EA EZ EL EAdd ET1 ET128
  Load1 Load128 Absent1 Absent128 BX BY BZ BI Scale Repr Flag X Y ZAt Inv PF AF IF.
 pose proof Sep as Sep0;repeat rewrite NoDup_cons_iff in Sep0;cbn [In] in Sep0.
 assert (Sep3:NoDup [bp;ba;bb]) by
  (repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence).
 assert (B128:b128<>bp /\ b128<>ba /\ b128<>bb) by intuition congruence.
 destruct (exec_elements_taptweak_generator_digit_dispatch_scaled false d1 x y z inv ax ay az s e le m i bits1 b1 bp ba bb
  Index Len1 Valid1 Sep3 Tables PR PI PL1 Array1 EA EZ EL EAdd ET1 Load1 Absent1
  BX BY BZ BI Scale Repr Flag X Y ZAt Inv PF AF IF)
  as (ml & lx & ly & lz & Low & XL & YL & ZL & FlagL & InvL & PFL & AFL & IFL & BXL & BYL & BZL & LiteralL & TablesL & FrameL).
 pose (ll:=generator_digit_temps false le i bits1 d1).
 assert (PRL:ll!_r=Some (Vptr bp Ptrofs.zero)).
 { unfold ll;rewrite generator_digit_temps_other by discriminate;exact PR. }
 assert (PIL:ll!_i=Some (Vint (Int.repr i))).
 { unfold ll;rewrite generator_digit_temps_other by discriminate;exact PI. }
 assert (PL128L:ll!_bits_ng_128=Some (Vint (Int.repr bits128))).
 { unfold ll;rewrite generator_digit_temps_other by discriminate;exact PL128. }
 assert (Load128L:i<bits128 -> Mem.load Mint32 ml b128 (4*i)=Some (Vint (Int.repr (wnaf_literal_value d128)))).
 { intro Range;pose proof (Load128 Range) as Load.
   rewrite (proj1 FrameL Mint32 b128 (4*i));[exact Load| |].
   - eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
      [eapply Mem.load_valid_access;exact Load|constructor].
   - intros;exact B128. }
 destruct (exec_elements_taptweak_generator_digit_dispatch_scaled true d128 lx ly lz inv
  (rescale_field_output lx) (rescale_field_output ly) (rescale_field_output lz) s e ll ml i bits128 b128 bp ba bb
  Index Len128 Valid128 Sep3 TablesL PRL PIL PL128L Array128 EA EZ EL EAdd ET128 Load128L Absent128
  BXL BYL BZL BI Scale eq_refl FlagL XL YL ZL InvL PFL AFL IFL)
  as (mf & ox & oy & oz & High & XO & YO & ZO & FlagO & InvO & PFO & AFO & IFO & BXO & BYO & BZO & LiteralO & TablesO & FrameO).
 assert (Frame:lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m mf) by (eapply lframe_trans;eassumption).
 assert (Literal:((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  generator_digit_action_scaled true s d128 (generator_digit_action_scaled false s d1 ((ax,ay),az))).
 { change (((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
    generator_digit_action_scaled true s d128 ((rescale_field_output lx,rescale_field_output ly),rescale_field_output lz)) in LiteralO.
   change (((rescale_field_output lx,rescale_field_output ly),rescale_field_output lz)=
    generator_digit_action_scaled false s d1 ((ax,ay),az)) in LiteralL.
   rewrite LiteralL in LiteralO;exact LiteralO. }
 exists mf,ox,oy,oz;split;[|repeat first [assumption|split]].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=ll) (m1:=ml);[exact Low|exact High].
Qed.

Lemma elements_taptweak_generator_pair_effects e le m trace lef mf out:
 Clight2.exec_stmt elements_taptweak_ge e le m
 (Ssequence(generator_digit_dispatch false)(generator_digit_dispatch true))trace lef mf out ->
 plain_env e ->keeps_permissions m mf /\readonly_preserved m mf.
Proof.
 intros Run Plain;split.
 - eapply(proj1(internal_exec_keeps_permissions _ _ elements_taptweak_internal_table));
   [exact Run|exact Plain|exact elements_taptweak_generator_pair_closed].
 - eapply(proj1(internal_exec_preserved _ _ elements_taptweak_internal_table));
   [exact Run|exact Plain|exact elements_taptweak_generator_pair_closed].
Qed.
Lemma elements_taptweak_generator_tables_readonly m mf:
 (forall h,elements_taptweak_generator_table_state h m) ->readonly_preserved m mf ->
 forall h,elements_taptweak_generator_table_state h mf.
Proof. intros Tables Read h;eapply elements_taptweak_generator_readonly;[apply Tables|exact Read]. Qed.
