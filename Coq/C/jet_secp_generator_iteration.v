(** One complete original descending-loop arithmetic body in generate's
    no-nongenerator-points case. Entry/wNAF initialization and loop induction
    remain caller obligations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_clight_forward C.jet_clight_readonly_frame C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_square_execution C.jet_secp_generator_globals C.jet_secp_generator_digit_add
 C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_array C.jet_secp_wnaf_literal_values
 C.jet_secp_double_loose_literal C.jet_secp_double_literal C.jet_secp_add_literal
 C.jet_secp_generate_literal C.jet_secp_rescale_literal C.jet_secp_canonical_zero.
Require Import C.jet_secp_generator_digit_control C.jet_secp_generator_loop_control.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output literal_gej_double literal_gej_ge_add literal_generate_small.

Definition generator_digit_action high (digit : Ty.tySem literal_wnaf_digit)
 (point : Ty.tySem literal_generator_jacobian) := match digit with
 | inl _=>point
 | inr word=>@literal_gej_ge_add Alg.CoreFunSem (point,@literal_generate_small high Alg.CoreFunSem word)
 end.

Theorem exec_generator_iteration d1 d128 x y z inv (ax ay az : Ty.tySem (Word 8))
 e le m i bits1 bits128 b1 b128 bp ba bb :
 0<=i<129 -> 0<=bits1<=129 -> 0<=bits128<=129 ->
 wnaf_literal_valid d1 -> wnaf_literal_valid d128 -> NoDup [bp;ba;bb;b1;b128] ->
 (forall h,generator_table_state h m) ->
 le!_r=Some (Vptr bp Ptrofs.zero) -> le!_no=Some (Vlong Int64.zero) ->
 le!_i=Some (Vint (Int.repr i)) ->
 le!_bits_ng_1=Some (Vint (Int.repr bits1)) -> le!_bits_ng_128=Some (Vint (Int.repr bits128)) ->
 e!_wnaf_ng_1=Some (b1,tarray tint 129) -> e!_wnaf_ng_128=Some (b128,tarray tint 129) ->
 e!_tmpa=Some (ba,curve_ge_type) -> e!_Z=Some (bb,curve_fe_type) ->
 e!_secp256k1_ecmult_table_get_ge_storage=None -> e!_secp256k1_gej_add_zinv_var=None ->
 e!_secp256k1_gej_double_var=None -> e!(generator_table_id false)=None -> e!(generator_table_id true)=None ->
 (i<bits1 -> Mem.load Mint32 m b1 (4*i)=Some (Vint (Int.repr (wnaf_literal_value d1)))) ->
 (i<bits128 -> Mem.load Mint32 m b128 (4*i)=Some (Vint (Int.repr (wnaf_literal_value d128)))) ->
 (bits1<=i -> d1=inl tt) -> (bits128<=i -> d128=inl tt) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> square_input_bounds inv ->
 radix_value inv mod feP=1 ->
 ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=((ax,ay),az) ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m bb 0 (words5 inv) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bb 0 40 Cur Freeable -> exists mf ox oy oz,
 Clight2.exec_stmt secp_ge e le m generator_loop_arithmetic E0
   (generator_digit_temps true (generator_digit_temps false (PTree.set _np (Vlong Int64.zero) le) i bits1 d1)
     i bits128 d128) mf Out_normal /\
 fe_at mf bp 0 (words5 ox) /\ fe_at mf bp 40 (words5 oy) /\ fe_at mf bp 80 (words5 oz) /\
 Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Bit.toBool
   (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 fe_at mf bb 0 (words5 inv) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bb 0 40 Cur Freeable /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
   generator_digit_action true d128 (generator_digit_action false d1
     (@literal_gej_double Alg.CoreFunSem ((ax,ay),az))) /\
 (forall h,generator_table_state h mf) /\ lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m mf.
Proof.
 intros Index Len1 Len128 Valid1 Valid128 Sep Tables PR No PI PL1 PL128 Array1 Array128 EA EZ EL EAdd ED ET1 ET128
   Load1 Load128 Absent1 Absent128 BX BY BZ BI One Repr Flag X Y ZAt Inv PF AF IF.
 pose proof Sep as Sep0;repeat rewrite NoDup_cons_iff in Sep0;cbn [In] in Sep0.
 assert (Sep3 : NoDup [bp;ba;bb]) by
   (repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence).
 assert (BA : ba<>bp) by intuition congruence.
 assert (BB : bb<>bp) by intuition congruence.
 assert (B1 : b1<>bp) by intuition congruence.
 assert (B128 : b128<>bp /\ b128<>ba /\ b128<>bb) by intuition congruence.
 assert (RX : radix_value x mod feP=@toZ (WordToZ 8) ax mod feP).
 { assert (AX : rescale_field_output x=ax) by congruence;rewrite <-AX,rescale_field_output_value,
     field_prime_matches_normalizer,Z.mod_mod by (unfold feP,feR;lia);reflexivity. }
 assert (RY : radix_value y mod feP=@toZ (WordToZ 8) ay mod feP).
 { assert (AY : rescale_field_output y=ay) by congruence;rewrite <-AY,rescale_field_output_value,
     field_prime_matches_normalizer,Z.mod_mod by (unfold feP,feR;lia);reflexivity. }
 assert (RZ : radix_value z mod feP=@toZ (WordToZ 8) az mod feP).
 { assert (AZ : rescale_field_output z=az) by congruence;rewrite <-AZ,rescale_field_output_value,
     field_prime_matches_normalizer,Z.mod_mod by (unfold feP,feR;lia);reflexivity. }
 destruct (eval_double_var_loose_literal x y z ax ay az m bp BX BY BZ RX RY RZ Flag X Y ZAt PF)
   as (md & dx & dy & dz & Double & XD & YD & ZD & FlagD & PFD & BXD & BYD & BZD & LiteralD & FrameD).
 assert (InvD : fe_at md bb 0 (words5 inv)).
 { eapply field_at_lframe;[exact Inv|exact FrameD|];intros;exact BB. }
 assert (AFD : Mem.range_perm md ba 0 88 Cur Freeable).
 { eapply curve_keep_free;[lia|exact AF|exact FrameD|];intros;exact BA. }
 assert (IFD : Mem.range_perm md bb 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact IF|exact FrameD|];intros;exact BB. }
 assert (TablesD : forall h,generator_table_state h md).
 { intro h;pose proof (Tables h) as [Table Readonly];pose proof Table as [Valid _].
   assert (Outside : generator_table_block h<>bp).
   { intro Equal;rewrite Equal in Readonly.
     destruct (proj1 (Readonly 0 Cur Freeable) (PF 0 ltac:(lia))) as [_ Order];inversion Order. }
   pose proof (generator_table_rep_lframe h m md _ Table FrameD ltac:(intros;exact Outside)) as TF.
   split;[exact TF|].
   eapply readonly_bounds_transport;[exact Valid|exact Readonly| |exact (proj1 (proj2 TF))].
   exact (proj2 (clight_exec_forward secp_ge) _ _ _ _ _ _ Double). }
 set (ln:=PTree.set _np (Vlong Int64.zero) le).
 assert (PRN : ln!_r=Some (Vptr bp Ptrofs.zero)) by (unfold ln;rewrite PTree.gso by discriminate;exact PR).
 assert (PIN : ln!_i=Some (Vint (Int.repr i))) by (unfold ln;rewrite PTree.gso by discriminate;exact PI).
 assert (PL1N : ln!_bits_ng_1=Some (Vint (Int.repr bits1))) by (unfold ln;rewrite PTree.gso by discriminate;exact PL1).
 assert (Load1D : i<bits1 -> Mem.load Mint32 md b1 (4*i)=Some (Vint (Int.repr (wnaf_literal_value d1)))).
 { intro Range;pose proof (Load1 Range) as Load.
   rewrite (proj1 FrameD Mint32 b1 (4*i));[exact Load| |].
   - eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
       [eapply Mem.load_valid_access;exact Load|constructor].
   - intros;exact B1. }
 destruct (exec_generator_digit_dispatch false d1 dx dy dz inv
   (rescale_field_output dx) (rescale_field_output dy) (rescale_field_output dz) e ln md i bits1 b1 bp ba bb
   Index Len1 Valid1 Sep3 TablesD PRN PIN PL1N Array1 EA EZ EL EAdd ET1 Load1D Absent1
   BXD BYD BZD BI One eq_refl FlagD XD YD ZD InvD PFD AFD IFD)
   as (ml & lx & ly & lz & Low & XL & YL & ZL & FlagL & InvL & PFL & AFL & IFL & BXL & BYL & BZL & LiteralL & TablesL & FrameL).
 assert (FrameDL : lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m ml).
 { eapply lframe_trans;[|exact FrameL];eapply lframe_implies;[exact FrameD|];intros b pos Outside Valid;tauto. }
 set (ll:=generator_digit_temps false ln i bits1 d1).
 assert (PRL : ll!_r=Some (Vptr bp Ptrofs.zero)).
 { unfold ll;rewrite generator_digit_temps_other by discriminate;exact PRN. }
 assert (PIL : ll!_i=Some (Vint (Int.repr i))).
 { unfold ll;rewrite generator_digit_temps_other by discriminate;exact PIN. }
 assert (PL128L : ll!_bits_ng_128=Some (Vint (Int.repr bits128))).
 { unfold ll;rewrite generator_digit_temps_other by discriminate;unfold ln;rewrite PTree.gso by discriminate;exact PL128. }
 assert (Load128L : i<bits128 -> Mem.load Mint32 ml b128 (4*i)=Some (Vint (Int.repr (wnaf_literal_value d128)))).
 { intro Range;pose proof (Load128 Range) as Load.
   rewrite (proj1 FrameDL Mint32 b128 (4*i));[exact Load| |].
   - eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
       [eapply Mem.load_valid_access;exact Load|constructor].
   - intros;exact B128. }
 destruct (exec_generator_digit_dispatch true d128 lx ly lz inv
   (rescale_field_output lx) (rescale_field_output ly) (rescale_field_output lz) e ll ml i bits128 b128 bp ba bb
   Index Len128 Valid128 Sep3 TablesL PRL PIL PL128L Array128 EA EZ EL EAdd ET128 Load128L Absent128
   BXL BYL BZL BI One eq_refl FlagL XL YL ZL InvL PFL AFL IFL)
   as (mf & ox & oy & oz & High & XO & YO & ZO & FlagO & InvO & PFO & AFO & IFO & BXO & BYO & BZO & LiteralO & TablesO & FrameO).
 assert (Frame : lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m mf) by (eapply lframe_trans;eassumption).
 assert (Literal : ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
   generator_digit_action true d128 (generator_digit_action false d1 (@literal_gej_double Alg.CoreFunSem ((ax,ay),az)))).
 { change (((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
     generator_digit_action true d128 ((rescale_field_output lx,rescale_field_output ly),rescale_field_output lz)) in LiteralO.
   change (((rescale_field_output lx,rescale_field_output ly),rescale_field_output lz)=
     generator_digit_action false d1 ((rescale_field_output dx,rescale_field_output dy),rescale_field_output dz)) in LiteralL.
   rewrite LiteralL,LiteralD in LiteralO;exact LiteralO. }
 exists mf,ox,oy,oz;split;[|repeat first [assumption|split]].
 rewrite generator_loop_arithmetic_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=md).
 - unfold generator_double_statement;eapply exec_curve_call with
     (vargs:=[Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vlong Int64.zero]) (v:=Vundef).
   + unfold secp_pure;repeat first [left;reflexivity|right].
   + exact ED.
   + eapply eval_Econs;[apply eval_Etempvar;exact PR|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;exact PR|reflexivity|].
     eapply eval_Econs.
     * eapply eval_Ecast;[constructor|reflexivity].
     * reflexivity.
     * constructor.
   + exact Double.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=ln) (m1:=md).
   + apply exec_generator_nongenerator_empty;exact No.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=ll) (m1:=ml);[exact Low|exact High].
Qed.
