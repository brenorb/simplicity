(** Derive all six original public calls of the extended jet for every input:
    the incoming-infinity and every finite H/I outcome. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.jet_exec C.jet_encoding C.jet_readBit_layout C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
  C.jet_sx_mem C.jet_sx_exec C.jet_sx_state C.jet_secp_linkage C.jets_secp C.jet_secp_frame
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_fe_clear_memory C.jet_secp_multiply_normalize_bridge
  C.jet_secp_multiply_finish_product C.jet_secp_multiply_writer_bridge C.jet_secp_square_spec_bridge
  C.jet_secp_square_columns C.jet_secp_field_weak_tight C.jet_secp_mixed_finite_return
  C.jet_secp_mixed_ratio_function C.jet_secp_mixed_public_reads C.jet_secp_rescale_public_reads
  C.jet_secp_mixed_ex_public_body C.jet_secp_curve_frame C.jet_secp_field_read_preservation
  C.jet_secp_rescale_writer C.jet_secp_point_three_general_writes C.jet_secp_point_write_run
  C.jet_secp_owned_write_field C.jet_secp_owned_write_preservation C.jet_secp_canonical_zero
  C.jet_secp_double_all_calls C.jet_secp_curve_statements C.jet_secp_rescale_literal
  C.jet_secp_point_write_field C.jet_secp_local_regions C.jet_secp_mixed_ex_public_rest
  C.jet_secp_mixed_function_ratio C.jet_secp_mixed_finite_ratio C.jet_secp_mixed_ratio_branches
  C.jet_secp_mixed_body C.jet_secp_mixed_difference C.jet_secp_mixed_finite_prefix
  C.jet_secp_mixed_zero_return C.jet_secp_double_var_owned C.jet_secp_mixed_dispatch_literal C.jet_secp_mixed_literal_bridge C.jet_secp_double_coordinate_numeric.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Simplicity.Translate.encode.

Definition mixed_ex_output (x y z u v : Ty.tySem (Word 8)) :=
  let fl := bit_int (Bit.toBool (@canonical_fe_is_zero Simplicity.Alg.CoreFunSem z)) in
  Simplicity.Translate.encode (rescale_field_output (mixed_body_ratio_words fl (square_reader_rho x)
    (square_reader_rho y) (square_reader_rho z) (square_reader_rho u) (square_reader_rho v))) ++
  ((Simplicity.Translate.encode (rescale_field_output (mixed_body_x_words fl (square_reader_rho x)
      (square_reader_rho y) (square_reader_rho z) (square_reader_rho u) (square_reader_rho v))) ++
    Simplicity.Translate.encode (rescale_field_output (mixed_body_y_words fl (square_reader_rho x)
      (square_reader_rho y) (square_reader_rho z) (square_reader_rho u) (square_reader_rho v)))) ++
    Simplicity.Translate.encode (rescale_field_output (mixed_body_z_words fl (square_reader_rho x)
      (square_reader_rho y) (square_reader_rho z) (square_reader_rho u) (square_reader_rho v)))).

Lemma mixed_h_words_bounds x z u :
  fe_limbs_ok (Int64.unsigned (x 0%nat)) (Int64.unsigned (x 1%nat))
    (Int64.unsigned (x 2%nat)) (Int64.unsigned (x 3%nat)) (Int64.unsigned (x 4%nat)) ->
  square_input_bounds z -> square_input_bounds u -> square_input_bounds (mixed_h_words x z u).
Proof.
  intros Pos BZ BU;unfold mixed_h_words;apply (proj2 (mixed_difference_numeric _ _
    (mixed_positioned_tight _ Pos)
    (double_mul_tight _ _ BU (double_tight_loose _ (double_square_tight _ BZ))))).
Qed.

Lemma mixed_ratio_words_bounds flag x y z u v :
  fe_limbs_ok (Int64.unsigned (x 0%nat)) (Int64.unsigned (x 1%nat))
    (Int64.unsigned (x 2%nat)) (Int64.unsigned (x 3%nat)) (Int64.unsigned (x 4%nat)) ->
  square_input_bounds y -> square_input_bounds z -> square_input_bounds u ->
  square_input_bounds (mixed_body_ratio_words flag x y z u v).
Proof.
  intros Pos BY BZ BU;unfold mixed_body_ratio_words,mixed_finite_ratio_words,mixed_zero_words.
  destruct (Int.eq flag Int.zero);[|exact square_zero_bounds].
  destruct (Z.eqb (radix_value (mixed_h_words x z u) mod feP) 0).
  - destruct (Z.eqb (radix_value (mixed_i_words y z v) mod feP) 0);[exact BY|exact square_zero_bounds].
  - exact (mixed_h_words_bounds x z u Pos BZ BU).
Qed.

Local Ltac keep_ex_field F Frame :=
  eapply field_at_lframe;[exact F|exact Frame|];intros;repeat split;congruence.
Local Ltac keep_ex_free F Frame :=
  eapply curve_keep_free;[lia|exact F|exact Frame|];intros;repeat split;congruence.

Theorem exec_mixed_ex_rest le m0 bd dbase bw outedge cursor N bi edge rc
    (x y z u v : Ty.tySem (Word 8)) m bp ba bl br :
  le!_dst=Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m0 bd dbase bw outedge cursor N -> 1024<=N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits y)) ->
  frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits z)) ->
  frame_input_cells_at m0 bi edge (rc+768) (map Some (frame_input_word_bits u)) ->
  frame_input_cells_at m0 bi edge (rc+1024) (map Some (frame_input_word_bits v)) ->
  0<=rc -> rc+1280<=Int64.max_unsigned ->
  NoDup [bl;bp;ba;br] ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m bl 0 16 Cur Freeable -> Mem.range_perm m br 0 40 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc ->
  xsep (extA m0 bd bw bi) [(bp,0);(ba,0);(bl,0);(br,0)] ->
  finv m0 bd dbase bw outedge cursor N bi m false [] ->
  exists mf,
  Clight2.exec_stmt secp_ge (mixed_ex_public_env bl bp ba br) le m mixed_ex_public_rest E0 le mf
    (Out_return (Some (Vint Int.one,tint))) /\
  finv m0 bd dbase bw outedge cursor N bi mf true (mixed_ex_output x y z u v) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf bl 0 16 Cur Freeable /\ Mem.range_perm mf br 0 40 Cur Freeable /\
  lframe (mixed_ex_public_outside m0 bd bw bi bp ba bl br) m mf.
Proof.
  intros HD HO HN HX HY HZ HU HV Hrc HM Sep FP FA FL FR Source HSep Fin.
  pose proof Sep as Sep0;repeat rewrite NoDup_cons_iff in Sep0;cbn [In] in Sep0.
  assert (SPL : bp<>bl) by intuition congruence.
  assert (SAL : ba<>bl) by intuition congruence.
  assert (SPA : bp<>ba) by intuition congruence.
  assert (SPR : bp<>br) by intuition congruence.
  assert (SAR : ba<>br) by intuition congruence.
  assert (SLR : bl<>br) by intuition congruence.
  assert (NotR : ~extA m0 bd bw bi br) by (exact (HSep 3%nat ltac:(cbn;lia))).
  assert (NotP : ~extA m0 bd bw bi bp) by (exact (HSep 0%nat ltac:(cbn;lia))).
  assert (NotA : ~extA m0 bd bw bi ba) by (exact (HSep 1%nat ltac:(cbn;lia))).
  assert (NotL : ~extA m0 bd bw bi bl) by (exact (HSep 2%nat ltac:(cbn;lia))).
  destruct (eval_mixed_ex_clear_owned m br FR) as (mc & CC & FRC & FC).
  assert (FPC : Mem.range_perm mc bp 0 128 Cur Freeable) by (keep_ex_free FP FC).
  assert (FAC : Mem.range_perm mc ba 0 88 Cur Freeable) by (keep_ex_free FA FC).
  assert (FLC : Mem.range_perm mc bl 0 16 Cur Freeable) by (keep_ex_free FL FC).
  assert (SourceC : frame_fields_at mc bl 0 bi edge rc).
  { destruct Source as (SE & SC);split;rewrite (proj1 FC);try assumption;
      [eapply Mem.perm_valid_block;apply (FL 0);lia|intros;exact SLR|
       eapply Mem.perm_valid_block;apply (FL 0);lia|intros;exact SLR]. }
  assert (FinC : finv m0 bd dbase bw outedge cursor N bi mc false []).
  { eapply finv_stable;[exact HO|exact Fin|].
    eapply lframe_implies;[exact FC|];intros b pos HE HVB;intro EQ;subst b;apply NotR;exact HE. }
  assert (Sep3 : xsep (extA m0 bd bw bi) [(bp,0);(ba,0);(bl,0)]).
  { intros [|[|[|r]]] HI;[exact (HSep 0%nat ltac:(cbn;lia))|exact (HSep 1%nat ltac:(cbn;lia))|
      exact (HSep 2%nat ltac:(cbn;lia))|cbn in HI;lia]. }
  destruct (eval_mixed_public_reads m0 bd dbase bw outedge cursor N bi edge rc x y z u v mc bp ba bl
    HO ltac:(lia) HX HY HZ HU HV Hrc HM FPC FAC FLC SourceC SPL SAL SPA Sep3 FinC)
    as (mr & ms & CR & CA & X & Y & Z & U & V & FlagP & FlagA & FPS & FAS & FLS & FinS & FS).
  assert (FRS : Mem.range_perm ms br 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FRC|exact FS|];intros;unfold rescale_locals_outside;repeat split;congruence. }
  assert (SepH : NoDup [bp;ba;br]) by (repeat constructor;cbn [In];intuition congruence).
  destruct (eval_mixed_ratio_function (square_reader_rho x) (square_reader_rho y)
    (square_reader_rho z) (square_reader_rho u) (square_reader_rho v)
    (bit_int (Bit.toBool (@canonical_fe_is_zero Simplicity.Alg.CoreFunSem z))) ms bp ba br SepH
    (square_reader_positioned x) (square_reader_positioned y) (square_reader_bounds z)
    (square_reader_bounds u) (square_reader_bounds v) FlagP FlagA X Y Z U V FPS FAS FRS)
    as (mn & CH & OX & OY & OZ & FlagN & FPN & FAN & BX & BY & BZ & RY & FRN & FH).
  assert (FLN : Mem.range_perm mn bl 0 16 Cur Freeable) by (keep_ex_free FLS FH).
  assert (FinN : finv m0 bd dbase bw outedge cursor N bi mn false []).
  { eapply finv_stable;[exact HO|exact FinS|].
    eapply lframe_implies;[exact FH|];intros b pos HE HVB;repeat split;intro EQ;subst b;
      [apply NotP|apply NotA|apply NotR];exact HE. }
  set (fl := bit_int (Bit.toBool (@canonical_fe_is_zero Simplicity.Alg.CoreFunSem z))).
  set (ratio := rescale_point_field (mixed_body_ratio_words fl (square_reader_rho x) (square_reader_rho y)
    (square_reader_rho z) (square_reader_rho u) (square_reader_rho v))).
  set (outs := Simplicity.Translate.encode (point_field_output ratio)).
  assert (Len : length outs=256%nat) by (unfold outs;rewrite Simplicity.Translate.encode_length;reflexivity).
  assert (InvR : invA m0 bd dbase bw outedge cursor N bi rc false [] 256 (point_field_rho ratio rc) [] mn).
  { change (Int64.repr rc=Int64.repr rc /\ finv m0 bd dbase bw outedge cursor N bi mn false [] /\
      0+256<=N /\ 0<=256);split;[reflexivity|];split;[exact FinN|];split;lia. }
  assert (SepR : xsep (extA m0 bd bw bi) [(br,0)]).
  { intros [|r] HI;[exact NotR|cbn in HI;lia]. }
  destruct (eval_owned_bounded_field_write 40 m0 bd dbase bw outedge cursor N bi rc ratio false [] PointX mn br
    ltac:(cbn;lia) HO (rescale_point_bounds _ (mixed_ratio_words_bounds fl (square_reader_rho x) (square_reader_rho y)
      (square_reader_rho z) (square_reader_rho u) (square_reader_rho v) (square_reader_positioned x)
      (square_reader_bounds y) (square_reader_bounds z) (square_reader_bounds u))) RY FRN SepR InvR)
    as (mw & CW & FinW & FRW & FWR).
  change (finv m0 bd dbase bw outedge cursor N bi mw true outs) in FinW.
  pose proof (owned_write_outside_owner 40 mn mw m0 bd bw bi br PointX FWR) as FW.
  assert (XW : fe_at mw bp 0 (words5 (mixed_body_x_words fl (square_reader_rho x) (square_reader_rho y) (square_reader_rho z) (square_reader_rho u) (square_reader_rho v))))
    by (eapply field_at_lframe;[exact OX|exact FW|];intros;split;assumption).
  assert (YW : fe_at mw bp 40 (words5 (mixed_body_y_words fl (square_reader_rho x) (square_reader_rho y) (square_reader_rho z) (square_reader_rho u) (square_reader_rho v))))
    by (eapply field_at_lframe;[exact OY|exact FW|];intros;split;assumption).
  assert (ZW : fe_at mw bp 80 (words5 (mixed_body_z_words fl (square_reader_rho x) (square_reader_rho y) (square_reader_rho z) (square_reader_rho u) (square_reader_rho v))))
    by (eapply field_at_lframe;[exact OZ|exact FW|];intros;split;assumption).
  assert (FPW : Mem.range_perm mw bp 0 128 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FPN|exact FW|];intros;split;assumption. }
  assert (FAW : Mem.range_perm mw ba 0 88 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FAN|exact FW|];intros;split;assumption. }
  assert (FLW : Mem.range_perm mw bl 0 16 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FLN|exact FW|];intros;split;assumption. }
  assert (SepP : xsep (extA m0 bd bw bi) [(bp,0)]).
  { intros [|r] HI;[exact NotP|cbn in HI;lia]. }
  destruct (eval_write_gej_general_prefix m0 bd dbase bw outedge cursor N bi rc true outs mw bp
    (rescale_point_field (mixed_body_x_words fl (square_reader_rho x) (square_reader_rho y) (square_reader_rho z) (square_reader_rho u) (square_reader_rho v)))
    (rescale_point_field (mixed_body_y_words fl (square_reader_rho x) (square_reader_rho y) (square_reader_rho z) (square_reader_rho u) (square_reader_rho v)))
    (rescale_point_field (mixed_body_z_words fl (square_reader_rho x) (square_reader_rho y) (square_reader_rho z) (square_reader_rho u) (square_reader_rho v)))
    HO ltac:(rewrite Len;lia) FinW (rescale_point_bounds _ BX) (rescale_point_bounds _ BY) (rescale_point_bounds _ BZ)
    XW YW ZW FPW SepP) as (mf & CP & FinF & FPF & FPFrame).
  assert (FAF : Mem.range_perm mf ba 0 88 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FAW|exact FPFrame|];intros;split;congruence. }
  assert (FLF : Mem.range_perm mf bl 0 16 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FLW|exact FPFrame|];intros;split;congruence. }
  assert (FRF : Mem.range_perm mf br 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FRW|exact FPFrame|];intros;split;congruence. }
  exists mf;split.
  - eapply exec_mixed_ex_rest_from_calls;eassumption.
  - split.
    + unfold mixed_ex_output,outs,ratio,fl in *.
      rewrite !rescale_point_output in FinF;exact FinF.
    + split;[exact FPF|];split;[exact FAF|];split;[exact FLF|];split;[exact FRF|].
      eapply lframe_trans.
      * eapply lframe_implies;[exact FC|];intros b pos (NP & NA & NL & NR & NE) HVB;exact NR.
      * eapply lframe_trans.
        -- eapply lframe_implies;[exact FS|];intros b pos (NP & NA & NL & NR & NE) HVB;
             unfold rescale_locals_outside;repeat split;assumption.
        -- eapply lframe_trans.
           ++ eapply lframe_implies;[exact FH|];intros b pos (NP & NA & NL & NR & NE) HVB;repeat split;assumption.
           ++ eapply lframe_trans;
                [eapply lframe_implies;[exact FW|]|eapply lframe_implies;[exact FPFrame|]];
                intros b pos (NP & NA & NL & NR & NE) HVB;split;assumption.
Qed.
