(** Actual incoming-infinity mixed-addition branch with an indexed ratio
    array output. The ratio clear and affine-to-projective call both execute. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_curve_statements C.jet_secp_double_statements C.jet_secp_double_flag
 C.jet_secp_mixed_head C.jet_secp_mixed_body C.jet_secp_double_var_ratio_slice
 C.jet_secp_fe_clear_memory C.jet_secp_gej_set_ge_owned C.jet_secp_point_set_bit
 C.jet_secp_multiply_normalize_bridge C.jet_secp_local_regions C.jet_secp_curve_frame
 C.jet_secp_field_read_preservation.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Local Ltac original_pure := unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
Local Ltac keep_temp H := rewrite PTree.gso by discriminate;exact H.

Lemma exec_mixed_head_infinite_ratio_slice e le m mc mf ba br base size bb flag :
  0<=base -> base+40<=size -> size<=Ptrofs.max_unsigned ->
  le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
  le!_b=Some (Vptr bb Ptrofs.zero) -> le!_rzr=Some (Vptr br (Ptrofs.repr base)) ->
  e!_secp256k1_gej_set_ge=None -> e!_secp256k1_fe_clear=None ->
  Mem.load Mint32 m ba 120=Some (Vint flag) -> flag<>Int.zero ->
  Mem.range_perm m br 0 size Cur Freeable ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_clear) [Vptr br (Ptrofs.repr base)] E0 mc Vundef ->
  Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_gej_set_ge)
    [Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m mixed_head E0
    (PTree.set _t'4 (Vint flag) le) mf (Out_return None).
Proof.
  intros Base Fit Max HA HR HB HN HE HClr HF HFlag RF CC HC;unfold mixed_head.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'4 (Vint flag) le).
  - apply exec_Sset;eapply eval_Elvalue.
    + apply eval_double_flag_field;exact HA.
    + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
      change (Mem.load Mint32 m ba 120=Some (Vint flag));exact HF.
  - eapply exec_Sifthenelse with (v1:=Vint flag) (b:=true).
    + apply eval_Etempvar;apply PTree.gss.
    + change (Some (negb (Int.eq flag Int.zero))=Some true).
      rewrite Int.eq_false by exact HFlag;reflexivity.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'4 (Vint flag) le).
      * eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=m)
          (le1:=PTree.set _t'4 (Vint flag) le) (out1:=Out_normal).
        -- apply exec_Sskip.
        -- constructor.
        -- apply exec_Sbreak.
        -- constructor.
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=PTree.set _t'4 (Vint flag) le).
        -- eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
           ++ apply eval_double_var_nonnull_slice with (br:=br) (base:=base);
                [lia|keep_temp HN|apply Mem.valid_pointer_nonempty_perm;
                  eapply Mem.perm_implies;[apply (RF base);lia|constructor]].
           ++ reflexivity.
           ++ change (Clight2.exec_stmt secp_ge e (PTree.set _t'4 (Vint flag) le) m
                (curve_call _secp256k1_fe_clear f_secp256k1_fe_clear None [Etempvar _rzr (tptr curve_fe_type)])
                E0 (PTree.set _t'4 (Vint flag) le) mc Out_normal).
              eapply exec_curve_call with (vargs:=[Vptr br (Ptrofs.repr base)]) (v:=Vundef).
              ** original_pure.
              ** exact HClr.
              ** eapply eval_Econs;[apply eval_Etempvar;keep_temp HN|reflexivity|constructor].
              ** exact CC.
        -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set _t'4 (Vint flag) le).
           ++ change (Clight2.exec_stmt secp_ge e (PTree.set _t'4 (Vint flag) le) mc
                (curve_call _secp256k1_gej_set_ge f_secp256k1_gej_set_ge None
                  [Etempvar _r (tptr (Tstruct __6123 noattr));Etempvar _b (tptr (Tstruct __6121 noattr))])
                E0 (PTree.set _t'4 (Vint flag) le) mf Out_normal).
              eapply exec_curve_call with (vargs:=[Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero]) (v:=Vundef).
              ** original_pure.
              ** exact HE.
              ** eapply eval_Econs;[apply eval_Etempvar;keep_temp HR|reflexivity|].
                 eapply eval_Econs;[apply eval_Etempvar;keep_temp HB|reflexivity|constructor].
              ** exact HC.
           ++ apply exec_Sreturn_none.
Qed.

Definition mixed_infinite_slice_frame (ba br:block) base (b:block) pos :=
 b<>ba /\ (b<>br \/ pos<base \/ base+40<=pos).

Theorem exec_mixed_infinite_ratio_slice e le m ba bb br base size x y flag :
 0<=base -> (8|base) -> base+40<=size -> size<=Ptrofs.max_unsigned ->
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
 le!_b=Some (Vptr bb Ptrofs.zero) -> le!_rzr=Some (Vptr br (Ptrofs.repr base)) ->
 e!_secp256k1_gej_set_ge=None -> e!_secp256k1_fe_clear=None ->
 ba<>bb -> ba<>br -> bb<>br ->
 Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bb 0 88 Cur Freeable ->
 Mem.range_perm m br 0 size Cur Freeable ->
 Mem.load Mint32 m ba 120=Some (Vint flag) -> flag<>Int.zero ->
 fe_at m bb 0 (words5 x) -> fe_at m bb 40 (words5 y) -> Mem.load Mint32 m bb 80=Some (Vint Int.zero) -> exists mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_ge_var) E0
  (PTree.set _t'4 (Vint flag) le) mf (Out_return None) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\
 fe_at mf ba 80 (words5 (point_set_bit_words true)) /\ Mem.load Mint32 mf ba 120=Some (Vint Int.zero) /\
 fe_at mf bb 0 (words5 x) /\ fe_at mf bb 40 (words5 y) /\ Mem.load Mint32 mf bb 80=Some (Vint Int.zero) /\
 fe_at mf br base (words5 (point_set_bit_words false)) /\
 Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bb 0 88 Cur Freeable /\
 Mem.range_perm mf br 0 size Cur Freeable /\ lframe (mixed_infinite_slice_frame ba br base) m mf.
Proof.
 intros Base Align Fit Max A R B Ratio SetGE ClearGlobal AB AR BR FreeA FreeB FreeR Flag Nonzero X Y FlagB.
 destruct (eval_fe_clear_owned m br base Base Align ltac:(lia)
   ltac:(intros pos Range;apply (freeable_range_writable _ _ _ _ FreeR);lia))
  as (mc & Clear & RatioC & Loads & Perms & Valid).
 assert (FC:lframe (fun b pos=>b<>br \/ pos<base \/ base+40<=pos) m mc).
 { split.
   - intros ch b ofs Old Outside;apply Loads;destruct (Pos.eq_dec b br) as [->|Different];[right|left;exact Different].
     destruct (Z_le_dec (ofs+size_chunk ch) base) as [Before|NotBefore];[left;exact Before|right].
     destruct (Z_le_dec (base+40) ofs) as [After|NotAfter];[exact After|].
     pose proof (size_chunk_pos ch) as Positive.
     destruct (Z_le_dec ofs base) as [Low|High];
      [specialize (Outside base ltac:(lia))|specialize (Outside ofs ltac:(lia))];
      destruct Outside as [Different|[Before|After]];[contradiction|lia|lia|contradiction|lia|lia].
   - split;[intros b pos k p Old Outside P;apply (proj2 (Perms b pos k p));exact P|exact Valid]. }
 assert (XC:fe_at mc bb 0 (words5 x)) by (eapply field_at_lframe;[exact X|exact FC|];intros;left;exact BR).
 assert (YC:fe_at mc bb 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact FC|];intros;left;exact BR).
 assert (FreeAC:Mem.range_perm mc ba 0 128 Cur Freeable).
 { intros pos Range;apply (proj2 (Perms ba pos Cur Freeable));apply FreeA;exact Range. }
 assert (FreeBC:Mem.range_perm mc bb 0 88 Cur Freeable).
 { intros pos Range;apply (proj2 (Perms bb pos Cur Freeable));apply FreeB;exact Range. }
 assert (FreeRC:Mem.range_perm mc br 0 size Cur Freeable).
 { intros pos Range;apply (proj2 (Perms br pos Cur Freeable));apply FreeR;exact Range. }
 assert (FlagBC:Mem.load Mint32 mc bb 80=Some (Vint Int.zero)).
 { rewrite (proj1 FC Mint32 bb 80);[exact FlagB| |intros;left;exact BR].
   eapply Mem.perm_valid_block;apply (FreeB 0);lia. }
 destruct (eval_gej_set_ge_owned mc ba bb x y Int.zero AB FreeAC XC YC FlagBC)
  as (mf & SetCall & XO & YO & ZO & FlagO & FreeAO & Frame).
 assert (XF:fe_at mf bb 0 (words5 x)) by (eapply field_at_lframe;[exact XC|exact Frame|];intros;congruence).
 assert (YF:fe_at mf bb 40 (words5 y)) by (eapply field_at_lframe;[exact YC|exact Frame|];intros;congruence).
 assert (FlagBF:Mem.load Mint32 mf bb 80=Some (Vint Int.zero)).
 { rewrite (proj1 Frame Mint32 bb 80);[exact FlagBC| |intros;congruence].
   eapply Mem.perm_valid_block;apply (FreeBC 0);lia. }
 assert (RatioF:fe_at mf br base (words5 (point_set_bit_words false))) by
  (eapply field_at_lframe;[exact RatioC|exact Frame|];intros;congruence).
 assert (FreeBO:Mem.range_perm mf bb 0 88 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact FreeBC|exact Frame|];intros;congruence).
 assert (FreeRO:Mem.range_perm mf br 0 size Cur Freeable) by
  (eapply curve_keep_free;[clear -Base Fit;lia|exact FreeRC|exact Frame|];intros;congruence).
 exists mf;split.
 - rewrite mixed_body_source;eapply exec_Sseq_2;[|discriminate].
   eapply exec_mixed_head_infinite_ratio_slice with (mc:=mc) (br:=br) (base:=base) (size:=size);eassumption.
 - split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FlagO|];split;[exact XF|];split;[exact YF|];
    split;[exact FlagBF|];split;[exact RatioF|];split;[exact FreeAO|];split;[exact FreeBO|];split;[exact FreeRO|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact FC|];intros b pos [NotA Outside] Old;exact Outside.
   + eapply lframe_implies;[exact Frame|];intros b pos [NotA Outside] Old;exact NotA.
Qed.
