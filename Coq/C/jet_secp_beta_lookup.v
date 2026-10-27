(** Actual auxiliary-array construction followed by the original lambda
    lookup. The beta-array relation required by the lookup is derived from
    all eight original C multiplications, not supplied as a premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_beta_loop C.jet_secp_beta_loop_step C.jet_secp_beta_global C.jet_secp_beta_state
 C.jet_secp_generator_globalz_call C.jet_secp_globalz_loop C.jet_secp_globalz_pass2 C.jet_secp_globalz_word_walk
 C.jet_secp_table_get_lambda_literal C.jet_secp_lookup5_literal C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_field_mul_small C.jet_secp_field_negate_separate
 C.jet_secp_rescale_literal C.jet_secp_multiply_normalize_bridge C.jet_secp_curve_frame
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge beta_block literal_ge_scale_lambda rescale_field_output.

Definition beta_lookup_frame bt bx bd b (_:Z) := b<>bx /\ b<>bt /\ b<>beta_block /\ b<>bd.

Theorem exec_beta_array_then_lookup nib e le xs ys m bs bt bx bd :
 bs<>bt -> bs<>bx -> bs<>beta_block -> bt<>bx -> bt<>beta_block -> bx<>beta_block ->
 bd<>bs -> bd<>bt -> bd<>bx ->
 e!_secp256k1_fe_mul=None -> e!_secp256k1_const_beta=None ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_no=Some (Vlong Int64.one) ->
 Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) -> Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) ->
 globalz_table_rep m bt xs ys -> (forall k,(k<8)%nat -> square_input_bounds (xs k)) ->
 (forall k,(k<8)%nat -> mul_small_input_bounds (ys k)) ->
 Mem.range_perm m bs 0 24 Cur Freeable -> Mem.range_perm m bt 0 704 Cur Freeable ->
 Mem.range_perm m bx 0 320 Cur Freeable -> Mem.range_perm m bd 0 88 Cur Freeable -> beta_initialized m ->
 let j:=Z.to_nat (lookup5_index nib) in
 let outy:=if lookup5_negative nib then negate_sep_words (ys j) else ys j in exists lef m1 mf,
 Clight2.exec_stmt secp_ge e le m generator_auxiliary_statement E0 lef m1 Out_normal /\
 Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_ecmult_table_get_ge_lambda)
  [Vptr bd Ptrofs.zero;Vptr bt Ptrofs.zero;Vptr bx Ptrofs.zero;
   Vint (Int.repr (lookup5_digit nib));Vint (Int.repr 5)] E0 mf Vundef /\
 fe_at mf bd 0 (words5 (beta_aux_values xs j)) /\ fe_at mf bd 40 (words5 outy) /\
 (rescale_field_output (beta_aux_values xs j),rescale_field_output outy)=
  @literal_ge_scale_lambda Alg.CoreFunSem
   (@literal_lookup5 Alg.CoreFunSem (nib,globalz_word_vector (globalz_decoded_points xs ys))) /\
 square_input_bounds (beta_aux_values xs j) /\ square_input_bounds outy /\
 Mem.load Mint32 mf bd 80=Some (Vint Int.zero) /\
 globalz_table_rep mf bt xs ys /\ beta_aux_prefix mf bx xs 8 /\
 Mem.load Mptr mf bs 0=Some (Vptr bx Ptrofs.zero) /\ Mem.load Mptr mf bs 8=Some (Vptr bt Ptrofs.zero) /\
 Mem.range_perm mf bs 0 24 Cur Freeable /\ Mem.range_perm mf bt 0 704 Cur Freeable /\
 Mem.range_perm mf bx 0 320 Cur Freeable /\ Mem.range_perm mf bd 0 88 Cur Freeable /\
 beta_initialized mf /\ keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (beta_lookup_frame bt bx bd) m mf.
Proof.
 intros ST SX SB TX TB XB DS DT DX Global Const State No PX PT Table Bounds Tight FreeS FreeT FreeX FreeD Init;cbv zeta.
 destruct (exec_beta_auxiliary_one e le xs ys m bs bt bx ST SX SB TX TB XB Global Const State No PX PT
   Table Bounds FreeS FreeT FreeX Init)
  as (lef & m1 & Loop & NP1 & I1 & Other1 & Memory1 & Bounds1 & Match1).
 destruct Memory1 as (Table1 & Aux1 & PX1 & PT1 & FreeS1 & FreeT1 & FreeX1 & Init1 & Keep1 & RO1 & Frame1).
 assert (FreeD1:Mem.range_perm m1 bd 0 88 Cur Freeable) by (intros pos Pos;apply Keep1,FreeD;exact Pos).
 destruct (eval_table_get_lambda_lookup5 nib xs ys (beta_aux_values xs) m1 bd bt bx DT DX
   Table1 Aux1 Bounds1 Tight Match1 FreeT1 FreeX1 FreeD1)
  as (mf & Call & OutX & OutY & Literal & BX & BY & Flag & FreeDF & FreeTF & FreeXF & Keep2 & Frame2 & RO2).
 assert (TableF:globalz_table_rep mf bt xs ys).
 { intros k K;destruct (Table1 k K) as (X & Y & F);split.
   - eapply curve_keep_field_range;[reflexivity|exact X|exact Frame2|intros;congruence].
   - split.
     + eapply curve_keep_field_range;[reflexivity|exact Y|exact Frame2|intros;congruence].
     + assert (Valid:Mem.valid_block m1 bt) by (eapply Mem.perm_valid_block;apply (FreeT1 0);lia).
       rewrite (proj1 Frame2 Mint32 bt (88*Z.of_nat k+80) Valid);[exact F|intros;congruence]. }
 assert (AuxF:beta_aux_prefix mf bx xs 8).
 { intros k K;eapply curve_keep_field_range;[reflexivity|exact (Aux1 k K)|exact Frame2|intros;congruence]. }
 assert (ValidS:Mem.valid_block m1 bs) by (eapply Mem.perm_valid_block;apply (FreeS1 0);lia).
 exists lef,m1,mf;split;[exact Loop|];split;[exact Call|];split;[exact OutX|];split;[exact OutY|];
  split;[exact Literal|];split;[exact BX|];split;[exact BY|];split;[exact Flag|];
  split;[exact TableF|];split;[exact AuxF|];split.
 - rewrite (proj1 Frame2 Mptr bs 0 ValidS);[exact PX1|intros;congruence].
 - split.
   + rewrite (proj1 Frame2 Mptr bs 8 ValidS);[exact PT1|intros;congruence].
   + split;[intros pos Pos;apply Keep2,FreeS1;exact Pos|];split;[exact FreeTF|];split;[exact FreeXF|];
     split;[exact FreeDF|];split.
     * eapply beta_initialized_preserved;[exact Init1|exact RO2].
     * split;[eapply keeps_permissions_trans;[exact Keep1|exact Keep2]|];split.
       -- eapply preserved_trans;[exact RO1|exact RO2].
       -- eapply lframe_trans.
          ++ eapply lframe_implies;[exact Frame1|];intros b pos (NX & NT & NB & ND) Valid;
             unfold beta_aux_loop_frame;split;[exact NX|];split;assumption.
          ++ eapply lframe_implies;[exact Frame2|];intros b pos (NX & NT & NB & ND) Valid;exact ND.
Qed.
