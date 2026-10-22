(** Original projective-equivalence call, using the verified negation and
    generic addition calls and their actual stored infinity flag. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_square_columns C.jet_secp_square_spec_bridge
 C.jet_secp_multiply_input_input
 C.jet_secp_field_negate_separate C.jet_secp_field_weak_loose C.jet_secp_curve_frame
 C.jet_secp_field_read_preservation C.jet_secp_gej_negate_separate
 C.jet_secp_gej_ge_equiv_function C.jet_secp_gej_ge_equiv_dispatch C.jet_secp_gej_ge_equiv_flag
 C.jet_secp_gej_flag_read C.jet_secp_gej_add_generic_function C.jet_secp_gej_equiv_statements
 C.jet_secp_gej_equiv_literal C.jet_secp_gej_negate_literal C.jet_secp_negate_literal_contract
 C.jet_secp_canonical_normalize C.jet_secp_canonical_zero C.jet_secp_rescale_literal
 C.jet_secp_add_literal C.jet_secp_literal_gej_predicate C.jet_secp_double_coordinate_numeric.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge normalized_value canonical_fe_normalize canonical_fe_is_zero
 literal_fe_negate literal_gej_add literal_gej_equiv literal_gej_is_infinity square_reader_rho.

Definition gej_equiv_entry_temps bp ba := PTree.set _b (Vptr ba Ptrofs.zero)
 (PTree.set _a (Vptr bp Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_gej_eq_var))).

Lemma gej_equiv_entry m mi bp ba bt : Mem.alloc m 0 128=(mi,bt) ->
 function_entry2 secp_ge f_secp256k1_gej_eq_var [Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero] m
  (gej_equiv_env bt) (gej_equiv_entry_temps bp ba) mi.
Proof.
 intro Alloc;assert (Ok : fn_okb f_secp256k1_gej_eq_var=true) by reflexivity.
 destruct (fn_okb_true _ Ok) as (HN1 & HN2 & HD);constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
 eapply alloc_variables_cons with (m1:=mi) (b1:=bt);[exact Alloc|constructor].
Qed.
Lemma gej_equiv_blocks bt : blocks_of_env secp_ge (gej_equiv_env bt)=[(bt,0,128)].
Proof. reflexivity. Qed.

Theorem eval_gej_equiv_reader (x y z u v w : Ty.tySem (Word 8)) m bp ba :
 bp<>ba ->
 fe_at m bp 0 (words5 (square_reader_rho x)) ->
 fe_at m bp 40 (words5 (square_reader_rho y)) ->
 fe_at m bp 80 (words5 (square_reader_rho z)) ->
 fe_at m ba 0 (words5 (square_reader_rho u)) ->
 fe_at m ba 40 (words5 (square_reader_rho v)) ->
 fe_at m ba 80 (words5 (square_reader_rho w)) ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)))) ->
 Mem.load Mint32 m ba 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem w)))) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_eq_var)
  [Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf
  (Vint (bit_int (Bit.toBool (@literal_gej_equiv Alg.CoreFunSem (((x,y),z),((u,v),w)))))) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 lframe (fun b _=>b<>bp /\ b<>ba) m mf.
Proof.
 intros Sep X Y Z U V W FlagA FlagB PF AF.
 assert (VP : Mem.valid_block m bp) by (eapply Mem.perm_valid_block;apply (PF 0);lia).
 assert (VA : Mem.valid_block m ba) by (eapply Mem.perm_valid_block;apply (AF 0);lia).
 destruct (Mem.alloc m 0 128) as [mi bt] eqn:Alloc.
 pose proof (Mem.fresh_block_alloc _ _ _ _ _ Alloc) as Fresh.
 assert (TP : bt<>bp) by (intro HE;subst bt;contradiction).
 assert (TA : bt<>ba) by (intro HE;subst bt;contradiction).
 assert (FA : lframe (fun _ _=>True) m mi)
  by (apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc).
 pose proof (field_at_lframe m mi bp 0 _ _ X FA ltac:(intros;exact Logic.I)) as XI.
 pose proof (field_at_lframe m mi bp 40 _ _ Y FA ltac:(intros;exact Logic.I)) as YI.
 pose proof (field_at_lframe m mi bp 80 _ _ Z FA ltac:(intros;exact Logic.I)) as ZI.
 pose proof (field_at_lframe m mi ba 0 _ _ U FA ltac:(intros;exact Logic.I)) as UI.
 pose proof (field_at_lframe m mi ba 40 _ _ V FA ltac:(intros;exact Logic.I)) as VI.
 pose proof (field_at_lframe m mi ba 80 _ _ W FA ltac:(intros;exact Logic.I)) as WI.
 pose proof (curve_keep_free _ m mi bp 128 ltac:(lia) PF FA ltac:(intros;exact Logic.I)) as PFI.
 pose proof (curve_keep_free _ m mi ba 128 ltac:(lia) AF FA ltac:(intros;exact Logic.I)) as AFI.
 assert (TFI : Mem.range_perm mi bt 0 128 Cur Freeable)
  by (intros pos HP;eapply Mem.perm_alloc_2;eassumption).
 assert (FlagAI : Mem.load Mint32 mi bp 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)))))
  by (rewrite (proj1 FA Mint32 bp 120 VP ltac:(intros;exact Logic.I));exact FlagA).
 assert (FlagBI : Mem.load Mint32 mi ba 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem w)))))
  by (rewrite (proj1 FA Mint32 ba 120 VA ltac:(intros;exact Logic.I));exact FlagB).
 destruct (eval_gej_negate_separate mi bp bt (square_reader_rho x) (normalized_value y)
   (square_reader_rho z) (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)))
   ltac:(congruence) (normalized_value_range y) XI YI ZI FlagAI TFI)
  as (mn & Neg & XN & YN & ZN & FlagN & TFN & FN).
 rewrite negate_reader_words in YN.
 assert (UN : fe_at mn ba 0 (words5 (square_reader_rho u))).
 { eapply field_at_lframe;[exact UI|exact FN|];intros;congruence. }
 assert (VN : fe_at mn ba 40 (words5 (square_reader_rho v))).
 { eapply field_at_lframe;[exact VI|exact FN|];intros;congruence. }
 assert (WN : fe_at mn ba 80 (words5 (square_reader_rho w))).
 { eapply field_at_lframe;[exact WI|exact FN|];intros;congruence. }
 assert (PFN : Mem.range_perm mn bp 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact PFI|exact FN|];intros;congruence. }
 assert (AFN : Mem.range_perm mn ba 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact AFI|exact FN|];intros;congruence. }
 assert (FlagBN : Mem.load Mint32 mn ba 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem w))))).
 { rewrite (proj1 FN Mint32 ba 120);[exact FlagBI| |intros;congruence].
   eapply Mem.perm_valid_block;apply (AFI 0);lia. }
 assert (FlagNN : Mem.load Mint32 mn bt 120=Some (Vint (bit_int (Bit.toBool
    (@canonical_fe_is_zero Alg.CoreFunSem (@canonical_fe_normalize Alg.CoreFunSem z)))))).
 { rewrite equiv_normalized_zero_test;exact FlagN. }
 destruct (eval_gej_add_generic (@canonical_fe_normalize Alg.CoreFunSem x)
    (@literal_fe_negate Alg.CoreFunSem y) (@canonical_fe_normalize Alg.CoreFunSem z) u v w
    (square_reader_rho x) (negate_sep_words (square_reader_rho y)) (square_reader_rho z)
    (square_reader_rho u) (square_reader_rho v) (square_reader_rho w) mn bt ba
    TA (square_reader_bounds x) (gej_ge_equiv_negated_bounds (normalized_value y) (normalized_value_range y))
    (square_reader_bounds z) (square_reader_bounds u) (square_reader_bounds v) (square_reader_bounds w)
    (equiv_normalized_reader_residue x) (double_match_mod _ _ (equiv_negated_reader_residue y))
    (equiv_normalized_reader_residue z)
    ltac:(rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue)
    ltac:(rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue)
    ltac:(rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue)
    FlagNN FlagBN XN YN ZN UN VN WN TFN AFN)
  as (ma & ox & oy & oz & Add & XF & YF & ZF & FlagF & TFA & AFA & BXF & BYF & BZF & Literal & FM).
 assert (FlagLiteral : Mem.load Mint32 ma bt 120=Some (Vint (bit_int
   (Bit.toBool (@literal_gej_equiv Alg.CoreFunSem (((x,y),z),((u,v),w))))))).
 { rewrite literal_gej_equiv_step,literal_gej_negate_step;exact FlagF. }
 pose proof (eval_gej_flag_accessor ma bt 0 (bit_int
   (Bit.toBool (@literal_gej_equiv Alg.CoreFunSem (((x,y),z),((u,v),w)))))
   ltac:(lia) ltac:(change (128<=18446744073709551615);lia) FlagLiteral) as ReadFlag.
 assert (PFA : Mem.range_perm ma bp 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact PFN|exact FM|];intros;split;congruence. }
 destruct (free_list_exists [(bt,0,128)] ma) as (mf & Free & Unchanged).
 - cbn;repeat constructor;cbn;intuition congruence.
 - intros b lo hi [HE|HE];[inversion HE;subst;exact TFA|contradiction].
 - assert (FF : lframe (fun b _=>b<>bt) ma mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
     intros b pos NB VB;cbn;intuition congruence. }
   assert (PFF : Mem.range_perm mf bp 0 128 Cur Freeable).
   { eapply curve_keep_free;[lia|exact PFA|exact FF|];intros;congruence. }
   assert (AFF : Mem.range_perm mf ba 0 128 Cur Freeable).
   { eapply curve_keep_free;[lia|exact AFA|exact FF|];intros;congruence. }
   exists mf;split.
   + eapply eval_funcall_internal with (e:=gej_equiv_env bt) (le1:=gej_equiv_entry_temps bp ba)
      (le2:=PTree.set _t'1 (Vint (bit_int (Bit.toBool (@literal_gej_equiv Alg.CoreFunSem
       (((x,y),z),((u,v),w)))))) (gej_equiv_entry_temps bp ba))
      (m1:=mi) (m2:=ma) (out:=Out_return (Some (Vint (bit_int (Bit.toBool
        (@literal_gej_equiv Alg.CoreFunSem (((x,y),z),((u,v),w))))),tint))).
     * apply gej_equiv_entry;exact Alloc.
     * eapply exec_gej_equiv_body_from_calls;[| |exact Neg|exact Add|exact ReadFlag].
       -- unfold gej_equiv_entry_temps;rewrite PTree.gso by discriminate;apply PTree.gss.
       -- apply PTree.gss.
     * split;[discriminate|reflexivity].
     * rewrite gej_equiv_blocks;exact Free.
   + split;[exact PFF|];split;[exact AFF|].
     assert (Frame : lframe (fun b _=>Mem.valid_block m b /\ b<>bp /\ b<>ba) m mf).
     { eapply lframe_trans.
       - eapply lframe_implies;[exact FA|];intros;exact Logic.I.
       - eapply lframe_trans.
         + eapply lframe_implies;[exact FN|];intros b pos [VB [NP NA]] VCur HE;subst b;contradiction.
         + eapply lframe_trans.
           * eapply lframe_implies;[exact FM|];intros b pos [VB [NP NA]] VCur;
             split;[intro HE;subst b;contradiction|exact NA].
           * eapply lframe_implies;[exact FF|];intros b pos [VB [NP NA]] VCur HE;subst b;contradiction. }
     eapply lframe_implies;[exact Frame|];intros b pos NP VA0;split;assumption.
Qed.
