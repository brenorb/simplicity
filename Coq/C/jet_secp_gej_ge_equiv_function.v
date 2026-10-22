(** Complete original gej_eq_ge_var execution from owned input points.
    This returns its actual C flag; the literal specification bridge is separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_linkage C.jets_secp
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_b32_exec C.jet_secp_field_mul_small C.jet_secp_field_negate_separate C.jet_secp_field_weak_loose
 C.jet_secp_point_field_bridge C.jet_secp_mixed_finite_prefix C.jet_secp_gej_negate_separate
 C.jet_secp_mixed_function_loose C.jet_secp_mixed_body_loose C.jet_secp_curve_frame
 C.jet_secp_field_read_preservation C.jet_secp_gej_flag_read C.jet_secp_gej_ge_equiv_statements.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge mixed_loose_body_flag.

Definition gej_ge_equiv_result x value z u v flag :=
 mixed_loose_body_flag flag x (negate_sep_words (limb_rho value)) z u v.
Definition gej_ge_equiv_entry_temps bp ba := PTree.set _b (Vptr ba Ptrofs.zero)
 (PTree.set _a (Vptr bp Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_gej_eq_ge_var))).

Lemma gej_ge_equiv_entry m mi bp ba bt : Mem.alloc m 0 128=(mi,bt) ->
 function_entry2 secp_ge f_secp256k1_gej_eq_ge_var [Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero] m
  (gej_ge_equiv_env bt) (gej_ge_equiv_entry_temps bp ba) mi.
Proof.
 intro Alloc;assert (Ok : fn_okb f_secp256k1_gej_eq_ge_var=true) by reflexivity.
 destruct (fn_okb_true _ Ok) as (HN1 & HN2 & HD);constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
 eapply alloc_variables_cons with (m1:=mi) (b1:=bt);[exact Alloc|constructor].
Qed.
Lemma gej_ge_equiv_blocks bt : blocks_of_env secp_ge (gej_ge_equiv_env bt)=[(bt,0,128)].
Proof. reflexivity. Qed.
Lemma gej_ge_equiv_negated_bounds value : 0<=value<2^256 ->
 square_input_bounds (negate_sep_words (limb_rho value)).
Proof.
 intro Bound;assert (Small : mul_small_input_bounds (limb_rho value)).
 { apply mixed_positioned_tight;exact (proj1 (point_reader_limb_model value Bound)). }
 exact (proj2 (negate_sep_numeric (limb_rho value) Small)).
Qed.

Theorem eval_gej_ge_equiv_function x value z u v flag m bp ba :
 bp<>ba -> 0<=value<2^256 ->
 fe_limbs_ok (Int64.unsigned (x 0%nat)) (Int64.unsigned (x 1%nat))
  (Int64.unsigned (x 2%nat)) (Int64.unsigned (x 3%nat)) (Int64.unsigned (x 4%nat)) ->
 square_input_bounds z -> square_input_bounds u -> square_input_bounds v ->
 Mem.load Mint32 m bp 120=Some (Vint flag) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 (limb_rho value)) -> fe_at m bp 80 (words5 z) ->
 fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_eq_ge_var)
  [Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf (Vint (gej_ge_equiv_result x value z u v flag)) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 lframe (fun b _=>b<>bp /\ b<>ba) m mf.
Proof.
 intros Sep Bound BX BZ BU BV FlagA FlagB X Y Z U V PF AF.
 assert (VP : Mem.valid_block m bp) by (eapply Mem.perm_valid_block;apply (PF 0);lia).
 assert (VA : Mem.valid_block m ba) by (eapply Mem.perm_valid_block;apply (AF 0);lia).
 destruct (Mem.alloc m 0 128) as [mi bt] eqn:Alloc.
 pose proof (Mem.fresh_block_alloc _ _ _ _ _ Alloc) as Fresh.
 assert (TP : bt<>bp) by (intro HE;subst bt;contradiction).
 assert (TA : bt<>ba) by (intro HE;subst bt;contradiction).
 assert (FA : lframe (fun _ _=>True) m mi)
  by (apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc).
 pose proof (field_at_lframe m mi bp 0 _ _ X FA ltac:(intros;exact I)) as XI.
 pose proof (field_at_lframe m mi bp 40 _ _ Y FA ltac:(intros;exact I)) as YI.
 pose proof (field_at_lframe m mi bp 80 _ _ Z FA ltac:(intros;exact I)) as ZI.
 pose proof (field_at_lframe m mi ba 0 _ _ U FA ltac:(intros;exact I)) as UI.
 pose proof (field_at_lframe m mi ba 40 _ _ V FA ltac:(intros;exact I)) as VI.
 pose proof (curve_keep_free _ m mi bp 128 ltac:(lia) PF FA ltac:(intros;exact I)) as PFI.
 pose proof (curve_keep_free _ m mi ba 88 ltac:(lia) AF FA ltac:(intros;exact I)) as AFI.
 assert (TFI : Mem.range_perm mi bt 0 128 Cur Freeable)
  by (intros pos HP;eapply Mem.perm_alloc_2;eassumption).
 assert (FlagAI : Mem.load Mint32 mi bp 120=Some (Vint flag))
  by (rewrite (proj1 FA Mint32 bp 120 VP ltac:(intros;exact I));exact FlagA).
 assert (FlagBI : Mem.load Mint32 mi ba 80=Some (Vint Int.zero))
  by (rewrite (proj1 FA Mint32 ba 80 VA ltac:(intros;exact I));exact FlagB).
 destruct (eval_gej_negate_separate mi bp bt x value z flag ltac:(congruence) Bound XI YI ZI FlagAI TFI)
  as (mn & Neg & XN & YN & ZN & FlagN & TFN & FN).
 rewrite negate_reader_words in YN.
 assert (UN : fe_at mn ba 0 (words5 u)).
 { eapply field_at_lframe;[exact UI|exact FN|];intros;congruence. }
 assert (VN : fe_at mn ba 40 (words5 v)).
 { eapply field_at_lframe;[exact VI|exact FN|];intros;congruence. }
 assert (PFN : Mem.range_perm mn bp 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact PFI|exact FN|];intros;congruence. }
 assert (AFN : Mem.range_perm mn ba 0 88 Cur Freeable).
 { eapply curve_keep_free;[lia|exact AFI|exact FN|];intros;congruence. }
 assert (FlagBN : Mem.load Mint32 mn ba 80=Some (Vint Int.zero)).
 { rewrite (proj1 FN Mint32 ba 80);[exact FlagBI| |intros;congruence].
   eapply Mem.perm_valid_block;apply (AFI 0);lia. }
 destruct (eval_mixed_function_loose x (negate_sep_words (limb_rho value)) z u v flag mn bt ba
  TA BX (gej_ge_equiv_negated_bounds value Bound) BZ BU BV FlagN FlagBN XN YN ZN UN VN TFN AFN)
  as (ma & Add & XF & YF & ZF & FlagF & TFA & AFA & BXF & BYF & BZF & FM).
 change (Mem.load Mint32 ma bt 120=Some (Vint (gej_ge_equiv_result x value z u v flag))) in FlagF.
 pose proof (eval_gej_flag_accessor ma bt 0 (gej_ge_equiv_result x value z u v flag)
  ltac:(lia) ltac:(change (128<=18446744073709551615);lia) FlagF) as ReadFlag.
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
   assert (AFF : Mem.range_perm mf ba 0 88 Cur Freeable).
   { eapply curve_keep_free;[lia|exact AFA|exact FF|];intros;congruence. }
   exists mf;split.
   + eapply eval_funcall_internal with (e:=gej_ge_equiv_env bt) (le1:=gej_ge_equiv_entry_temps bp ba)
      (le2:=PTree.set _t'1 (Vint (gej_ge_equiv_result x value z u v flag)) (gej_ge_equiv_entry_temps bp ba))
      (m1:=mi) (m2:=ma) (out:=Out_return (Some (Vint (gej_ge_equiv_result x value z u v flag),tint))).
     * apply gej_ge_equiv_entry;exact Alloc.
     * eapply exec_gej_ge_equiv_body_from_calls;[| |exact Neg|exact Add|exact ReadFlag].
       -- unfold gej_ge_equiv_entry_temps;rewrite PTree.gso by discriminate;apply PTree.gss.
       -- apply PTree.gss.
     * split;[discriminate|reflexivity].
     * rewrite gej_ge_equiv_blocks;exact Free.
   + split;[exact PFF|];split;[exact AFF|].
     assert (Frame : lframe (fun b _=>Mem.valid_block m b /\ b<>bp /\ b<>ba) m mf).
     { eapply lframe_trans.
       - eapply lframe_implies;[exact FA|];intros;exact I.
       - eapply lframe_trans.
         + eapply lframe_implies;[exact FN|];intros b pos [VB [NP NA]] VCur HE;subst b;contradiction.
         + eapply lframe_trans.
           * eapply lframe_implies;[exact FM|];intros b pos [VB [NP NA]] VCur;
             split;[intro HE;subst b;contradiction|exact NA].
           * eapply lframe_implies;[exact FF|];intros b pos [VB [NP NA]] VCur HE;subst b;contradiction. }
     eapply lframe_implies;[exact Frame|];intros b pos NP VA0;split;assumption.
Qed.
