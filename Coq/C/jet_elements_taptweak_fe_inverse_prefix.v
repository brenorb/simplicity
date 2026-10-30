(** Prepare the real field-inverse caller for linked metadata. The pure
    prefix is derived first at the source GE, with the target metadata only
    as a logical memory region, then transported with its actual local domain. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_sx_exec.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_fe_inv_statements C.jet_secp_curve_statements C.jet_secp_curve_frame.
Require Import C.jet_secp_field_copy_owned C.jet_secp_signed62_storage C.jet_secp_signed62_repack C.jet_secp_signed62_numeric.
Require Import C.jet_secp_modinfo_fe_global C.jet_secp_modinv_var_entry C.jet_secp_point_mul_storage.
Require Import C.jet_secp_local_regions C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_square_columns C.jet_secp_b32_exec C.jet_secp_statement_prefix.
Require Import C.jet_clight_internal_frame C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.


Require Import C.jet_secp_fe_inv_prefix C.jet_elements_taptweak_pure C.jet_elements_taptweak_modinfo
 C.jet_elements_taptweak_inverse_entry C.jet_elements_taptweak_curve_transport
 C.jet_elements_taptweak_internal C.jet_clight_internal_preserve C.jet_transport C.jet_transport_entry C.jet_transport_locals.
Lemma elements_taptweak_fe_inv_vars_checked:
 vars_okb secp_ge elements_taptweak_ge(fn_vars f_secp256k1_fe_inv_var)=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_fe_inv_prefix_checked:
 locals_stmt_okb secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (map fst(fn_vars f_secp256k1_fe_inv_var))fe_inv_prefix=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_fe_inv_prefix_closed:
 closed_stmtb elements_taptweak_curve_helpers fe_inv_prefix=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_modinfo_fe_block elements_taptweak_curve_helpers.
Theorem exec_fe_inv_prefix_for_linked_metadata le w m bx sbase bt bs :
  le!_x=Some(Vptr bx (Ptrofs.repr sbase)) ->
  square_input_bounds w -> fe_at m bx sbase (words5 w) ->
  Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable ->
  bt<>bx -> bs<>bx -> bt<>bs -> bt<>elements_taptweak_modinfo_fe_block -> bs<>elements_taptweak_modinfo_fe_block ->
  elements_taptweak_modinfo_fe_global_rep m -> exists mf,
  Clight2.exec_stmt secp_ge (fe_inv_env bt bs) le m fe_inv_prefix E0 le mf Out_normal /\
  rep (fe_inv_packed_words w) [(bs,0);(elements_taptweak_modinfo_fe_block,0)] inv_start_regs mf /\
  fe_at mf bs 0 (words5 (fe_inv_packed_words w)) /\
  fe_at mf bt 0 (words5 (fe_inv_canonical_words w)) /\ fe_at mf bx sbase (words5 w) /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  signed62_normalized (fe_inv_packed_words w) /\
  signed62_unsigned_value (fe_inv_packed_words w)=fe_inv_value w /\
  elements_taptweak_modinfo_fe_global_rep mf /\ lframe (fun b _=>b<>bt /\ b<>bs) m mf.
Proof.
  intros TX Bounds Field FT FS TB SB TS TG SG Global.
  destruct (exec_field_copy_owned (fe_inv_env bt bs) le m
    (Ederef (Etempvar _x (tptr curve_fe_type)) curve_fe_type) (Evar _tmp curve_fe_type)
    bx sbase bt 0 w eq_refl eq_refl
    ltac:(eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact TX|apply deref_loc_copy;reflexivity])
    ltac:(apply eval_Evar_local;reflexivity) ltac:(congruence) Field ltac:(lia)
    ltac:(exists 0;reflexivity) ltac:(change (40<=18446744073709551615);lia) FT)
    as (mc & Copy & Tmp & Perm & LC).
  assert (FTC : Mem.range_perm mc bt 0 40 Cur Freeable).
  { intros pos HP;apply (proj2 (Perm bt pos Cur Freeable));apply FT;exact HP. }
  assert (FSC : Mem.range_perm mc bs 0 40 Cur Freeable).
  { intros pos HP;apply (proj2 (Perm bs pos Cur Freeable));apply FS;exact HP. }
  destruct (eval_fe_inv_normalize w mc bt Bounds Tmp FTC)
    as (mn & Normalize & Canonical & FTN & Keep & LN).
  assert (FSN : Mem.range_perm mn bs 0 40 Cur Freeable).
  { intros pos HP;apply Keep,FSC;exact HP. }
  destruct (eval_fe_to_signed62_value (fe_inv_canonical_words w) mn bs bt
    (proj1 (fe_inv_canonical_numeric w)) ltac:(congruence) FSN Canonical FTN)
    as (mf & Pack & Packed & FinalTmp & FSF & FTF & Normalized & Numeric & LP).
  change (signed62_unsigned_value (fe_inv_packed_words w)=radix_value (fe_inv_canonical_words w)) in Numeric.
  rewrite (proj2 (fe_inv_canonical_numeric w)) in Numeric.
  assert (Frame : lframe (fun b _=>b<>bt /\ b<>bs) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact LC|];intros b pos [NotT NotS] Valid;left;exact NotT.
    - eapply lframe_trans.
      + eapply lframe_implies;[exact LN|];intros b pos [NotT NotS] Valid [Eq Range];congruence.
      + eapply lframe_implies;[exact LP|];intros b pos [NotT NotS] Valid;split;assumption. }
  assert (Source : fe_at mf bx sbase (words5 w)).
  { eapply curve_keep_field_range;[reflexivity|exact Field|exact Frame|];intros;split;congruence. }
  assert (GlobalF : elements_taptweak_modinfo_fe_global_rep mf).
  { eapply elements_taptweak_modinfo_fe_global_lframe;[exact Global|exact Frame|];intros;split;congruence. }
  assert (Core : rep (fe_inv_packed_words w) [(bs,0);(elements_taptweak_modinfo_fe_block,0)] inv_start_regs mf).
  { apply elements_taptweak_inv_start_rep_from_storage;[exact SG|exact Packed|exact FSF|exact GlobalF]. }
  assert (Body : Clight2.exec_stmt secp_ge (fe_inv_env bt bs) le m fe_inv_prefix E0 le mf Out_normal).
  { unfold fe_inv_prefix;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=le);[exact Copy|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn) (le1:=le).
    - eapply exec_curve_call with (vargs:=[Vptr bt Ptrofs.zero]) (v:=Vundef).
      + unfold secp_pure;repeat (first [left;reflexivity|right]).
      + reflexivity.
      + eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|apply eval_Enil].
      + exact Normalize.
    - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
      + eapply exec_curve_call with (vargs:=[Vptr bs Ptrofs.zero;Vptr bt Ptrofs.zero]) (v:=Vundef).
        * unfold secp_pure;repeat (first [left;reflexivity|right]).
        * reflexivity.
        * eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
          eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|apply eval_Enil].
        * exact Pack.
      + apply exec_Sskip. }
  exists mf;repeat first [assumption|split].
Qed.

Theorem elements_taptweak_fe_inv_entry_to_core w m bx sbase bd dbase :
  square_input_bounds w -> fe_at m bx sbase (words5 w) -> elements_taptweak_modinfo_fe_global_rep m ->
  exists bt bs mi mf,
  function_entry2 elements_taptweak_ge f_secp256k1_fe_inv_var
    [Vptr bd (Ptrofs.repr dbase);Vptr bx (Ptrofs.repr sbase)] m
    (fe_inv_env bt bs) (fe_inv_slice_temps bd dbase bx sbase) mi /\
  Clight2.exec_stmt elements_taptweak_ge (fe_inv_env bt bs) (fe_inv_slice_temps bd dbase bx sbase) mi
    fe_inv_prefix E0 (fe_inv_slice_temps bd dbase bx sbase) mf Out_normal /\
  rep (fe_inv_packed_words w) [(bs,0);(elements_taptweak_modinfo_fe_block,0)] inv_start_regs mf /\
  fe_at mf bs 0 (words5 (fe_inv_packed_words w)) /\
  fe_at mf bt 0 (words5 (fe_inv_canonical_words w)) /\ fe_at mf bx sbase (words5 w) /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  signed62_normalized (fe_inv_packed_words w) /\
  signed62_unsigned_value (fe_inv_packed_words w)=fe_inv_value w /\
  elements_taptweak_modinfo_fe_global_rep mf /\ bt<>bs /\
  ~Mem.valid_block m bt /\ ~Mem.valid_block m bs /\ lframe (fun _ _=>True) m mf /\ readonly_preserved m mf.
Proof.
  intros Bounds Field Global.
  destruct (Mem.alloc m 0 40) as [mt bt] eqn:AT.
  destruct (Mem.alloc mt 0 40) as [mi bs] eqn:AS.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ AT) as FreshT.
  assert (FreshS : ~Mem.valid_block m bs).
  { intro Old;apply (Mem.fresh_block_alloc _ _ _ _ _ AS);eapply Mem.valid_block_alloc;eassumption. }
  assert (ValidX : Mem.valid_block m bx).
  { pose proof Field as (Nonneg & Align & Max & Perm & Loads).
    eapply Mem.perm_valid_block;apply (Perm sbase);lia. }
  assert (TG : bt<>elements_taptweak_modinfo_fe_block) by (intro Eq;apply FreshT;rewrite Eq;exact (proj1 Global)).
  assert (SG : bs<>elements_taptweak_modinfo_fe_block) by (intro Eq;apply FreshS;rewrite Eq;exact (proj1 Global)).
  assert (TB : bt<>bx) by (intro Eq;apply FreshT;rewrite Eq;exact ValidX).
  assert (SB : bs<>bx) by (intro Eq;apply FreshS;rewrite Eq;exact ValidX).
  assert (TS : bt<>bs).
  { intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ AS);rewrite <-Eq;eapply Mem.valid_new_block;exact AT. }
  assert (AllocFrame : lframe (fun _ _=>True) m mi).
  { eapply lframe_trans;apply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption. }
  assert (FieldI : fe_at mi bx sbase (words5 w)).
  { eapply curve_keep_field_range;[reflexivity|exact Field|exact AllocFrame|];intros;exact I. }
  assert (GlobalI : elements_taptweak_modinfo_fe_global_rep mi).
  { eapply elements_taptweak_modinfo_fe_global_lframe;[exact Global|exact AllocFrame|];intros;exact I. }
  assert (FT : Mem.range_perm mi bt 0 40 Cur Freeable).
  { intros pos HP;eapply Mem.perm_alloc_1;[exact AS|];eapply Mem.perm_alloc_2;eassumption. }
  assert (FS : Mem.range_perm mi bs 0 40 Cur Freeable).
  { intros pos HP;eapply Mem.perm_alloc_2;eassumption. }
  destruct (exec_fe_inv_prefix_for_linked_metadata (fe_inv_slice_temps bd dbase bx sbase) w mi bx sbase bt bs
    eq_refl Bounds FieldI FT FS TB SB TS TG SG GlobalI)
    as (mf & Body & Core & Packed & Canonical & Source & FTF & FSF & Normalized & Numeric & GlobalF & BodyFrame).
  assert (OldFrame : lframe (fun b _=>Mem.valid_block m b) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact AllocFrame|];intros;exact I.
    - eapply lframe_implies;[exact BodyFrame|];intros b pos Old Valid;split;intro Eq;
      [apply FreshT|apply FreshS];rewrite <-Eq;exact Old. }
  assert (Frame : lframe (fun _ _=>True) m mf).
  { eapply lframe_implies;[exact OldFrame|];intros b pos _ Valid;exact Valid. }
  pose proof(fe_inv_slice_entry m mt mi bt bs bd dbase bx sbase AT AS)as Entry.
  assert(EntryT:function_entry2 elements_taptweak_ge f_secp256k1_fe_inv_var
   [Vptr bd(Ptrofs.repr dbase);Vptr bx(Ptrofs.repr sbase)]m(fe_inv_env bt bs)
   (fe_inv_slice_temps bd dbase bx sbase)mi).
  { eapply function_entry2_transport;[exact elements_taptweak_fe_inv_vars_checked|exact Entry]. }
  assert(BodyT:Clight2.exec_stmt elements_taptweak_ge(fe_inv_env bt bs)(fe_inv_slice_temps bd dbase bx sbase)
   mi fe_inv_prefix E0(fe_inv_slice_temps bd dbase bx sbase)mf Out_normal).
  { eapply(proj1(locals_transport_main secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
    (locals_transportable_of_entries secp_ge elements_taptweak_ge elements_taptweak_curve_helpers
     elements_taptweak_curve_entries elements_taptweak_curve_ok)));
    [exact Body|eapply function_entry2_domain;exact Entry|eapply function_entry2_bound;exact Entry|
     exact elements_taptweak_fe_inv_prefix_checked]. }
  assert(Readonly:readonly_preserved m mf).
  { eapply preserved_trans;[eapply entry_preserved;exact EntryT|].
    eapply(proj1(internal_exec_preserved _ _ elements_taptweak_internal_table));
    [exact BodyT|eapply entry_plain;[exact EntryT|reflexivity]|exact elements_taptweak_fe_inv_prefix_closed]. }
  exists bt,bs,mi,mf;split;[exact EntryT|];split;[exact BodyT|].
  repeat first[assumption|split].
Qed.
