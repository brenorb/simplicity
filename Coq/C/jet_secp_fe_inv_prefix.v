(** Original fe_inv_var preparation: copy an arbitrary represented field
    slice, canonically normalize its private copy, and pack signed62 input.
    The subsequent modular-inverse call is not assumed or executed here. *)
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
Local Opaque secp_ge modinfo_fe_block.

Definition fe_inv_normalize_table := [(_secp256k1_fe_normalize_var,f_secp256k1_fe_normalize_var)].
Lemma fe_inv_normalize_table_ok : internal_table_ok secp_ge fe_inv_normalize_table.
Proof.
  intros id fd Lookup;apply internal_lookup_in in Lookup.
  destruct Lookup as [Eq|Nil];[injection Eq as <- <-|contradiction].
  split;[apply secp_pure_ok;unfold secp_pure;repeat (first [left;reflexivity|right])|].
  split;reflexivity.
Qed.

Lemma inv_start_rep_from_storage w m bs : bs<>modinfo_fe_block ->
  fe_at m bs 0 (words5 w) -> Mem.range_perm m bs 0 40 Cur Freeable ->
  modinfo_fe_global_rep m -> rep w [(bs,0);(modinfo_fe_block,0)] inv_start_regs m.
Proof.
  intros Sep Field Free (Valid & Read & Loads).
  apply two_region_rep_separate;[reflexivity|exact Sep| |].
  - apply owned_field_slice_region;[reflexivity|lia|lia|exact Field|exact Free].
  - apply region_u64;cbn [bas blk lay nth fst snd].
    + lia.
    + exists 0;reflexivity.
    + change (48<=18446744073709551615);lia.
    + exact Valid.
    + exact Read.
    + intros i x At;rewrite nth_error_map in At.
      destruct (nth_error modinfo_fe_words i) as [v|] eqn:Word;[|discriminate].
      injection At as <-;split;[exact (Loads i v Word)|reflexivity].
Qed.
Lemma fe_inv_normalize_permissions m mf b :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_var) [Vptr b Ptrofs.zero] E0 mf Vundef ->
  keeps_permissions m mf.
Proof.
  intro Call;eapply (proj2 (internal_exec_keeps_permissions secp_ge fe_inv_normalize_table fe_inv_normalize_table_ok));
    [exact Call|].
  exists _secp256k1_fe_normalize_var,f_secp256k1_fe_normalize_var;split;reflexivity.
Qed.

Definition fe_inv_value w := radix_value w mod feP.
Definition fe_inv_canonical_words w := limb_rho (fe_inv_value w).
Definition fe_inv_packed_words w := fe_repack_words true (fe_inv_canonical_words w).
Lemma fe_inv_value_range w : 0<=fe_inv_value w<feP /\ 0<=fe_inv_value w<2^256.
Proof.
  unfold fe_inv_value;pose proof (Z.mod_pos_bound (radix_value w) feP ltac:(unfold feP,feR;lia)).
  split;[assumption|];unfold feP,feR in *;lia.
Qed.
Lemma fe_inv_canonical_storage w : words5 (fe_inv_canonical_words w)=map Int64.repr (fe_limbs_of (fe_inv_value w)).
Proof. reflexivity. Qed.
Lemma fe_inv_canonical_numeric w :
  fe_limbs_ok (Int64.unsigned (fe_inv_canonical_words w 0%nat))
    (Int64.unsigned (fe_inv_canonical_words w 1%nat)) (Int64.unsigned (fe_inv_canonical_words w 2%nat))
    (Int64.unsigned (fe_inv_canonical_words w 3%nat)) (Int64.unsigned (fe_inv_canonical_words w 4%nat)) /\
  radix_value (fe_inv_canonical_words w)=fe_inv_value w.
Proof.
  rewrite radix_value_matches_normalizer;unfold fe_inv_canonical_words.
  rewrite !limb_rho_unsigned by exact (proj2 (fe_inv_value_range w)).
  exact (fe_limbs_of_ok _ (proj2 (fe_inv_value_range w))).
Qed.

Theorem eval_fe_inv_normalize w m b : square_input_bounds w -> fe_at m b 0 (words5 w) ->
  Mem.range_perm m b 0 40 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_var) [Vptr b Ptrofs.zero] E0 mf Vundef /\
  fe_at mf b 0 (words5 (fe_inv_canonical_words w)) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
  keeps_permissions m mf /\ lframe (fun bx pos=>~(bx=b /\ 0<=pos<40)) m mf.
Proof.
  intros Bounds Field Free.
  assert (B : forall i,(i<5)%nat -> Int64.unsigned (w i)<=2^60).
  { intros i I;pose proof (Bounds i I);destruct (Nat.eqb i 4);lia. }
  destruct (eval_fe_normalize_var m b 0 (w 0%nat) (w 1%nat) (w 2%nat) (w 3%nat) (w 4%nat)
    Field (B 0%nat ltac:(lia)) (B 1%nat ltac:(lia)) (B 2%nat ltac:(lia)) (B 3%nat ltac:(lia)) (B 4%nat ltac:(lia)))
    as (mf & Call & Output & Frame).
  pose proof (fe_inv_normalize_permissions m mf b Call) as Keep.
  assert (Values : map Int64.repr (normalized_words w)=words5 (fe_inv_canonical_words w)).
  { rewrite bounded_normalized_words by exact B;rewrite fe_inv_canonical_storage;reflexivity. }
  change (fe_at mf b 0 (map Int64.repr (normalized_words w))) in Output;rewrite Values in Output.
  exists mf;split;[exact Call|];split;[exact Output|];split.
  - intros pos HP;apply Keep,Free;exact HP.
  - split;assumption.
Qed.

Definition fe_inv_prefix := Ssequence fe_inv_copy (Ssequence fe_inv_normalize (Ssequence fe_inv_pack Sskip)).
Lemma fe_inv_prefix_source : fn_body f_secp256k1_fe_inv_var =
  statement_sequence [fe_inv_copy;fe_inv_normalize;fe_inv_pack] (Ssequence fe_inv_inverse fe_inv_unpack).
Proof. reflexivity. Qed.
Definition fe_inv_slice_temps bd dbase bx sbase :=
  PTree.set _x (Vptr bx (Ptrofs.repr sbase))
    (PTree.set _r (Vptr bd (Ptrofs.repr dbase)) (create_undef_temps (fn_temps f_secp256k1_fe_inv_var))).
Lemma fe_inv_slice_entry m mt mi bt bs bd dbase bx sbase :
  Mem.alloc m 0 40=(mt,bt) -> Mem.alloc mt 0 40=(mi,bs) ->
  function_entry2 secp_ge f_secp256k1_fe_inv_var
    [Vptr bd (Ptrofs.repr dbase);Vptr bx (Ptrofs.repr sbase)] m
    (fe_inv_env bt bs) (fe_inv_slice_temps bd dbase bx sbase) mi.
Proof.
  intros AT AS;assert (Ok : fn_okb f_secp256k1_fe_inv_var=true) by reflexivity.
  destruct (fn_okb_true _ Ok) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
  eapply alloc_variables_cons with (m1:=mt) (b1:=bt);[exact AT|].
  eapply alloc_variables_cons with (m1:=mi) (b1:=bs);[exact AS|constructor].
Qed.

Theorem exec_fe_inv_prefix le w m bx sbase bt bs :
  le!_x=Some(Vptr bx (Ptrofs.repr sbase)) ->
  square_input_bounds w -> fe_at m bx sbase (words5 w) ->
  Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable ->
  bt<>bx -> bs<>bx -> bt<>bs -> bt<>modinfo_fe_block -> bs<>modinfo_fe_block ->
  modinfo_fe_global_rep m -> exists mf,
  Clight2.exec_stmt secp_ge (fe_inv_env bt bs) le m fe_inv_prefix E0 le mf Out_normal /\
  rep (fe_inv_packed_words w) [(bs,0);(modinfo_fe_block,0)] inv_start_regs mf /\
  fe_at mf bs 0 (words5 (fe_inv_packed_words w)) /\
  fe_at mf bt 0 (words5 (fe_inv_canonical_words w)) /\ fe_at mf bx sbase (words5 w) /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  signed62_normalized (fe_inv_packed_words w) /\
  signed62_unsigned_value (fe_inv_packed_words w)=fe_inv_value w /\
  modinfo_fe_global_rep mf /\ lframe (fun b _=>b<>bt /\ b<>bs) m mf.
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
  assert (GlobalF : modinfo_fe_global_rep mf).
  { eapply modinfo_fe_global_lframe;[exact Global|exact Frame|];intros;split;congruence. }
  assert (Core : rep (fe_inv_packed_words w) [(bs,0);(modinfo_fe_block,0)] inv_start_regs mf).
  { apply inv_start_rep_from_storage;[exact SG|exact Packed|exact FSF|exact GlobalF]. }
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

Theorem fe_inv_entry_to_core w m bx sbase bd dbase :
  square_input_bounds w -> fe_at m bx sbase (words5 w) -> modinfo_fe_global_rep m ->
  exists bt bs mi mf,
  function_entry2 secp_ge f_secp256k1_fe_inv_var
    [Vptr bd (Ptrofs.repr dbase);Vptr bx (Ptrofs.repr sbase)] m
    (fe_inv_env bt bs) (fe_inv_slice_temps bd dbase bx sbase) mi /\
  Clight2.exec_stmt secp_ge (fe_inv_env bt bs) (fe_inv_slice_temps bd dbase bx sbase) mi
    fe_inv_prefix E0 (fe_inv_slice_temps bd dbase bx sbase) mf Out_normal /\
  rep (fe_inv_packed_words w) [(bs,0);(modinfo_fe_block,0)] inv_start_regs mf /\
  fe_at mf bs 0 (words5 (fe_inv_packed_words w)) /\
  fe_at mf bt 0 (words5 (fe_inv_canonical_words w)) /\ fe_at mf bx sbase (words5 w) /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  signed62_normalized (fe_inv_packed_words w) /\
  signed62_unsigned_value (fe_inv_packed_words w)=fe_inv_value w /\
  modinfo_fe_global_rep mf /\ bt<>bs /\
  ~Mem.valid_block m bt /\ ~Mem.valid_block m bs /\ lframe (fun _ _=>True) m mf.
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
  assert (TG : bt<>modinfo_fe_block) by (intro Eq;apply FreshT;rewrite Eq;exact (proj1 Global)).
  assert (SG : bs<>modinfo_fe_block) by (intro Eq;apply FreshS;rewrite Eq;exact (proj1 Global)).
  assert (TB : bt<>bx) by (intro Eq;apply FreshT;rewrite Eq;exact ValidX).
  assert (SB : bs<>bx) by (intro Eq;apply FreshS;rewrite Eq;exact ValidX).
  assert (TS : bt<>bs).
  { intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ AS);rewrite <-Eq;eapply Mem.valid_new_block;exact AT. }
  assert (AllocFrame : lframe (fun _ _=>True) m mi).
  { eapply lframe_trans;apply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption. }
  assert (FieldI : fe_at mi bx sbase (words5 w)).
  { eapply curve_keep_field_range;[reflexivity|exact Field|exact AllocFrame|];intros;exact I. }
  assert (GlobalI : modinfo_fe_global_rep mi).
  { eapply modinfo_fe_global_lframe;[exact Global|exact AllocFrame|];intros;exact I. }
  assert (FT : Mem.range_perm mi bt 0 40 Cur Freeable).
  { intros pos HP;eapply Mem.perm_alloc_1;[exact AS|];eapply Mem.perm_alloc_2;eassumption. }
  assert (FS : Mem.range_perm mi bs 0 40 Cur Freeable).
  { intros pos HP;eapply Mem.perm_alloc_2;eassumption. }
  destruct (exec_fe_inv_prefix (fe_inv_slice_temps bd dbase bx sbase) w mi bx sbase bt bs
    eq_refl Bounds FieldI FT FS TB SB TS TG SG GlobalI)
    as (mf & Body & Core & Packed & Canonical & Source & FTF & FSF & Normalized & Numeric & GlobalF & BodyFrame).
  assert (OldFrame : lframe (fun b _=>Mem.valid_block m b) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact AllocFrame|];intros;exact I.
    - eapply lframe_implies;[exact BodyFrame|];intros b pos Old Valid;split;intro Eq;subst b;contradiction. }
  assert (Frame : lframe (fun _ _=>True) m mf).
  { eapply lframe_implies;[exact OldFrame|];intros b pos _ Valid;exact Valid. }
  exists bt,bs,mi,mf;split;[eapply fe_inv_slice_entry;eassumption|].
  repeat first [assumption|split].
Qed.
