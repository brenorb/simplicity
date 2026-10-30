(** Original native-to-x-only conversion with the NULL parity argument used by TapTweak. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_secp_statement_prefix C.jet_sx_mem C.jet_sx_exec C.jet_readBit_layout C.jet_clight_nonnull_guard
 C.jet_secp_xonly_tweak_entry C.jet_secp_xonly_parse_control C.jet_secp_extrakeys_even_y
 C.jet_secp_affine_storage C.jet_secp_storage_numeric C.jet_secp_table_decode
 C.jet_secp_pubkey_load_function C.jet_secp_pubkey_load_body C.jet_secp_pubkey_save_function C.jet_secp_ge_storage_body
 C.jet_secp_xonly_tweak_function C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_field_mul_small
 C.jet_secp_field_read_preservation C.jet_secp_field_negate_separate C.jet_secp_square_columns
 C.jet_secp_multiply_normalize_bridge C.jet_secp_rescale_literal C.jet_secp_curve_frame
 C.jet_memcpy_model C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition xonly_from_temps bout bin:=PTree.set _pubkey (Vptr bin Ptrofs.zero)
 (PTree.set _pk_parity (Vlong Int64.zero) (PTree.set _xonly_pubkey (Vptr bout Ptrofs.zero)
 (create_undef_temps (fn_temps f_secp256k1_xonly_pubkey_from_pubkey)))).
Definition xonly_from_start:=[nonnull_return_zero _xonly_pubkey (Tstruct __6478 noattr);
 nonnull_return_zero _pubkey (Tstruct __2078 noattr)].
Definition xonly_from_load:=curve_call _secp256k1_pubkey_load f_secp256k1_pubkey_load (Some _t'1)
 [Eaddrof (Evar _pk curve_ge_type) (tptr curve_ge_type);Etempvar _pubkey (tptr (Tstruct __2078 noattr))].
Definition xonly_from_even:=curve_call _secp256k1_extrakeys_ge_even_y f_secp256k1_extrakeys_ge_even_y (Some _t'2)
 [Eaddrof (Evar _pk curve_ge_type) (tptr curve_ge_type)].
Definition xonly_from_parity:=Sifthenelse
 (Ebinop One (Etempvar _pk_parity (tptr tint)) (Ecast (Econst_int Int.zero tint) (tptr tvoid)) tint)
 (Sassign (Ederef (Etempvar _pk_parity (tptr tint)) tint) (Etempvar _tmp tint)) Sskip.
Definition xonly_from_save:=curve_call _secp256k1_xonly_pubkey_save f_secp256k1_xonly_pubkey_save None
 [Etempvar _xonly_pubkey (tptr (Tstruct __6478 noattr));Eaddrof (Evar _pk curve_ge_type) (tptr curve_ge_type)].
Definition xonly_from_tail:=Ssequence (Ssequence xonly_from_load (xonly_parse_guard _t'1))
 (Ssequence (Ssequence xonly_from_even (Sset _tmp (Etempvar _t'2 tint)))
 (Ssequence xonly_from_parity (Ssequence xonly_from_save (Sreturn (Some (Econst_int Int.one tint)))))).
Lemma xonly_from_body_source:fn_body f_secp256k1_xonly_pubkey_from_pubkey=statement_sequence xonly_from_start xonly_from_tail.
Proof. reflexivity. Qed.
Lemma affine_storage_small_bounds w k:mul_small_input_bounds (affine_storage_coord w k).
Proof.
 intros i Index;unfold affine_storage_coord;pose proof (storage_unpack_limb_bounds
  (fun j=>w ((if k then 4 else 0)+j)%nat)) as Bounds.
 unfold fe_limbs_ok in Bounds;destruct i as [|[|[|[|[|i]]]]];try lia;cbn [Nat.eqb];lia.
Qed.
Definition xonly_from_value w:=(rescale_field_output (affine_storage_coord w false),
 rescale_field_output (extrakeys_even_y_words (affine_storage_coord w true))).
Local Opaque secp_ge rescale_field_output.
Theorem eval_xonly_pubkey_from_pubkey_null (Copy:memcpy_model) w m bout bin:
 bout<>bin ->Mem.range_perm m bout 0 64 Cur Freeable ->Mem.range_perm m bin 0 64 Cur Freeable ->
 affine_storage_readable m bin 0 w ->pubkey_storage_accept w=true ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_xonly_pubkey_from_pubkey)
 [Vptr bout Ptrofs.zero;Vlong Int64.zero;Vptr bin Ptrofs.zero] E0 mf (Vint Int.one) /\
 xonly_tweak_saved_result (Some (xonly_from_value w)) mf bout /\
 Mem.range_perm mf bout 0 64 Cur Freeable /\Mem.range_perm mf bin 0 64 Cur Freeable /\
 lframe (fun b _=>b<>bout) m mf /\readonly_preserved m mf.
Proof.
 intros Separate FO FI Input Accept.
 assert (VO:Mem.valid_block m bout) by (eapply Mem.perm_valid_block;apply (FO 0);lia).
 assert (VI:Mem.valid_block m bin) by (eapply Mem.perm_valid_block;apply (FI 0);lia).
 destruct (Mem.alloc m 0 88) as (mi,bk) eqn:Alloc.
 pose (e:=xonly_tweak_env bk);pose (le:=xonly_from_temps bout bin).
 assert (Entry:function_entry2 secp_ge f_secp256k1_xonly_pubkey_from_pubkey
 [Vptr bout Ptrofs.zero;Vlong Int64.zero;Vptr bin Ptrofs.zero] m e le mi).
 { assert (OK:fn_okb f_secp256k1_xonly_pubkey_from_pubkey=true) by reflexivity.
   destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons;[exact Alloc|constructor]. }
 assert (Fresh:forall b,Mem.valid_block m b ->b<>bk).
 { intros b Valid Same;subst b;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Valid). }
 assert (OK:bout<>bk) by (apply Fresh;exact VO).
 assert (IK:bin<>bk) by (apply Fresh;exact VI).
 assert (FrameI:lframe (fun _ _=>True) m mi) by (apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc).
 assert (KeepI:keeps_permissions m mi) by (eapply entry_keeps_permissions;exact Entry).
 assert (ReadI:readonly_preserved m mi) by (eapply entry_preserved;exact Entry).
 assert (FKI:Mem.range_perm mi bk 0 88 Cur Freeable) by (intros pos Range;eapply Mem.perm_alloc_2;[exact Alloc|exact Range]).
 assert (Start:Clight2.exec_stmt secp_ge e le mi (statement_sequence xonly_from_start Sskip) E0 le mi Out_normal).
 { cbn [statement_sequence xonly_from_start];eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=le).
   - apply exec_nonnull_return_zero with (b:=bout) (ofs:=Ptrofs.zero);[reflexivity|].
     apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm;eapply Mem.perm_implies;
      [apply KeepI,FO;clear;change (0<=0<64);lia|apply perm_any_N].
   - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=le);[|constructor].
     apply exec_nonnull_return_zero with (b:=bin) (ofs:=Ptrofs.zero);[reflexivity|].
     apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm;eapply Mem.perm_implies;
      [apply KeepI,FI;clear;change (0<=0<64);lia|apply perm_any_N]. }
 assert (InputI:affine_storage_readable mi bin 0 w) by
  (eapply affine_storage_readable_lframe;[exact Input|exact FrameI|intros;exact I]).
 destruct (eval_pubkey_load Copy w mi bin 0 bk FKI InputI) as (ml & Load & Fields & Flag & FKL & FrameL & ReadL).
 rewrite Accept in Load.
 pose (lel:=PTree.set _t'1 (Vint Int.one) le).
 assert (LoadStmt:Clight2.exec_stmt secp_ge e le mi xonly_from_load E0 lel ml Out_normal).
 { unfold xonly_from_load;eapply exec_curve_call with (vargs:=[Vptr bk Ptrofs.zero;Vptr bin Ptrofs.zero]) (v:=Vint Int.one).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - reflexivity.
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|constructor].
   - exact Load. }
 pose (wx:=affine_storage_coord w false);pose (wy:=affine_storage_coord w true).
 destruct (eval_extrakeys_ge_even_y wy ml bk (affine_storage_small_bounds w true) (affine_storage_square_bounds w true)
  (Fields true) FKL Flag) as (mp & Even & YP & BYP & FKP & FrameP & ReadP).
 assert (XP:fe_at mp bk 0 (words5 wx)).
 { eapply curve_keep_field_range;[reflexivity|exact (Fields false)|exact FrameP|intros pos Range;right;left;clear -Range;lia]. }
 assert (FOP:Mem.range_perm mp bout 0 64 Cur Freeable).
 { eapply curve_keep_free;[clear;lia| |exact FrameP|intros;left;exact OK].
   eapply curve_keep_free;[clear;lia| |exact FrameL|intros;exact OK].
   intros pos Range;apply KeepI,FO;exact Range. }
 destruct (eval_xonly_pubkey_save Copy wx (extrakeys_even_y_words wy) mp bk bout
  (affine_storage_square_bounds w false) BYP XP YP FOP)
 as (mb & Save & Stored & FOB & FrameS & ReadS).
 pose (lep:=PTree.set _t'2 (Vint (bit_int (C.jet_secp_field_odd_words.field_words_odd wy))) lel).
 pose (lef:=PTree.set _tmp (Vint (bit_int (C.jet_secp_field_odd_words.field_words_odd wy))) lep).
 assert (EvenStmt:Clight2.exec_stmt secp_ge e lel ml xonly_from_even E0 lep mp Out_normal).
 { unfold xonly_from_even;eapply exec_curve_call with (vargs:=[Vptr bk Ptrofs.zero])
   (v:=Vint (bit_int (C.jet_secp_field_odd_words.field_words_odd wy))).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - reflexivity.
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
   - exact Even. }
 assert (ParityStmt:Clight2.exec_stmt secp_ge e lef mp xonly_from_parity E0 lef mp Out_normal).
 { unfold xonly_from_parity;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
   - eapply eval_Ebinop;[apply eval_Etempvar;reflexivity|eapply eval_Ecast;[constructor|reflexivity]|reflexivity].
   - reflexivity.
   - constructor. }
 assert (SaveStmt:Clight2.exec_stmt secp_ge e lef mp xonly_from_save E0 lef mb Out_normal).
 { unfold xonly_from_save;eapply exec_curve_call with (vargs:=[Vptr bout Ptrofs.zero;Vptr bk Ptrofs.zero]) (v:=Vundef).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - reflexivity.
   - eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
   - exact Save. }
 assert (FKB:Mem.range_perm mb bk 0 88 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FKP|exact FrameS|intros;clear -OK;congruence]. }
 destruct (xonly_tweak_free mb bk FKB) as (mf & Free & FrameF & ReadF).
 assert (Frame:lframe (fun b _=>b<>bout) m mf).
 { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\b<>bout).
   - eapply lframe_trans;[eapply lframe_implies;[exact FrameI|intros;exact I]|].
     eapply lframe_trans;[eapply lframe_implies;[exact FrameL|intros b pos [Old NO] Valid;apply Fresh;exact Old]|].
     eapply lframe_trans;[eapply lframe_implies;[exact FrameP|intros b pos [Old NO] Valid;left;apply Fresh;exact Old]|].
     eapply lframe_trans;
      [eapply lframe_implies;[exact FrameS|intros b pos [Old NO] Valid;exact NO]|
       eapply lframe_implies;[exact FrameF|intros b pos [Old NO] Valid;apply Fresh;exact Old]].
   - intros b pos NO Old;split;assumption. }
 exists mf;split.
 - eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=lef) (m1:=mi) (m2:=mb)
   (out:=Out_return (Some (Vint Int.one,tint))).
   + exact Entry.
   + rewrite xonly_from_body_source;eapply exec_statement_prefix_then_last;[exact Start|].
     unfold xonly_from_tail;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ml) (le1:=lel).
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact LoadStmt|apply exec_xonly_guard_one;apply PTree.gss].
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mp) (le1:=lef).
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact EvenStmt|apply exec_Sset;apply eval_Etempvar;apply PTree.gss].
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact ParityStmt|].
          eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact SaveStmt|apply exec_Sreturn_some;constructor].
   + split;[clear;discriminate|reflexivity].
   + exact Free.
 - split.
   + exists wx,(extrakeys_even_y_words wy);split.
     * eapply affine_storage_readable_lframe;[exact Stored|exact FrameF|intros;exact OK].
     * split;[apply affine_storage_square_bounds|];split;[exact BYP|reflexivity].
   + split.
     * eapply curve_keep_free;[clear;lia|exact FOB|exact FrameF|intros;exact OK].
     * split.
       -- eapply curve_keep_free;[clear;lia|exact FI|exact Frame|intros;clear -Separate;congruence].
       -- split;[exact Frame|].
          eapply preserved_trans;[exact ReadI|];eapply preserved_trans;[exact ReadL|];
          eapply preserved_trans;[exact ReadP|];eapply preserved_trans;[exact ReadS|exact ReadF].
Qed.
