(** Original scalar_inverse_var entry/packing and unpacking/cleanup. The
    intervening modular-inverse call remains a required separate proof. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements C.jet_secp_curve_frame.
Require Import C.jet_secp_scalar_signed62 C.jet_secp_scalar_signed62_numeric C.jet_secp_signed62_numeric.
Require Import C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_add_initial C.jet_secp_scalar_add_reader_support.
Require Import C.jet_secp_scalar_overflow_numeric C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_closed_helpers C.jet_clight_internal_preserve C.jet_clight_internal_frame.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_inv_env bs := PTree.set _s (bs,Tstruct _secp256k1_modinv64_signed62 noattr) empty_env.
Definition scalar_inv_temps bd bx := PTree.set _x (Vptr bx Ptrofs.zero)
  (PTree.set _r (Vptr bd Ptrofs.zero) (create_undef_temps(fn_temps f_secp256k1_scalar_inverse_var))).
Definition scalar_inv_s_address := Eaddrof(Evar _s (Tstruct _secp256k1_modinv64_signed62 noattr))
  (tptr(Tstruct _secp256k1_modinv64_signed62 noattr)).
Definition scalar_inv_modinfo_block := secp_symbol_block _secp256k1_const_modinfo_scalar.
Definition scalar_inv_modinfo_address := Eaddrof
  (Evar _secp256k1_const_modinfo_scalar (Tstruct _secp256k1_modinv64_modinfo noattr))
  (tptr(Tstruct _secp256k1_modinv64_modinfo noattr)).
Definition scalar_inv_pack := curve_call _secp256k1_scalar_to_signed62 f_secp256k1_scalar_to_signed62 None
  [scalar_inv_s_address;Etempvar _x (tptr(Tstruct __5826 noattr))].
Definition scalar_inv_core := curve_call _secp256k1_modinv64_var f_secp256k1_modinv64_var None
  [scalar_inv_s_address;scalar_inv_modinfo_address].
Definition scalar_inv_unpack := curve_call _secp256k1_scalar_from_signed62 f_secp256k1_scalar_from_signed62 None
  [Etempvar _r (tptr(Tstruct __5826 noattr));scalar_inv_s_address].

Lemma scalar_inv_body_source : fn_body f_secp256k1_scalar_inverse_var=
  Ssequence scalar_inv_pack (Ssequence scalar_inv_core scalar_inv_unpack).
Proof. reflexivity. Qed.
Lemma scalar_inv_modinfo_symbol : Genv.find_symbol secp_ge _secp256k1_const_modinfo_scalar=Some scalar_inv_modinfo_block.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge scalar_inv_modinfo_block.

Lemma scalar_inv_entry m mi bs bd bx : Mem.alloc m 0 40=(mi,bs) ->
  function_entry2 secp_ge f_secp256k1_scalar_inverse_var [Vptr bd Ptrofs.zero;Vptr bx Ptrofs.zero]
    m (scalar_inv_env bs) (scalar_inv_temps bd bx) mi.
Proof.
  intro Alloc;assert(Ok:fn_okb f_secp256k1_scalar_inverse_var=true) by reflexivity.
  destruct(fn_okb_true _ Ok) as (N1 & N2 & Disjoint).
  constructor;[exact N1|exact N2|exact Disjoint| |reflexivity].
  eapply alloc_variables_cons with (m1:=mi) (b1:=bs);[exact Alloc|constructor].
Qed.

Lemma scalar_inv_blocks bs : blocks_of_env secp_ge (scalar_inv_env bs)=[(bs,0,40)].
Proof. reflexivity. Qed.

Lemma scalar_inv_core_arguments bs le m :
  eval_exprlist secp_ge (scalar_inv_env bs) le m [scalar_inv_s_address;scalar_inv_modinfo_address]
    (type_of_params(fn_params f_secp256k1_modinv64_var))
    [Vptr bs Ptrofs.zero;Vptr scalar_inv_modinfo_block Ptrofs.zero].
Proof.
  eapply eval_Econs.
  - unfold scalar_inv_s_address;apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
  - reflexivity.
  - eapply eval_Econs.
    + unfold scalar_inv_modinfo_address;apply eval_Eaddrof;apply eval_Evar_global;
        [reflexivity|exact scalar_inv_modinfo_symbol].
    + reflexivity.
    + constructor.
Qed.

Theorem scalar_inv_entry_to_core w m bd bx :
  scalar_at m bx 0 (scalar_add_values w 0) ->
  Mem.range_perm m bx 0 32 Cur Freeable -> Mem.range_perm m bd 0 32 Cur Freeable ->
  exists bs mi mp,
  function_entry2 secp_ge f_secp256k1_scalar_inverse_var [Vptr bd Ptrofs.zero;Vptr bx Ptrofs.zero]
    m (scalar_inv_env bs) (scalar_inv_temps bd bx) mi /\
  Clight2.exec_stmt secp_ge (scalar_inv_env bs) (scalar_inv_temps bd bx) mi scalar_inv_pack
    E0 (scalar_inv_temps bd bx) mp Out_normal /\
  eval_exprlist secp_ge (scalar_inv_env bs) (scalar_inv_temps bd bx) mp
    [scalar_inv_s_address;scalar_inv_modinfo_address]
    (type_of_params(fn_params f_secp256k1_modinv64_var))
    [Vptr bs Ptrofs.zero;Vptr scalar_inv_modinfo_block Ptrofs.zero] /\
  fe_at mp bs 0 (words5(scalar62_words true w)) /\ signed62_normalized(scalar62_words true w) /\
  signed62_unsigned_value(scalar62_words true w)=scalar_limb_value w /\
  scalar_at mp bx 0 (scalar_add_values w 0) /\
  Mem.range_perm mp bs 0 40 Cur Freeable /\ Mem.range_perm mp bx 0 32 Cur Freeable /\
  Mem.range_perm mp bd 0 32 Cur Freeable /\ bs<>bx /\ bd<>bs /\ ~Mem.valid_block m bs /\
  lframe (fun b _=>b<>bs /\ b<>bx) m mp.
Proof.
  intros Source FX FD;destruct(Mem.alloc m 0 40) as (mi,bs) eqn:Alloc.
  pose proof(Mem.fresh_block_alloc _ _ _ _ _ Alloc) as Fresh.
  assert(VX:Mem.valid_block m bx) by (eapply Mem.perm_valid_block;apply(FX 0);lia).
  assert(VD:Mem.valid_block m bd) by (eapply Mem.perm_valid_block;apply(FD 0);lia).
  assert(SX:bs<>bx) by (intro Same;subst bs;contradiction).
  assert(DS:bd<>bs) by (intro Same;subst bd;contradiction).
  assert(AllocFrame:lframe (fun _ _=>True) m mi) by (apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc).
  assert(Input:scalar_at mi bx 0 (scalar_add_values w 0)).
  { eapply scalar_at_lframe;[exact Source|exact AllocFrame|];intros;exact I. }
  assert(FXI:Mem.range_perm mi bx 0 32 Cur Freeable).
  { intros pos Range;eapply Mem.perm_alloc_1;[exact Alloc|apply FX;exact Range]. }
  assert(FDI:Mem.range_perm mi bd 0 32 Cur Freeable).
  { intros pos Range;eapply Mem.perm_alloc_1;[exact Alloc|apply FD;exact Range]. }
  assert(FS:Mem.range_perm mi bs 0 40 Cur Freeable) by (intros pos Range;eapply Mem.perm_alloc_2;eassumption).
  destruct(eval_scalar_to62_value w mi bs bx SX FS Input FXI)
    as (mp & Pack & Packed & Normal & Value & InputP & FSP & FXP & PackFrame).
  assert(FDP:Mem.range_perm mp bd 0 32 Cur Freeable).
  { destruct(Pos.eq_dec bd bx) as [Same|Different];[subst bd;exact FXP|].
    eapply curve_keep_free;[lia|exact FDI|exact PackFrame|];intros;split;assumption. }
  assert(Exec:Clight2.exec_stmt secp_ge (scalar_inv_env bs) (scalar_inv_temps bd bx) mi scalar_inv_pack
    E0 (scalar_inv_temps bd bx) mp Out_normal).
  { unfold scalar_inv_pack;eapply exec_curve_call with (vargs:=[Vptr bs Ptrofs.zero;Vptr bx Ptrofs.zero]) (v:=Vundef).
    - unfold secp_pure;repeat(first[left;reflexivity|right]).
    - reflexivity.
    - eapply eval_Econs.
      + unfold scalar_inv_s_address;apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
      + reflexivity.
      + eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|constructor].
    - exact Pack. }
  assert(Frame:lframe (fun b _=>b<>bs /\ b<>bx) m mp).
  { eapply lframe_trans;[|exact PackFrame].
    eapply lframe_implies;[exact AllocFrame|];intros;exact I. }
  pose proof(scalar_inv_entry m mi bs bd bx Alloc) as Entry.
  pose proof(scalar_inv_core_arguments bs (scalar_inv_temps bd bx) mp) as Args.
  exists bs,mi,mp;repeat first[assumption|split].
Qed.

Theorem exec_scalar_inv_unpack_and_free le m bs bd w :
  le!_r=Some(Vptr bd Ptrofs.zero) -> bd<>bs -> signed62_normalized w ->
  fe_at m bs 0 (words5 w) -> Mem.range_perm m bs 0 40 Cur Freeable ->
  Mem.range_perm m bd 0 32 Cur Freeable -> exists mf mr,
  Clight2.exec_stmt secp_ge (scalar_inv_env bs) le m scalar_inv_unpack E0 le mf Out_normal /\
  Mem.free_list mf (blocks_of_env secp_ge (scalar_inv_env bs))=Some mr /\
  scalar_at mr bd 0 (scalar_add_values(scalar62_words false w)0) /\
  scalar_limb_value(scalar62_words false w)=signed62_unsigned_value w /\
  Mem.range_perm mr bd 0 32 Cur Freeable /\ lframe (fun b _=>b<>bd /\ b<>bs) m mr.
Proof.
  intros Result Separate Normal Input FS FD.
  destruct(eval_scalar_from62_value w m bd bs Normal Separate FD Input FS)
    as (mf & Call & Output & Value & Source & FDF & FSF & Frame).
  assert(Exec:Clight2.exec_stmt secp_ge (scalar_inv_env bs) le m scalar_inv_unpack E0 le mf Out_normal).
  { unfold scalar_inv_unpack;eapply exec_curve_call with (vargs:=[Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero]) (v:=Vundef).
    - unfold secp_pure;repeat(first[left;reflexivity|right]).
    - reflexivity.
    - eapply eval_Econs;[apply eval_Etempvar;exact Result|reflexivity|].
      eapply eval_Econs;[unfold scalar_inv_s_address;apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
    - exact Call. }
  destruct(free_list_exists [(bs,0,40)] mf) as (mr & Free & Unchanged).
  - cbn;repeat constructor;cbn;tauto.
  - intros b lo hi [Eq|Nil];[injection Eq as <- <- <-;exact FSF|contradiction].
  - assert(Freed:lframe (fun b _=>b<>bs) mf mr).
    { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|];intros b pos Different Valid;cbn;intuition congruence. }
    assert(OutputR:scalar_at mr bd 0 (scalar_add_values(scalar62_words false w)0)).
    { eapply scalar_at_lframe;[exact Output|exact Freed|];intros;exact Separate. }
    assert(FDR:Mem.range_perm mr bd 0 32 Cur Freeable).
    { eapply curve_keep_free;[lia|exact FDF|exact Freed|];intros;exact Separate. }
    assert(Whole:lframe (fun b _=>b<>bd /\ b<>bs) m mr).
    { eapply lframe_trans;[exact Frame|].
      eapply lframe_implies;[exact Freed|];intros b pos [_ Different] Valid;exact Different. }
    exists mf,mr;rewrite scalar_inv_blocks;repeat first[assumption|split].
Qed.

(** A checked call context for the remaining core proof. The actual core
    execution and its live, canonically positioned result are premises here, not new axioms
    or a public scalar-invert theorem. Entry/packing come from the checked
    prefix above; this theorem derives unpacking/cleanup and the whole call. *)
Theorem scalar_inv_call_from_core w m mi mp mc bs bd bx :
  function_entry2 secp_ge f_secp256k1_scalar_inverse_var [Vptr bd Ptrofs.zero;Vptr bx Ptrofs.zero]
    m (scalar_inv_env bs) (scalar_inv_temps bd bx) mi ->
  Clight2.exec_stmt secp_ge (scalar_inv_env bs) (scalar_inv_temps bd bx) mi scalar_inv_pack
    E0 (scalar_inv_temps bd bx) mp Out_normal ->
  Clight2.eval_funcall secp_ge mp (Internal f_secp256k1_modinv64_var)
    [Vptr bs Ptrofs.zero;Vptr scalar_inv_modinfo_block Ptrofs.zero] E0 mc Vundef ->
  bd<>bs -> signed62_normalized w -> fe_at mc bs 0 (words5 w) ->
  Mem.range_perm mc bs 0 40 Cur Freeable -> Mem.range_perm mc bd 0 32 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_inverse_var)
    [Vptr bd Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf Vundef /\
  scalar_at mf bd 0 (scalar_add_values(scalar62_words false w)0) /\
  scalar_limb_value(scalar62_words false w)=signed62_unsigned_value w /\
  Mem.range_perm mf bd 0 32 Cur Freeable /\ lframe (fun b _=>b<>bd /\ b<>bs) mc mf /\
  (readonly_preserved mp mc -> readonly_preserved m mf).
Proof.
  intros Entry Pack Core Separate Normal Input FS FD.
  destruct(exec_scalar_inv_unpack_and_free (scalar_inv_temps bd bx) mc bs bd w
    ltac:(reflexivity) Separate Normal Input FS FD)
    as (mu & mf & Unpack & Free & Output & Value & Owned & Frame).
  assert(CoreStmt:Clight2.exec_stmt secp_ge (scalar_inv_env bs) (scalar_inv_temps bd bx) mp scalar_inv_core
    E0 (scalar_inv_temps bd bx) mc Out_normal).
  { unfold scalar_inv_core;eapply exec_curve_call with
      (vargs:=[Vptr bs Ptrofs.zero;Vptr scalar_inv_modinfo_block Ptrofs.zero]) (v:=Vundef).
    - unfold secp_pure;repeat(first[left;reflexivity|right]).
    - reflexivity.
    - apply scalar_inv_core_arguments.
    - exact Core. }
  assert(Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_inverse_var)
    [Vptr bd Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf Vundef).
  { eapply eval_funcall_internal with (e:=scalar_inv_env bs) (le1:=scalar_inv_temps bd bx)
      (m1:=mi) (le2:=scalar_inv_temps bd bx) (m2:=mu) (out:=Out_normal).
    - exact Entry.
    - rewrite scalar_inv_body_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mp)
        (le1:=scalar_inv_temps bd bx);[exact Pack|].
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc)
        (le1:=scalar_inv_temps bd bx);[exact CoreStmt|exact Unpack].
    - reflexivity.
    - exact Free. }
  exists mf;split;[exact Call|];split;[exact Output|];split;[exact Value|];split;[exact Owned|];split;[exact Frame|].
  intro CoreReadonly.
  assert(Plain:plain_env(scalar_inv_env bs)) by(eapply entry_plain;[exact Entry|reflexivity]).
  eapply preserved_trans;[eapply entry_preserved;exact Entry|].
  eapply preserved_trans.
  - eapply secp_closed_stmt_preserved;[exact Pack|exact Plain|vm_compute;reflexivity].
  - eapply preserved_trans;[exact CoreReadonly|].
    eapply preserved_trans;[|eapply freelist_preserved;exact Free].
    eapply secp_closed_stmt_preserved;[exact Unpack|exact Plain|vm_compute;reflexivity].
Qed.
