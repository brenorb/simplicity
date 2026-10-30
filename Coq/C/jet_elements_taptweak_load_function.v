(** Entire original opaque public-key loader, including both guard outcomes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_memcpy_model
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge
 C.jet_secp_affine_storage C.jet_secp_table_decode C.jet_secp_pubkey_copy
 C.jet_clight_internal_preserve C.jet_clight_internal_permissions C.jet_secp_field_read_preservation.
Require Import C.jet_secp_pubkey_load_entry C.jet_secp_pubkey_load_body.
Require Import C.jet_secp_pubkey_load_function C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_load_body C.jet_elements_taptweak_save_copy C.jet_elements_taptweak_parser
 C.jet_elements_taptweak_parse_start C.jet_transport.
From compcert Require Import Globalenvs.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_load_vars_checked:
 vars_okb secp_ge elements_taptweak_ge(fn_vars f_secp256k1_pubkey_load)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_pubkey_load_lookup:
 secp_helper_lookup elements_taptweak_ge(_secp256k1_pubkey_load,f_secp256k1_pubkey_load)=
 Some(Internal f_secp256k1_pubkey_load).
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge.
Lemma elements_taptweak_load_blocks bs bx b_y:
 blocks_of_env elements_taptweak_ge(pubkey_load_env bs bx b_y)=[(bs,0,64);(b_y,0,40);(bx,0,40)].
Proof.
 change ([(bs,0,sizeof elements_taptweak_ge pubkey_storage_type);
 (b_y,0,sizeof elements_taptweak_ge curve_fe_type);(bx,0,sizeof elements_taptweak_ge curve_fe_type)]=
 [(bs,0,64);(b_y,0,40);(bx,0,40)]).
 rewrite elements_taptweak_pubkey_storage_size,(proj1 elements_taptweak_parser_sizes);reflexivity.
Qed.
Theorem elements_taptweak_load_entry_owned m out key:
 exists mi bs bx b_y,
 function_entry2 elements_taptweak_ge f_secp256k1_pubkey_load [out;key] m
  (pubkey_load_env bs bx b_y) (pubkey_load_temps out key) mi /\
 NoDup [bs;bx;b_y] /\
 (forall b,Mem.valid_block m b ->~In b [bs;bx;b_y]) /\
 (forall b hi,In (b,hi) [(bs,64);(bx,40);(b_y,40)] ->Mem.range_perm mi b 0 hi Cur Freeable) /\
 lframe (fun _ _=>True) m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct(pubkey_load_entry_owned m out key)as(mi & bs & bx & b_y & Entry & Memory).
 exists mi,bs,bx,b_y;split;[|exact Memory].
 inversion Entry as [Vars Params Disjoint Alloc Bind];subst.
 constructor;[exact Vars|exact Params|exact Disjoint| |exact Bind].
 eapply(alloc_variables_transport secp_ge elements_taptweak_ge);
 [exact Alloc|exact elements_taptweak_load_vars_checked].
Qed.
Theorem eval_elements_taptweak_pubkey_load (Model:memcpy_model) w m bin base bout:
 Mem.range_perm m bout 0 88 Cur Freeable ->affine_storage_readable m bin base w ->
 exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_pubkey_load)
  [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr base)] E0 mf
  (Vint (bit_int (pubkey_storage_accept w))) /\
 (forall k:bool,fe_at mf bout (if k then 40 else 0) (words5 (affine_storage_coord w k))) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\Mem.range_perm mf bout 0 88 Cur Freeable /\
 lframe (fun b _=>b<>bout) m mf /\readonly_preserved m mf.
Proof.
 intros Free Input.
 assert (VO:Mem.valid_block m bout) by (eapply Mem.perm_valid_block;apply (Free 0);lia).
 assert (VI:Mem.valid_block m bin).
 { destruct Input as (_ & _ & _ & Read & _);eapply Mem.perm_valid_block;apply (Read base);lia. }
 destruct (elements_taptweak_load_entry_owned m (Vptr bout Ptrofs.zero) (Vptr bin (Ptrofs.repr base)))
 as (mi & bs & bx & b_y & Entry & Separate & Fresh & OwnedI & FrameI & KeepI & ReadI).
 assert (InputI:affine_storage_readable mi bin base w).
 { eapply affine_storage_readable_lframe;[exact Input|exact FrameI|intros;exact I]. }
 assert (OutFresh:~In bout [bs;bx;b_y]) by (apply Fresh;exact VO).
 assert (SourceSep:bin<>bs).
 { intro Same;apply (Fresh bin VI);rewrite Same;left;reflexivity. }
 assert (AllSeparate:NoDup [bout;bs;bx;b_y]) by (constructor;assumption).
 assert (OwnedAll:forall b hi,In (b,hi) [(bout,88);(bs,64);(bx,40);(b_y,40)] ->Mem.range_perm mi b 0 hi Cur Freeable).
 { intros b hi [Same|Slot].
   - inversion Same;subst b hi;intros pos Pos;apply KeepI;apply Free;exact Pos.
   - apply OwnedI;exact Slot. }
 destruct (exec_elements_taptweak_pubkey_load_body Model w (pubkey_load_env bs bx b_y)
  (pubkey_load_temps (Vptr bout Ptrofs.zero) (Vptr bin (Ptrofs.repr base))) mi bin base bout bs bx b_y
  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl AllSeparate SourceSep OwnedAll InputI)
 as (mb & lef & Body & Fields & Flag & OwnedB & FrameB & ReadB).
 destruct (free_list_exists [(bs,0,64);(b_y,0,40);(bx,0,40)] mb) as (mf & FreeLocals & UnchangedF).
 - clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;
   repeat constructor;cbn;intuition congruence.
 - intros b lo hi Slot;cbn [In] in Slot;
   repeat destruct Slot as [Slot|Slot];try contradiction;inversion Slot;subst b lo hi;
    apply OwnedB;clear;cbn [In];tauto.
 - assert (FrameF:lframe (fun b _=>~In b [bs;bx;b_y]) mb mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact UnchangedF|].
     intros b pos Outside _;clear -Outside;cbn [map fst In] in *;tauto. }
   assert (FieldsF:forall k:bool,fe_at mf bout (if k then 40 else 0) (words5 (affine_storage_coord w k))).
   { intro k;eapply field_at_lframe;[apply Fields|exact FrameF|intros;exact OutFresh]. }
   assert (FlagF:Mem.load Mint32 mf bout 80=Some (Vint Int.zero)).
   { rewrite (proj1 FrameF Mint32 bout 80);[exact Flag| |intros;exact OutFresh].
     eapply Mem.perm_valid_block;apply (OwnedB bout 88 ltac:(clear;cbn [In];tauto) 0);lia. }
   assert (FreeOut:Mem.range_perm mf bout 0 88 Cur Freeable).
   { eapply curve_keep_free;[lia|apply OwnedB;clear;cbn [In];tauto|exact FrameF|intros;exact OutFresh]. }
   exists mf;split.
   + eapply eval_funcall_internal with (e:=pubkey_load_env bs bx b_y)
      (le1:=pubkey_load_temps (Vptr bout Ptrofs.zero) (Vptr bin (Ptrofs.repr base)))
      (le2:=lef) (m1:=mi) (m2:=mb)
      (out:=Out_return (Some (Vint (bit_int (pubkey_storage_accept w)),tint))).
     * exact Entry.
     * exact Body.
     * split;[discriminate|reflexivity].
     * rewrite elements_taptweak_load_blocks;exact FreeLocals.
   + split;[exact FieldsF|];split;[exact FlagF|];split;[exact FreeOut|];split.
     * eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\b<>bout).
       { eapply lframe_trans.
         - eapply lframe_implies;[exact FrameI|intros;exact I].
         - eapply lframe_trans.
           + eapply lframe_implies;[exact FrameB|].
             intros b pos [Valid Outside] _;split;[exact Outside|].
             intro Same;apply (Fresh b Valid);rewrite Same;left;reflexivity.
           + eapply lframe_implies;[exact FrameF|].
             intros b pos [Valid _] _;apply Fresh;exact Valid. }
       intros b pos Outside Valid;split;assumption.
     * eapply preserved_trans;[exact ReadI|].
       eapply preserved_trans;[exact ReadB|eapply freelist_preserved;exact FreeLocals].
Qed.
Lemma elements_taptweak_xonly_load_entry m out key:
 function_entry2 elements_taptweak_ge f_secp256k1_xonly_pubkey_load [out;key] m empty_env
  (pubkey_load_temps out key) m.
Proof.
 constructor.
 - constructor.
 - repeat constructor;cbn;intuition discriminate.
 - intros x y HX HY Same;cbn in HX,HY.
   repeat match type of HX with _\/_=>destruct HX as [HX|HX] end;
   repeat match type of HY with _\/_=>destruct HY as [HY|HY] end;
   try contradiction;subst;discriminate.
 - constructor.
 - reflexivity.
Qed.
Theorem eval_elements_taptweak_xonly_pubkey_load (Model:memcpy_model) w m bin base bout:
 Mem.range_perm m bout 0 88 Cur Freeable ->affine_storage_readable m bin base w ->
 exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_xonly_pubkey_load)
  [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr base)] E0 mf
  (Vint (bit_int (pubkey_storage_accept w))) /\
 (forall k:bool,fe_at mf bout (if k then 40 else 0) (words5 (affine_storage_coord w k))) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\Mem.range_perm mf bout 0 88 Cur Freeable /\
 lframe (fun b _=>b<>bout) m mf /\readonly_preserved m mf.
Proof.
 intros Free Input.
 destruct (eval_elements_taptweak_pubkey_load Model w m bin base bout Free Input)
 as (mf & Load & Fields & Flag & FreeOut & Frame & Read).
 pose (le:=pubkey_load_temps (Vptr bout Ptrofs.zero) (Vptr bin (Ptrofs.repr base))).
 pose (value:=Vint (bit_int (pubkey_storage_accept w))).
 assert (Call:Clight2.exec_stmt elements_taptweak_ge empty_env le m
  (curve_call _secp256k1_pubkey_load f_secp256k1_pubkey_load (Some _t'1)
   [Etempvar _ge (tptr (Tstruct __6121 noattr));
    Ecast (Etempvar _pubkey (tptr (Tstruct __6478 noattr))) (tptr pubkey_opaque_type)])
  E0 (PTree.set _t'1 value le) mf Out_normal).
 { destruct(secp_helper_lookup_exists elements_taptweak_ge _ _ elements_taptweak_pubkey_load_lookup)as(bf & Sym & Funct).
   eapply exec_elements_taptweak_curve_call with(bf:=bf)(vargs:=[Vptr bout Ptrofs.zero;Vptr bin(Ptrofs.repr base)])(v:=value).
   - exact Sym.
   - unfold Genv.find_funct;rewrite pred_dec_true by reflexivity;exact Funct.
   - reflexivity.
   - eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|].
     eapply eval_Econs;[eapply eval_Ecast;[apply eval_Etempvar;reflexivity|reflexivity]|reflexivity|constructor].
   - exact Load. }
 exists mf;split.
 - eapply eval_funcall_internal with (e:=empty_env) (le1:=le) (le2:=PTree.set _t'1 value le)
    (m1:=m) (m2:=mf) (out:=Out_return (Some (value,tint))).
   + apply elements_taptweak_xonly_load_entry.
   + change (Clight2.exec_stmt elements_taptweak_ge empty_env le m
      (Ssequence
       (curve_call _secp256k1_pubkey_load f_secp256k1_pubkey_load (Some _t'1)
        [Etempvar _ge (tptr (Tstruct __6121 noattr));
         Ecast (Etempvar _pubkey (tptr (Tstruct __6478 noattr))) (tptr pubkey_opaque_type)])
       (Sreturn (Some (Etempvar _t'1 tint)))) E0 (PTree.set _t'1 value le) mf
      (Out_return (Some (value,tint)))).
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set _t'1 value le);[exact Call|].
     apply exec_Sreturn_some;apply eval_Etempvar;apply PTree.gss.
   + split;[discriminate|reflexivity].
   + reflexivity.
 - repeat first [assumption|split].
Qed.

Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_memcpy_model C.jet_secp_linkage C.jets_secp
 C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge
 C.jet_secp_affine_storage C.jet_secp_storage_numeric C.jet_secp_pubkey_load_function
 C.jet_secp_pubkey_load_body C.jet_secp_field_zero_readonly C.jet_secp_curve_literal C.jet_secp_curve_polynomial
 C.jet_clight_internal_preserve.
Require Import C.jet_secp_pubkey_load_coordinates.
Theorem eval_elements_taptweak_xonly_pubkey_load_coordinates (Model:memcpy_model) w m bin base bout
 (x y:Ty.tySem (Word 8)):
 Mem.range_perm m bout 0 88 Cur Freeable ->affine_storage_readable m bin base w ->
 field_storage_value w=@toZ (WordToZ 8) x ->
 field_storage_value (fun i=>w (4+i)%nat)=@toZ (WordToZ 8) y ->
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Simplicity.Alg.CoreFunSem (x,y))=true ->
 exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_xonly_pubkey_load)
  [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr base)] E0 mf (Vint Int.one) /\
 fe_at mf bout 0 (map Int64.repr (fe_limbs_of (@toZ (WordToZ 8) x))) /\
 fe_at mf bout 40 (map Int64.repr (fe_limbs_of (@toZ (WordToZ 8) y))) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\Mem.range_perm mf bout 0 88 Cur Freeable /\
 lframe (fun b _=>b<>bout) m mf /\readonly_preserved m mf.
Proof.
 intros Free Input X Y Curve.
 destruct (eval_elements_taptweak_xonly_pubkey_load Model w m bin base bout Free Input)
 as (mf & Call & Fields & Flag & FreeOut & Frame & Read).
 rewrite (pubkey_storage_accept_curve w x y X Curve) in Call.
 exists mf;split;[exact Call|];split.
 - pose proof (Fields false) as FX;rewrite affine_storage_coord_canonical in FX.
   change (fe_at mf bout 0 (map Int64.repr (fe_limbs_of (field_storage_value w)))) in FX.
   rewrite X in FX;exact FX.
 - split.
   + pose proof (Fields true) as FY;rewrite affine_storage_coord_canonical in FY.
     change (fe_at mf bout 40 (map Int64.repr (fe_limbs_of (field_storage_value (fun i=>w (4+i)%nat))))) in FY.
     rewrite Y in FY;exact FY.
   + repeat first [assumption|split].
Qed.
