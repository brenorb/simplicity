(** Fine memory frame of the original scalar byte parser with overflow output. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_exec C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_fe_b32 C.jet_secp_b32_exec C.jet_secp_linkage
 C.jet_secp_scalar_set_b32_exec C.jet_secp_scalar_set_shape C.jet_secp_scalar_set_bytes
 C.jet_secp_scalar_set_storage C.jet_secp_canonical_scalar C.jet_secp_local_regions
 C.jet_secp_shift64_statement C.jet_clight_internal_frame C.jet_clight_internal_permissions
 C.jet_clight_internal_preserve C.jet_secp_closed_helpers C.jet_secp_scalar_overflow_numeric C.jet_secp_shift64_executor C.jet_secp_statement_prefix.
Require C.jets_secp.
Import ListNotations Ctypes Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_scalar_set_flag.
Local Opaque secp_ge scalar_flag_state scalar_flag_initial scalar_set_state xstmt.
Theorem eval_scalar_set_b32_flag_frame bytes b bb ofs bf m :
 length bytes=32%nat ->Forall (fun z=>0<=z<=255) bytes ->
 b<>bb ->bf<>b ->bf<>bb ->0<=ofs ->ofs+32<=Ptrofs.max_unsigned ->
 Mem.range_perm m b 0 32 Cur Freeable ->Mem.range_perm m bb ofs (ofs+32) Cur Readable ->
 Mem.range_perm m bf 0 4 Cur Freeable ->
 (forall i,(i<32)%nat ->Mem.load Mint8unsigned m bb (ofs+Z.of_nat i)=Some (Vint (Int.repr (nth i bytes 0)))) ->
 let limbs:=scalar_set_limb (byte_rho bytes) (lay [(b,0);(bb,ofs)]) in exists mf,
 Clight2.eval_funcall secp_ge m (Internal jets_secp.f_secp256k1_scalar_set_b32)
  [Vptr b Ptrofs.zero;Vptr bb (Ptrofs.repr ofs);Vptr bf Ptrofs.zero] E0 mf Vundef /\
 (forall i,(i<4)%nat ->Mem.load Mint64 mf b (8*Z.of_nat i)=Some (Vlong (limbs i))) /\
 Mem.load Mint32 mf bf 0=Some (Vint (b2i (Z.leb canonical_group_order (be_val bytes)))) /\
 scalar_limb_value limbs=be_val bytes mod canonical_group_order /\keeps_permissions m mf /\
 lframe (fun block pos=>~foot [(b,0);(bb,ofs);(bf,0)]
  (map rshape scalar_flag_regs) block pos /\block<>bf) m mf /\ readonly_preserved m mf.
Proof.
 intros Length Bytes Separate FB FS Lo Hi Free Read Flag Source limbs.
 set (rho:=byte_rho bytes);set (layout:=[(b,0);(bb,ofs);(bf,0)]).
 assert (Initial:rep rho layout scalar_flag_regs m).
 { apply scalar_flag_initial_storage;assumption. }
 pose proof scalar_flag_run_eq as Run;unfold scalar_flag_run in Run.
 destruct (xstmt_shift64_normal 1000 scalar_flag_initial scalar_set_prefix scalar_flag_state
  rho layout m (scalar_flag_concrete_temps rho layout) Run Initial (scalar_flag_tmatch rho layout)) as
  (le & mp & Prefix & Final & Temps & Shape & Frame).
 assert (Prefix2:rep rho [(b,0);(bb,ofs)] (sregs scalar_set_state) mp).
 { rewrite scalar_flag_output_shape in Final.
   exact (rep_prefix rho [(b,0);(bb,ofs)] [(bf,0)] (sregs scalar_set_state) [scalar_flag_region]
    mp Final eq_refl). }
 destruct (rep_free_region rho layout (sregs scalar_flag_state) mp 2 4 Final
  ltac:(rewrite scalar_flag_output_shape,scalar_set_storage_regions;cbn [app length];lia)
  ltac:(rewrite scalar_flag_output_shape,scalar_set_storage_regions;reflexivity)) as [FlagBase FlagOwned].
 assert (Pointer:le!jets_secp._overflow=Some (Vptr bf Ptrofs.zero)).
 { exact (Temps jets_secp._overflow (XP 2 0) scalar_flag_pointer). }
 assert (Over:le!jets_secp._over=Some (Vint (b2i (Z.leb canonical_group_order (be_val bytes))))).
 { pose proof (Temps jets_secp._over scalar_set_flag scalar_flag_over) as Temp.
   rewrite scalar_set_actual_flag in Temp;unfold rho in Temp.
   rewrite scalar_set_raw_input_value in Temp by assumption;exact Temp. }
 assert (Access:Mem.valid_access mp Mint32 bf 0 Writable).
 { split;[intros pos Range;eapply Mem.perm_implies;[apply FlagOwned;exact Range|constructor]|exists 0;reflexivity]. }
 destruct (Mem.valid_access_store mp Mint32 bf 0 (Vint (b2i (Z.leb canonical_group_order (be_val bytes)))) Access)
  as (mf & Store).
 assert (Present:Cop.bool_val (Vptr bf Ptrofs.zero) (tptr tint) mp=Some true).
 { change ((if Mem.weak_valid_pointer mp bf 0 then Some true else None)=Some true).
   assert (Valid:Mem.weak_valid_pointer mp bf 0=true).
   { apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm.
     eapply Mem.perm_implies;[exact (FlagOwned 0 ltac:(lia))|apply perm_any_N]. }
   rewrite Valid;reflexivity. }
 assert (Call:Clight2.eval_funcall secp_ge m (Internal jets_secp.f_secp256k1_scalar_set_b32)
  [Vptr b Ptrofs.zero;Vptr bb (Ptrofs.repr ofs);Vptr bf Ptrofs.zero] E0 mf Vundef).
 { assert (Args:map (den rho (lay layout)) [XP 0 0;XP 1 0;XP 2 0]=
    [Vptr b Ptrofs.zero;Vptr bb (Ptrofs.repr ofs);Vptr bf Ptrofs.zero]).
   { cbn [map den];unfold layout;cbn [lay nth fst snd blk bas];rewrite !Z.add_0_r;reflexivity. }
   rewrite <-Args;eapply eval_funcall_internal with (e:=empty_env)
    (le1:=scalar_flag_concrete_temps rho layout) (le2:=le) (m1:=m) (m2:=mf) (out:=Out_normal).
   - apply scalar_flag_entry.
   - rewrite scalar_set_body_exact;eapply exec_statement_prefix_then_last;[exact Prefix|].
     rewrite scalar_set_suffix_exact;eapply exec_Sifthenelse with (b:=true);
      [apply eval_Etempvar;exact Pointer|exact Present|].
     eapply exec_Sassign_value with (b:=bf) (ofs:=Ptrofs.zero)
      (v2:=Vint (b2i (Z.leb canonical_group_order (be_val bytes))))
      (v:=Vint (b2i (Z.leb canonical_group_order (be_val bytes)))).
     + apply eval_Ederef;apply eval_Etempvar;exact Pointer.
     + apply eval_Etempvar;exact Over.
     + reflexivity.
     + apply assign_loc_value with (chunk:=Mint32);[reflexivity|exact Store].
   - reflexivity.
   - reflexivity. }
 assert (StoreFrame:lframe (fun block _=>block<>bf) mp mf).
 { apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact Store|intros;congruence]. }
 exists mf;split;[exact Call|];split.
 - intros i Index;erewrite Mem.load_store_other;[exact (scalar_set_storage_loads _ _ _ Prefix2 i Index)|exact Store|left;congruence].
 - split;[exact (Mem.load_store_same _ _ _ _ _ _ Store)|];split.
   + apply scalar_set_bytes_mod_group;assumption.
   + split.
     * eapply (proj2 (internal_exec_keeps_permissions secp_ge secp_closed_helpers secp_closed_helpers_ok));
        [exact Call|exact scalar_set_storage_allowed].
     * split.
       -- eapply lframe_trans.
          ++ eapply lframe_implies;[exact Frame|intros block pos Outside Old;exact (proj1 Outside)].
          ++ eapply lframe_implies;[exact StoreFrame|intros block pos [_ Other] Old;exact Other].
       -- eapply (proj2 (internal_exec_preserved secp_ge secp_closed_helpers secp_closed_helpers_ok));
           [exact Call|exact scalar_set_storage_allowed].
Qed.
Lemma scalar_flag_before_source b bb ofs bf pos:
 b<>bb ->bf<>bb ->pos<ofs ->
 ~foot [(b,0);(bb,ofs);(bf,0)] (map rshape scalar_flag_regs) bb pos /\bb<>bf.
Proof.
 intros Separate Flag Before;split;[|congruence].
 intros (r & shape & d & chunk & Region & Cell & Block & Range).
 destruct r as [|[|[|r]]].
 - change (bb=b) in Block;congruence.
 - cbn [scalar_flag_regs scalar_set_initial_regs app map nth_error rshape rcells rw rfree] in Region.
   injection Region as <-.
   apply in_map_iff in Cell as (c & Shape & Member).
   destruct (b32_byte_cells_in 32 0 0 c Member) as (i & Index & Eq);subst c.
   inversion Shape;subst d chunk.
   change (ofs+(0+Z.of_nat i)<=pos<ofs+(0+Z.of_nat i)+1) in Range;lia.
 - change (bb=bf) in Block;congruence.
 - destruct r;discriminate Region.
Qed.
