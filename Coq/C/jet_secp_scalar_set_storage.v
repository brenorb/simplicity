(** The original NULL-overflow scalar byte parser from concrete storage.
    Reuse its checked execution and numeric reduction without a frame reader. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_fe_b32 C.jet_secp_b32_exec C.jet_secp_linkage C.jet_secp_scalar_public_entry
 C.jet_secp_scalar_set_b32_exec C.jet_secp_scalar_set_shape C.jet_secp_scalar_set_bytes
 C.jet_secp_canonical_scalar C.jet_secp_scalar_overflow_numeric C.jet_secp_closed_helpers C.jet_clight_internal_frame
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Require C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Lemma scalar_set_storage_regions : sregs scalar_set_state =
 [mkreg (cells0 scalar_set_state) true None;
  mkreg (jet_secp_fe_b32.byte_cells 0 32 0) false None].
Proof. reflexivity. Qed.
Lemma scalar_set_storage_loads rho layout m :
 rep rho layout (sregs scalar_set_state) m ->forall i,(i<4)%nat ->
 Mem.load Mint64 m (blk layout 0) (bas layout 0+8*Z.of_nat i)=
  Some (Vlong (scalar_set_limb rho (lay layout) i)).
Proof.
 intro Repr;rewrite scalar_set_storage_regions in Repr.
 pose proof (rep_region rho layout _ m 0 _ Repr eq_refl) as Region.
 intros i Index;destruct i as [|[|[|[|i]]]];try lia;
 unfold scalar_set_limb;cbn [nth];
 match goal with |- Mem.load _ _ _ (_+?ofs)=Some (Vlong (il (den _ _ ?x))) =>
  pose proof (region_load rho layout m 0
   (mkreg (cells0 scalar_set_state) true None) ofs Mint64 x Region
   ltac:(cbn [rcells];rewrite scalar_set_output_shape;cbn;auto)) as Load;
  rewrite (den_KL rho (lay layout) x eq_refl) in Load;exact Load end.
Qed.
Lemma scalar_set_storage_initial bytes b bb ofs m :
 length bytes=32%nat ->Forall (fun z=>0<=z<=255) bytes ->
 b<>bb -> 0<=ofs ->ofs+32<=Ptrofs.max_unsigned ->
 Mem.range_perm m b 0 32 Cur Freeable ->Mem.range_perm m bb ofs (ofs+32) Cur Readable ->
 (forall i,(i<32)%nat ->Mem.load Mint8unsigned m bb (ofs+Z.of_nat i)=Some (Vint (Int.repr (nth i bytes 0)))) ->
 rep (byte_rho bytes) [(b,0);(bb,ofs)] scalar_set_initial_regs m.
Proof.
 intros Length Bytes Separate Lo Hi Free SourcePerm Source.
 unfold scalar_set_initial_regs;apply two_region_rep_separate;[reflexivity|exact Separate| |].
 - pose proof (scalar_undefined_owned_from_storage (byte_rho bytes) [(b,0);(bb,ofs)] m eq_refl Free)
    as (Base & Valid & Sorted & Cells & Owned).
   split;[exact Base|];split;[exact Valid|];split;[exact Sorted|];split;[exact Cells|exact I].
 - eapply region_b32_bytes_from_storage;[exact Length|exact Bytes|exact Lo|exact Hi|exact SourcePerm|exact Source].
Qed.
Lemma scalar_set_storage_allowed : allowed_call secp_closed_helpers (Internal jets_secp.f_secp256k1_scalar_set_b32).
Proof. exists jets_secp._secp256k1_scalar_set_b32,jets_secp.f_secp256k1_scalar_set_b32;split;[vm_compute;reflexivity|reflexivity]. Qed.

Lemma scalar_set_storage_foot_outside b bb ofs block pos :
 block<>b /\block<>bb ->
 ~foot [(b,0);(bb,ofs)] (map rshape scalar_set_initial_regs) block pos.
Proof.
 intros [Left Right] (r & shape & d & chunk & Entry & Member & Block & Range).
 assert (Index:(r<2)%nat).
 { change (r<length (map rshape scalar_set_initial_regs))%nat.
   apply nth_error_Some;congruence. }
 destruct r as [|[|r]];try lia.
 - change (block=b) in Block;contradiction.
 - change (block=bb) in Block;contradiction.
Qed.

(** Original setter, with NULL overflow output, from concrete byte/storage
    premises. The value bridge is the existing checked parser/reduction result. *)
Theorem eval_scalar_set_b32_storage bytes b bb ofs m :
 length bytes=32%nat ->Forall (fun z=>0<=z<=255) bytes ->
 b<>bb ->0<=ofs ->ofs+32<=Ptrofs.max_unsigned ->
 Mem.range_perm m b 0 32 Cur Freeable ->Mem.range_perm m bb ofs (ofs+32) Cur Readable ->
 (forall i,(i<32)%nat ->Mem.load Mint8unsigned m bb (ofs+Z.of_nat i)=Some (Vint (Int.repr (nth i bytes 0)))) ->
 let limbs:=scalar_set_limb (byte_rho bytes) (lay [(b,0);(bb,ofs)]) in exists mf,
 Clight2.eval_funcall secp_ge m (Internal jets_secp.f_secp256k1_scalar_set_b32)
  [Vptr b Ptrofs.zero;Vptr bb (Ptrofs.repr ofs);Vlong Int64.zero] E0 mf Vundef /\
 (forall i,(i<4)%nat ->Mem.load Mint64 mf b (8*Z.of_nat i)=Some (Vlong (limbs i))) /\
 scalar_limb_value limbs=be_val bytes mod canonical_group_order /\
 keeps_permissions m mf /\
 lframe (fun block _=>block<>b /\block<>bb) m mf /\
 readonly_preserved m mf.
Proof.
 intros Length Bytes Separate Lo Hi Free SourcePerm Source limbs.
 pose proof (scalar_set_storage_initial bytes b bb ofs m Length Bytes Separate Lo Hi Free SourcePerm Source) as Initial.
 destruct (eval_scalar_set_b32_from_initial_regions (byte_rho bytes) [(b,0);(bb,ofs)] m Initial) as
  (mf & Call & Final & Shape & Frame).
 change (Clight2.eval_funcall secp_ge m (Internal jets_secp.f_secp256k1_scalar_set_b32)
  [Vptr b Ptrofs.zero;Vptr bb (Ptrofs.repr ofs);Vlong Int64.zero] E0 mf Vundef) in Call.
 exists mf;split;[exact Call|];split.
 - intros i Index;exact (scalar_set_storage_loads _ _ _ Final i Index).
 - split;[apply scalar_set_bytes_mod_group;assumption|];split.
   + eapply (proj2 (internal_exec_keeps_permissions secp_ge secp_closed_helpers secp_closed_helpers_ok));
      [exact Call|exact scalar_set_storage_allowed].
   + split.
     * eapply lframe_implies;[exact Frame|intros block pos Outside Old;apply scalar_set_storage_foot_outside;exact Outside].
     * eapply (proj2 (internal_exec_preserved secp_ge secp_closed_helpers secp_closed_helpers_ok));
      [exact Call|exact scalar_set_storage_allowed].
Qed.
