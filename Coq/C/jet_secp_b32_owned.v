(** Complete storage and permission results of the original field serializer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Memory Values Ctypes Clight ClightBigstep Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_rep
 C.jets_secp C.jet_secp_linkage C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_secp_b32_exec C.jet_secp_b32_full
 C.jet_read8s_layout C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve
 C.jet_clight_internal_permissions.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Lemma get_b32_source_region:
 nth_error (sregs gb_leaf) 1=Some (mkreg (u64_cells 0 (vars5 0)) false None).
Proof. reflexivity. Qed.
Lemma get_b32_closed:
 closed_stmtb secp_closed_helpers (fn_body f_secp256k1_fe_get_b32)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma get_b32_allowed:allowed_call secp_closed_helpers (Internal f_secp256k1_fe_get_b32).
Proof. exists _secp256k1_fe_get_b32,f_secp256k1_fe_get_b32;split;vm_compute;reflexivity. Qed.
Lemma get_b32_foot_bounds bout offset bin base b pos:
 foot [(bout,offset);(bin,base)]
  (map rshape [mkreg (jet_secp_fe_b32.byte_undef 0 32) true None;
   mkreg (u64_cells 0 (vars5 0)) false None]) b pos ->
 (b=bout /\offset<=pos<offset+32) \/(b=bin /\base<=pos<base+40).
Proof.
 intros (r & sh & d & ch & Region & Cell & Block & Range).
 destruct r as [|[|r]].
 - left;split;[exact Block|].
   cbn [map nth_error rshape rcells rw rfree] in Region;injection Region as <-.
   apply in_map_iff in Cell as (c & Shape & Member).
   destruct (b32_undefined_cells_in 32 0 c Member) as (i & Index & Eq);subst c.
   inversion Shape;subst d ch.
   cbn [bas lay nth snd size_chunk] in Range;lia.
 - right;split;[exact Block|].
   cbn [map nth_error rshape rcells rw rfree] in Region;injection Region as <-.
   apply in_map_iff in Cell as (c & Shape & Member).
   destruct (u64_cells_In (vars5 0) 0 c Member) as (i & x & Index & Eq);subst c.
   assert (Bound:(i<5)%nat).
   { assert (Small:(i<length (vars5 0))%nat) by (apply nth_error_Some;congruence);exact Small. }
   inversion Shape;subst d ch.
   change (base+8*Z.of_nat i<=pos<base+8*Z.of_nat i+8) in Range;lia.
 - destruct r;discriminate Region.
Qed.
Theorem get_b32_final_source value b offset bf base m mf:
 fe_at m bf base (map Int64.repr (fe_limbs_of value)) ->keeps_permissions m mf ->
 rep (limb_rho value) [(b,offset);(bf,base)] (sregs gb_leaf) mf ->
 fe_at mf bf base (map Int64.repr (fe_limbs_of value)).
Proof.
 intros (Base & Align & Max & Perm & Loads) Keep Final.
 pose proof (rep_region _ _ _ _ _ _ Final get_b32_source_region) as Source.
 split;[exact Base|];split;[exact Align|];split;[exact Max|];split.
 - intros pos Range;apply Keep,Perm;exact Range.
 - intros i w Nth.
   assert (Bound:(i<5)%nat).
   { assert (Index:(i<length (map Int64.repr (fe_limbs_of value)))%nat)
     by (apply nth_error_Some;congruence).
     change (i<5)%nat in Index;exact Index. }
   assert (Var:nth_error (vars5 0) i=Some (XLv i)).
   { clear -Bound;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity. }
   pose proof (region_load _ _ _ _ _ _ _ _ Source (u64_cells_nth _ 0 i (XLv i) Var)) as Load.
   cbn [blk bas lay nth fst snd den] in Load.
   apply nth_error_nth with (d:=Int64.zero) in Nth.
   change (nth i (map Int64.repr (fe_limbs_of value)) (Int64.repr 0)=w) in Nth.
   rewrite map_nth in Nth;subst w;exact Load.
Qed.
Theorem eval_fe_get_b32_owned m b offset bf base value:
 0<=value<2^256 ->0<=offset ->offset+32<=Ptrofs.max_unsigned ->
 Mem.range_perm m b offset (offset+32) Cur Freeable ->
 fe_at m bf base (map Int64.repr (fe_limbs_of value)) ->b<>bf ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_get_b32)
  [Vptr b (Ptrofs.repr offset);Vptr bf (Ptrofs.repr base)] E0 mf Vundef /\
 uint8_array_at mf b offset (map Int.repr (be_bytes value)) /\
 fe_at mf bf base (map Int64.repr (fe_limbs_of value)) /\
 keeps_permissions m mf /\
 lframe (fun block pos=>~foot [(b,offset);(bf,base)]
  (map rshape [mkreg (jet_secp_fe_b32.byte_undef 0 32) true None;
   mkreg (u64_cells 0 (vars5 0)) false None]) block pos) m mf /\readonly_preserved m mf.
Proof.
 intros Range Base Max Free Input Separate.
 destruct (eval_fe_get_b32_from_storage_full m b offset bf base value Range Base Max
  ltac:(intros pos Pos;eapply Mem.perm_implies;[apply Free;exact Pos|constructor]) Input Separate)
 as (mf & Call & Bytes & Frame & Final).
 pose proof (proj2 (internal_exec_keeps_permissions _ _ secp_closed_helpers_ok)
  _ _ _ _ _ _ Call get_b32_allowed) as Keep.
 exists mf;split;[exact Call|];split;[exact Bytes|];split.
 - exact (get_b32_final_source value b offset bf base m mf Input Keep Final).
 - split;[exact Keep|];split;[exact Frame|].
   eapply secp_closed_function_preserved;[exact get_b32_closed|reflexivity|exact Call].
Qed.
