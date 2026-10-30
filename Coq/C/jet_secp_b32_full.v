(** Additive serializer contracts exposing its existing symbolic final state. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_exec C.jet_sx_pure.
Require Import C.jet_sx_zval C.jet_sx_rep C.jet_sx_zrep.
Require Import C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_read8s_layout.
Import ListNotations Values Mem Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.


Require Import C.jet_secp_b32_exec.

Theorem eval_fe_get_b32_from_initial_regions_full m b offset bf base value :
  0 <= value < 2 ^ 256 ->
  rep (limb_rho value) [(b, offset); (bf, base)]
    [mkreg (jet_secp_fe_b32.byte_undef 0 32) true None;
     mkreg (u64_cells 0 (vars5 0)) false None] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_get_b32)
      [Vptr b (Ptrofs.repr offset); Vptr bf (Ptrofs.repr base)] E0 mf Vundef /\
    uint8_array_at mf b offset (map Int.repr (be_bytes value)) /\
    lframe (fun block pos =>
      ~ foot [(b, offset); (bf, base)]
        (map rshape [mkreg (jet_secp_fe_b32.byte_undef 0 32) true None;
                     mkreg (u64_cells 0 (vars5 0)) false None]) block pos) m mf /\
    rep (limb_rho value) [(b, offset); (bf, base)] (sregs gb_leaf) mf.
Proof.
  intros HValue HRep; set (rho := limb_rho value) in *.
  pose proof (limb_rho_bound value HValue) as Hb; fold rho in Hb.
  pose proof (gb_output_numeric value HValue) as HBytes; fold rho in HBytes.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 400 f_secp256k1_fe_get_b32
      [XP 0 0; XP 1 0]
      [mkreg (jet_secp_fe_b32.byte_undef 0 32) true None;
       mkreg (u64_cells 0 (vars5 0)) false None]
      5 _ gb_run_eq eq_refl rho [(b, offset); (bf, base)] m HRep)
    as [mf [result [HExec [HFinal [HRet [HShape HFrame]]]]]].
  cbn [rsel fst] in HFinal, HRet.
  rewrite gb_return_empty in HRet; subst result.
  change (map (den rho (lay [(b, offset); (bf, base)])) [XP 0 0; XP 1 0]) with
    [Vptr b (Ptrofs.repr (offset + 0)); Vptr bf (Ptrofs.repr (base + 0))] in HExec.
  rewrite !Z.add_0_r in HExec.
  exists mf; split; [exact HExec|]; split; [|split;[exact HFrame|exact HFinal]].
  destruct (rep_region rho [(b, offset); (bf, base)] _ mf 0 _ HFinal gb_output_region)
    as [_ [_ [_ [HCells _]]]].
  pose proof (zbyte_region_load rho limb52_bnd [(b, offset); (bf, base)] Hb mf 0 true
    (cells0 gb_leaf) 0 gb_output_checked HCells) as HLoad.
  cbn [blk bas lay nth fst snd] in HLoad.
  unfold uint8_array_at; rewrite <- HBytes.
  intros i byte HNth; rewrite nth_error_map in HNth.
  destruct (nth_error (zcells (zrho rho) (cells0 gb_leaf)) i) as [z|] eqn:HZ; [|discriminate].
  inversion HNth; subst byte.
  rewrite <- (HLoad i z HZ); f_equal; lia.
Qed.

Theorem eval_fe_get_b32_from_storage_full m b offset bf base value :
  0 <= value < 2 ^ 256 ->
  0 <= offset -> offset + 32 <= Ptrofs.max_unsigned ->
  Mem.range_perm m b offset (offset + 32) Cur Writable ->
  fe_at m bf base (map Int64.repr (fe_limbs_of value)) ->
  b <> bf ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_get_b32)
      [Vptr b (Ptrofs.repr offset); Vptr bf (Ptrofs.repr base)] E0 mf Vundef /\
    uint8_array_at mf b offset (map Int.repr (be_bytes value)) /\
    lframe (fun block pos =>
      ~ foot [(b, offset); (bf, base)]
        (map rshape [mkreg (jet_secp_fe_b32.byte_undef 0 32) true None;
                     mkreg (u64_cells 0 (vars5 0)) false None]) block pos) m mf /\
    rep (limb_rho value) [(b, offset); (bf, base)] (sregs gb_leaf) mf.
Proof.
 intros Range Base Max Perms Input Separate.
 apply eval_fe_get_b32_from_initial_regions_full;[exact Range|].
 apply get_b32_initial_rep_derived;assumption.
Qed.
