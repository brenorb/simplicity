(** Reusable symbolic-store summary, justified by the actual original call. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_mem C.jet_sx_exec C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_u128_shift64_rep.
Require Import C.jet_secp_i128_shift62.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition i128_shift62_lo_sx lo hi := XLb Bor
  (XLsh Hshl (XLb Bmul (XLc Int64.one) hi) 2) (XLsh Hshru lo 62).
Definition i128_shift62_hi_sx hi := XLsh Hshr hi 62.

Lemma i128_shift62_lo_den rho layout lo hi :
  den rho layout (i128_shift62_lo_sx lo hi) =
    Vlong (i128_shift62_low (il (den rho layout lo)) (il (den rho layout hi))).
Proof. reflexivity. Qed.
Lemma i128_shift62_hi_den rho layout hi :
  den rho layout (i128_shift62_hi_sx hi) = Vlong (i128_shift62_high (il (den rho layout hi))).
Proof. reflexivity. Qed.

Theorem eval_i128_shift62_symbolic_stores rho layout regs m r reg lo hi regs1 regs2 :
  rep rho layout regs m -> nth_error regs r = Some reg -> rfree reg = Some 16 ->
  xload regs r 0 tulong = Some lo -> xload regs r 8 tulong = Some hi ->
  isk KL lo = true -> isk KL hi = true ->
  xstore regs r 0 Mint64 (i128_shift62_lo_sx lo hi) = Some regs1 ->
  xstore regs1 r 8 Mint64 (i128_shift62_hi_sx hi) = Some regs2 ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_i128_rshift)
      [Vptr (blk layout r) Ptrofs.zero; Vint (Int.repr 62)] E0 mf Vundef /\
    rep rho layout regs2 mf /\ map rshape regs2 = map rshape regs /\
    lframe (fun b ofs => ~ foot layout (map rshape regs) b ofs) m mf.
Proof.
  intros HRep HR HF HXL HXH HKL HKH HXS1 HXS2.
  pose proof (rep_owned_region_base_zero rho layout regs m r reg 16 HRep HR HF) as HB.
  pose proof (xload_u64_defined_sound rho layout regs m r 0 lo HRep HXL) as HL.
  pose proof (xload_u64_defined_sound rho layout regs m r 8 hi HRep HXH) as HH.
  destruct (xstore_sound rho layout regs m r 0 Mint64 (i128_shift62_lo_sx lo hi) regs1 HRep HXS1)
    as (m1 & HS1 & _ & HRep1 & HU1).
  destruct (xstore_sound rho layout regs1 m1 r 8 Mint64 (i128_shift62_hi_sx hi) regs2 HRep1 HXS2)
    as (mf & HS2 & _ & HRep2 & HU2).
  pose proof (xstore_shape regs r 0 Mint64 (i128_shift62_lo_sx lo hi) regs1 HXS1) as HShape1.
  pose proof (xstore_shape regs1 r 8 Mint64 (i128_shift62_hi_sx hi) regs2 HXS2) as HShape2.
  rewrite HB in HL, HH, HS1, HS2; cbn [Z.add] in HL, HH, HS1, HS2.
  rewrite (den_KL rho (lay layout) lo HKL) in HL.
  rewrite (den_KL rho (lay layout) hi HKH) in HH.
  rewrite i128_shift62_lo_den in HS1; rewrite i128_shift62_hi_den in HS2.
  exists mf; split.
  - eapply eval_funcall_internal with (e := empty_env)
      (le1 := i128_shift62_temps (blk layout r))
      (le2 := i128_shift62_final (i128_shift62_temps (blk layout r))
        (il (den rho (lay layout) lo)) (il (den rho (lay layout) hi)))
      (m1 := m) (m2 := mf) (out := Out_normal).
    + apply i128_shift62_entry.
    + apply exec_i128_shift62_body with (m1 := m1) (b := blk layout r); try assumption; reflexivity.
    + reflexivity.
    + reflexivity.
  - split; [exact HRep2|]; split; [congruence|].
    eapply lframe_trans.
    + apply lframe_unchanged; exact HU1.
    + rewrite <- HShape1; apply lframe_unchanged; exact HU2.
Qed.
