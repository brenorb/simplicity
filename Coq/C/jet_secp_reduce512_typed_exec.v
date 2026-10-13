(** Actual second-stage Clight execution, not an assumed phase call. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_compact_stmt_shift64 C.jet_secp_reduce512_typed_stage
  C.jet_secp_reduce512_typed_atomic C.jet_secp_reduce512_symbolic
  C.jet_secp_reduce512_wide C.jet_secp_scalar_mul512_symbolic.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Section TYPED.
Variable digits : nat -> int64.
Variable m6 : int.
Lemma typed_stage_raw_temps :
  (stemps (reduce512_typed_stage_state digits m6))!_p0 = Some (sc_lo (stage_sy0 digits)) /\
  (stemps (reduce512_typed_stage_state digits m6))!_p1 = Some (sc_lo (stage_sy1 digits)) /\
  (stemps (reduce512_typed_stage_state digits m6))!_p2 = Some (sc_lo (stage_sy2 digits m6)) /\
  (stemps (reduce512_typed_stage_state digits m6))!_p3 = Some (sc_lo (stage_sy3 digits m6)) /\
  (stemps (reduce512_typed_stage_state digits m6))!_p4 =
    Some (XL2I (XLb Badd (sc_hi (stage_sy3 digits m6)) (stage_sy_m6 m6))).
Proof. Timeout 10 (repeat split; reflexivity). Qed.
Local Opaque reduce512_typed_stage_state reduce512_allocated reduce512_typed_stage.
Theorem exec_typed_second_stage rho beta e le m :
  rep rho beta (sregs (reduce512_typed_stage_initial digits m6)) m ->
  tmatch rho beta (reduce512_typed_stage_temps digits m6) le ->
  ematch beta (snd reduce512_allocated) e ->
  exists le' mf,
    Clight2.exec_stmt secp_ge e le m reduce512_typed_stage E0 le' mf Out_normal /\
    rep rho beta (sregs (reduce512_typed_stage_state digits m6)) mf /\
    le'!_p0 = Some (Vlong (wlo (stage_ma0 digits))) /\
    le'!_p1 = Some (Vlong (wlo (stage_ma1 digits))) /\
    le'!_p2 = Some (Vlong (wlo (stage_ma2 digits m6))) /\
    le'!_p3 = Some (Vlong (wlo (stage_ma3 digits m6))) /\
    le'!_p4 = Some (Vint (Int64.loword
      (Int64.add (whi (stage_ma3 digits m6)) (stage_ma_m6 m6)))) /\
    tmatch rho beta (stemps (reduce512_typed_stage_state digits m6)) le' /\
    lframe (fun b ofs => ~ foot beta
      (map rshape (sregs (reduce512_typed_stage_initial digits m6))) b ofs) m mf.
Proof.
  intros HR HT HE.
  destruct (compact_stmt_shift64_normal 300 (snd reduce512_allocated)
    (reduce512_typed_stage_initial digits m6) reduce512_typed_stage
    (reduce512_typed_stage_state digits m6) (reduce512_typed_stage_run_eq digits m6)
    rho beta e le m HR HT HE) as (le' & mf & Hex & Hrep & Htm & Hshape & Hframe).
  destruct typed_stage_raw_temps as (S0 & S1 & S2 & S3 & S4).
  destruct (stage_columns_rep digits m6 rho (lay beta)) as [[D0 _] [[D1 _] [[D2 _] [D3 [DH _]]]]].
  pose proof (Htm _ _ S0) as L0; rewrite D0 in L0.
  pose proof (Htm _ _ S1) as L1; rewrite D1 in L1.
  pose proof (Htm _ _ S2) as L2; rewrite D2 in L2.
  pose proof (Htm _ _ S3) as L3; rewrite D3 in L3.
  pose proof (Htm _ _ S4) as L4.
  assert (DS : den rho (lay beta) (XLb Badd (sc_hi (stage_sy3 digits m6)) (stage_sy_m6 m6)) =
    Vlong (Int64.add (whi (stage_ma3 digits m6)) (stage_ma_m6 m6)))
    by (apply column_ladd_den; [exact DH|apply stage_m6_den]).
  change (le'!_p4 = Some (Vint (Int64.loword (il
    (den rho (lay beta) (XLb Badd (sc_hi (stage_sy3 digits m6)) (stage_sy_m6 m6))))))) in L4.
  rewrite DS in L4.
  exists le',mf; exact (conj Hex (conj Hrep (conj L0 (conj L1
    (conj L2 (conj L3 (conj L4 (conj Htm Hframe)))))))).
Qed.
End TYPED.
