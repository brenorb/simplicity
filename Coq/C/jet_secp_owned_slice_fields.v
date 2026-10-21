(** Combine logical field slices inside one actual owned allocation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_secp_fe_nv C.jet_secp_local_regions.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma owned_region_append rho beta m r cs1 cs2 size :
  region_ok rho beta m r (mkreg cs1 true (Some size)) ->
  region_ok rho beta m r (mkreg cs2 true (Some size)) ->
  cells_sorted 0 (cs1++cs2)=true ->
  region_ok rho beta m r (mkreg (cs1++cs2) true (Some size)).
Proof.
  intros (HB & HV & HS1 & HC1 & H0 & HW & HF & HFit1)
    (_ & _ & HS2 & HC2 & _ & _ & _ & HFit2) HS.
  unfold region_ok;cbn [rcells rw rfree].
  split;[exact HB|]. split;[exact HV|]. split;[exact HS|].
  split;[apply Forall_app;split;assumption|].
  split;[exact H0|]. split;[reflexivity|]. split;[exact HF|].
  apply Forall_app;split;assumption.
Qed.

Lemma owned_region_field_slice rho beta m r cs size ofs exprs words :
  region_ok rho beta m r (mkreg cs true (Some size)) ->
  0<=ofs -> (8|ofs) -> ofs+40<=size -> size<=Ptrofs.max_unsigned ->
  length exprs=5%nat -> length words=5%nat ->
  (forall c, In c (u64_cells ofs exprs) -> In c cs) ->
  map (den rho (lay beta)) exprs=map Vlong words ->
  fe_at m (blk beta r) ofs words.
Proof.
  intros HR HO HA HFit HMax HElen HWlen HIn HD.
  pose proof HR as (_ & _ & _ & _ & HBase & _ & HFree & _).
  split;[exact HO|]. split;[exact HA|]. split;[lia|]. split.
  - apply freeable_range_writable;intros pos HP;apply HFree;lia.
  - intros i x HN.
    assert (HI : (i<5)%nat).
    { rewrite <- HWlen;apply nth_error_Some;rewrite HN;discriminate. }
    assert (HX : nth_error exprs i=Some (nth i exprs (XLv 0))).
    { apply nth_error_nth';rewrite HElen;exact HI. }
    pose proof (f_equal (fun xs => nth_error xs i) HD) as HV.
    cbv beta in HV;rewrite !nth_error_map,HX,HN in HV;injection HV as HV.
    pose proof (region_load _ _ _ _ _ _ _ _ HR (HIn _ (u64_cells_nth _ _ _ _ HX))) as HL.
    rewrite HBase,Z.add_0_l,HV in HL;exact HL.
Qed.
