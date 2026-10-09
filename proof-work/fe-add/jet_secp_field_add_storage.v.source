(** Memory representation produced by actual C addition, for writer reuse. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_field_add C.jet_secp_field_add_values.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition add_values rho : list int64 :=
  [add_value rho 0; add_value rho 1; add_value rho 2;
   add_value rho 3; add_value rho 4].

Lemma add_rep_field m b bs rho :
  rep rho [(b, 0);(bs,0)] (sregs field_add_state) m ->
  fe_at m b 0 (add_values rho) /\ Mem.range_perm m b 0 40 Cur Freeable.
Proof.
  intro HRep.
  pose proof (rep_region rho [(b,0);(bs,0)] _ m 0 _ HRep eq_refl) as HRegion.
  destruct HRegion as (_ & _ & _ & HCells & HStorage).
  destruct HStorage as (_ & _ & HFree & _).
  change (Mem.range_perm m b 0 40 Cur Freeable) in HFree.
  pose proof (proj1 (Forall_forall _ _) HCells _
    (add_cell_present 4 ltac:(lia))) as HLast.
  destruct HLast as (HMax & _).
  change (40 <= Ptrofs.max_unsigned) in HMax.
  split; [|exact HFree].
  unfold fe_at. split; [lia|]. split; [exists 0; lia|].
  split; [exact HMax|]. split; [apply freeable_range_writable; exact HFree|].
  intros i x Hi.
  assert (HI : (i < 5)%nat).
  { assert (HN : nth_error (add_values rho) i <> None) by (rewrite Hi; discriminate).
    apply nth_error_Some in HN. exact HN. }
  pose proof (field_add_rep_loads m [(b,0);(bs,0)] rho HRep i HI) as HL.
  change (Mem.load Mint64 m b (0 + 8 * Z.of_nat i) =
    Some (Vlong (add_value rho i))) in HL.
  assert (HX : x = add_value rho i).
  { do 5 (destruct i as [|i]; [inversion Hi; reflexivity|]). lia. }
  rewrite HX. exact HL.
Qed.

Theorem eval_field_add_to_field m b bs rho :
  rep rho [(b,0);(bs,0)] field_add_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
      [Vptr b Ptrofs.zero; Vptr bs Ptrofs.zero] E0 mf Vundef /\
    fe_at mf b 0 (add_values rho) /\
    Mem.range_perm mf b 0 40 Cur Freeable /\
    Mem.range_perm mf bs 0 40 Cur Freeable /\
    lframe (fun b' pos => ~ foot [(b,0);(bs,0)] (map rshape field_add_initial_regs) b' pos) m mf.
Proof.
  intro HRep.
  destruct (eval_field_add_from_owned_region m [(b,0);(bs,0)] rho HRep)
    as (mf & HCall & HFinal & HShape & HFrame).
  destruct (add_rep_field mf b bs rho HFinal) as [HField HFree].
  pose proof (rep_free_region rho [(b,0);(bs,0)] (sregs field_add_state) mf
    1%nat 40 HFinal ltac:(cbn; lia) eq_refl) as [_ HFreeSource].
  change (Mem.range_perm mf bs 0 40 Cur Freeable) in HFreeSource.
  exists mf. split; [exact HCall|]. split; [exact HField|].
  split; [exact HFree|]. split; assumption.
Qed.
Print Assumptions eval_field_add_to_field.
