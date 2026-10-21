(** Reuse original private-field addition, exposing unchanged source words as
    well as the machine sum. No range bound is needed for actual execution. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem C.jet_secp_fe_nv
  C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions C.jet_secp_field_add C.jet_secp_field_add_initial
  C.jet_secp_field_add_storage C.jet_secp_field_add_scaled C.jet_secp_curve_tail_values C.jet_secp_curve_frame
  C.jet_secp_multiply_normalize_bridge C.jet_secp_owned_slice_fields.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem eval_field_sum_owned a b m ba bb : ba<>bb ->
  fe_at m ba 0 (words5 a) -> fe_at m bb 0 (words5 b) ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
    [Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef /\
  fe_at mf ba 0 (words5 (field_sum_words a b)) /\ fe_at mf bb 0 (words5 b) /\
  Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
  lframe (fun bx _=>bx<>ba /\ bx<>bb) m mf.
Proof.
  intros HSep HA HB HFA HFB.
  assert (HI : rep (curve_equal_rho a b) [(ba,0);(bb,0)] field_add_initial_regs m).
  { apply field_add_initial_from_owned_fields;[exact HSep| | |exact HFA|exact HFB].
    - rewrite curve_equal_first;exact HA.
    - rewrite curve_equal_second;exact HB. }
  destruct (eval_field_add_from_owned_region m [(ba,0);(bb,0)] (curve_equal_rho a b) HI)
    as (mf & HC & HR & HShape & Frame).
  destruct (add_rep_field mf ba bb (curve_equal_rho a b) HR) as (FO & FOF).
  rewrite field_sum_output in FO.
  pose proof (rep_region _ _ _ mf 1 _ HR eq_refl) as RS.
  assert (FB : fe_at mf bb 0 (words5 b)).
  { eapply owned_region_field_slice with (exprs:=vars5 6) (size:=40)
      (rho:=curve_equal_rho a b) (beta:=[(ba,0);(bb,0)]) (r:=1%nat);
      [exact RS|lia|exists 0;reflexivity|lia|change (40<=18446744073709551615);lia|
       reflexivity|reflexivity| |].
    - intros c HH;exact HH.
    - reflexivity. }
  pose proof RS as (_ & _ & _ & _ & _ & _ & FBF & _).
  exists mf;split;[exact HC|];split;[exact FO|];split;[exact FB|];
    split;[exact FOF|];split;[exact FBF|].
  exact (curve_frame_two field_add_initial_regs ba bb m mf eq_refl Frame).
Qed.
