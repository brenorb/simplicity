(** Build the existing multiplication input representation from one owned
    scalar and one readable scalar. No execution or product is a premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_sx_u64_transport
 C.jet_secp_local_regions C.jet_secp_b32_exec C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_writer_run C.jet_secp_scalar_writer_storage C.jet_secp_scalar_mul_reader_bridge
 C.jet_secp_scalar_mul_borrowed_alloc C.jet_secp_u128_shift64_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem scalar_borrowed_inputs_from_storage a b m ba bb :
 scalar_at m ba 0 (map Int64.repr (scalar_limbs_of a)) ->
 scalar_at m bb 0 (map Int64.repr (scalar_limbs_of b)) ->
 Mem.range_perm m ba 0 32 Cur Freeable -> ba<>bb ->
 rep (scalar_mul_reader_rho a b) [(ba,0);(bb,0)] scalar_mul_borrowed_inputs m.
Proof.
 intros A B Owned Separate.
 pose proof (scalar_writer_initial_rep_from_storage a m ba A Owned) as Input.
 apply two_region_rep_separate;[reflexivity|exact Separate| |].
 - eapply region_u64_transport with (rho:=scalar_limb_rho a) (beta:=[(ba,0)]) (r:=0%nat)
   (xs:=[XLv 0;XLv 1;XLv 2;XLv 3]) (ys:=[XLv 0;XLv 1;XLv 2;XLv 3]) (w:=true) (owned:=Some 32);
   try reflexivity;exact (rep_region _ _ _ _ 0 _ Input eq_refl).
 - eapply region_u64_transport with (rho:=scalar_limb_rho b) (beta:=[(bb,0)]) (r:=0%nat)
   (xs:=[XLv 0;XLv 1;XLv 2;XLv 3]) (ys:=[XLv 4;XLv 5;XLv 6;XLv 7]) (w:=false) (owned:=None);
   try reflexivity;apply scalar_region_from_storage;exact B.
Qed.

Lemma scalar_borrowed_inputs_source a b m ba bb :
 rep (scalar_mul_reader_rho a b) [(ba,0);(bb,0)] scalar_mul_borrowed_inputs m ->
 scalar_at m ba 0 (map Int64.repr (scalar_limbs_of a)) /\ Mem.range_perm m ba 0 32 Cur Freeable.
Proof.
 intro Rep;destruct (rep_free_region _ _ _ _ 0 32 Rep ltac:(cbn;lia) eq_refl) as (_ & Free).
 split;[|exact Free];unfold scalar_at;split;[reflexivity|];split;[lia|];split;[exists 0;lia|];split;
 [change (32<=18446744073709551615);lia|];split.
 - intros pos Range;eapply Mem.perm_implies;[apply Free;exact Range|constructor].
 - intros i word Nth;destruct i as [|[|[|[|i]]]];try (destruct i;discriminate);
   injection Nth as <-.
   all: first
    [ exact (xload_u64_defined_sound _ _ _ _ 0 0 (XLv 0) Rep eq_refl)
    | exact (xload_u64_defined_sound _ _ _ _ 0 8 (XLv 1) Rep eq_refl)
    | exact (xload_u64_defined_sound _ _ _ _ 0 16 (XLv 2) Rep eq_refl)
    | exact (xload_u64_defined_sound _ _ _ _ 0 24 (XLv 3) Rep eq_refl) ].
Qed.
