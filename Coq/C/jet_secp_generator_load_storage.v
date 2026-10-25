(** Complete original generator_load from caller byte storage. Both halves
    may encode any 256-bit integer, including values greater than p. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep
  C.jet_sx_rename C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_b32
  C.jet_secp_b32_exec C.jet_secp_affine_storage C.jet_secp_generator_load C.jet_secp_generator_load_values
  C.jet_secp_owned_slice_fields C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_curve_frame
  C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma generator_byte_member count : forall ofs start i,(i<count)%nat ->
  In (mkcell (ofs+Z.of_nat i) Mint8unsigned (Some (XL2I (XLv (start+i)))))
    (C.jet_secp_fe_b32.byte_cells ofs count start).
Proof.
  induction count as [|count IH];intros ofs start i Index;[lia|].
  destruct i as [|i].
  - rewrite Z.add_0_r,Nat.add_0_r;left;reflexivity.
  - right;replace (ofs+Z.of_nat (S i)) with (ofs+1+Z.of_nat i) by lia.
    replace (start+S i)%nat with (S start+i)%nat by lia;apply IH;lia.
Qed.
Lemma generator_point_initial rho beta m r : bas beta r=0 ->
  Mem.range_perm m (blk beta r) 0 88 Cur Freeable -> region_ok rho beta m r affine_storage_undef.
Proof.
  intros Base Free;unfold region_ok;cbn [affine_storage_undef rcells rw rfree];rewrite Base.
  split;[lia|];split;[eapply Mem.perm_valid_block;apply (Free 0);lia|];split;[reflexivity|];split.
  - apply Forall_forall;intros c Member;cbn in Member.
    repeat match goal with Same:_ \/ _ |- _=>destruct Same as [<- | Same] end;try contradiction.
    all: apply writable_undefined_cell;rewrite Base;cbn [size_chunk align_chunk].
    all: try (change Ptrofs.max_unsigned with 18446744073709551615;lia).
    all: try (apply Z.mod_divide;[lia|reflexivity]).
    all: intros pos Range;eapply Mem.perm_implies;[apply Free;lia|constructor].
  - split;[reflexivity|];split;[reflexivity|];split;[exact Free|].
    apply Forall_forall;intros c Member;cbn in Member.
    repeat match goal with Same:_ \/ _ |- _=>destruct Same as [<- | Same] end;try contradiction.
    all: cbn [cofs cchunk size_chunk];lia.
Qed.
Lemma generator_load_initial xs ys m bp bg : length xs=32%nat -> length ys=32%nat ->
  Forall (fun x=>0<=x<=255) xs -> Forall (fun y=>0<=y<=255) ys -> bp<>bg ->
  Mem.range_perm m bp 0 88 Cur Freeable -> Mem.range_perm m bg 0 64 Cur Freeable ->
  (forall i,(i<64)%nat -> Mem.load Mint8unsigned m bg (Z.of_nat i)=Some (Vint (Int.repr (nth i (xs++ys) 0)))) ->
  rep (generator_byte_pair xs ys) [(bp,0);(bg,0)] generator_load_regs m.
Proof.
  intros LX LY BX BY Sep FP FG Loads.
  assert (Bytes:Forall (fun x=>0<=x<=255) (xs++ys)) by (apply Forall_app;split;assumption).
  apply two_region_rep_separate;[reflexivity|exact Sep|apply generator_point_initial;[reflexivity|exact FP]|].
  unfold region_ok;cbn [generator_load_source rcells rw rfree blk bas lay nth fst snd].
  split;[lia|];split;[eapply Mem.perm_valid_block;apply (FG 0);lia|];split.
  - apply byte_cells_sorted;lia.
  - split.
    + apply Forall_forall;intros c Member.
      destruct (b32_byte_cells_in 64 0 0 c Member) as (i & Index & ->).
      unfold cell_ok;cbn [cofs cchunk cval rw size_chunk align_chunk blk bas lay nth fst snd].
      rewrite Nat.add_0_l,!Z.add_0_l.
      split;[change Ptrofs.max_unsigned with 18446744073709551615;lia|];split;[exists (Z.of_nat i);lia|];split.
      * intros pos Range;eapply Mem.perm_implies;[apply FG;lia|constructor].
      * intros expr Same;injection Same as <-;split;[|reflexivity].
        cbn [den il];rewrite generator_pair_as_bytes by exact LX.
        rewrite byte_loword_exact by exact Bytes;apply Loads;exact Index.
    + split;[reflexivity|];split;[reflexivity|];split;[exact FG|].
      apply Forall_forall;intros c Member.
      destruct (b32_byte_cells_in 64 0 0 c Member) as (i & Index & ->).
      cbn [cofs cchunk size_chunk];lia.
Qed.

Lemma generator_load_fields xs ys m bp bg : length xs=32%nat -> length ys=32%nat ->
  Forall (fun x=>0<=x<=255) xs -> Forall (fun y=>0<=y<=255) ys ->
  rep (generator_byte_pair xs ys) [(bp,0);(bg,0)] generator_load_out_regs m ->
  fe_at m bp 0 (map Int64.repr (fe_limbs_of (be_val xs))) /\
  fe_at m bp 40 (map Int64.repr (fe_limbs_of (be_val ys))) /\
  Mem.load Mint32 m bp 80=Some (Vint Int.zero) /\
  Mem.range_perm m bp 0 88 Cur Freeable /\ Mem.range_perm m bg 0 64 Cur Freeable /\
  (forall i,(i<64)%nat -> Mem.load Mint8unsigned m bg (Z.of_nat i)=Some (Vint (Int.repr (nth i (xs++ys) 0)))).
Proof.
  intros LX LY BX BY Rep.
  pose proof (rep_region _ _ _ m 0 _ Rep eq_refl) as R0.
  pose proof (rep_region _ _ _ m 1 _ Rep eq_refl) as R1.
  pose proof R0 as (_ & _ & _ & _ & _ & _ & FP & _).
  pose proof R1 as (_ & _ & _ & _ & _ & _ & FG & _).
  assert (X:fe_at m bp 0 (map Int64.repr (fe_limbs_of (be_val xs)))).
  { eapply owned_region_field_slice with (rho:=generator_byte_pair xs ys) (beta:=[(bp,0);(bg,0)])
      (r:=0%nat) (size:=88) (exprs:=generator_field_exprs).
    - exact R0.
    - lia.
    - exists 0;reflexivity.
    - lia.
    - change (88<=18446744073709551615);lia.
    - exact generator_field_length.
    - rewrite map_length;reflexivity.
    - intros c Member;unfold generator_load_cells;apply in_or_app;left;exact Member.
    - rewrite generator_pair_left;apply generator_field_den;assumption. }
  assert (Y:fe_at m bp 40 (map Int64.repr (fe_limbs_of (be_val ys)))).
  { eapply owned_region_field_slice with (rho:=generator_byte_pair xs ys) (beta:=[(bp,0);(bg,0)])
      (r:=0%nat) (size:=88) (exprs:=map (sx_rename (fun n=>(n+32)%nat)) generator_field_exprs).
    - exact R0.
    - lia.
    - exists 5;reflexivity.
    - lia.
    - change (88<=18446744073709551615);lia.
    - rewrite map_length;exact generator_field_length.
    - rewrite map_length;reflexivity.
    - intros c Member;unfold generator_load_cells;apply in_or_app;right;apply in_or_app;left;exact Member.
    - rewrite generator_pair_right;apply generator_field_den;assumption. }
  split;[exact X|];split;[exact Y|];split.
  - pose proof (region_load _ _ _ 0 _ 80 Mint32 (XIc Int.zero) R0) as Flag.
    apply Flag;unfold generator_load_cells;apply in_or_app;right;apply in_or_app;right;left;reflexivity.
  - split;[exact FP|];split;[exact FG|];intros i Index.
    pose proof (region_load _ _ _ 1 _ (Z.of_nat i) Mint8unsigned (XL2I (XLv i)) R1) as Load.
    assert (Member:In (mkcell (Z.of_nat i) Mint8unsigned (Some (XL2I (XLv i))))
      (C.jet_secp_fe_b32.byte_cells 0 64 0)).
    { change (In (mkcell (0+Z.of_nat i) Mint8unsigned (Some (XL2I (XLv (0+i)))))
        (C.jet_secp_fe_b32.byte_cells 0 64 0));apply generator_byte_member;exact Index. }
    specialize (Load Member);change (Mem.load Mint8unsigned m bg (Z.of_nat i)=
      Some (Vint (Int64.loword (generator_byte_pair xs ys i)))) in Load.
    rewrite generator_pair_as_bytes in Load by exact LX.
    rewrite byte_loword_exact in Load by (apply Forall_app;split;assumption);exact Load.
Qed.

Theorem eval_generator_load_from_storage xs ys m bp bg : length xs=32%nat -> length ys=32%nat ->
  Forall (fun x=>0<=x<=255) xs -> Forall (fun y=>0<=y<=255) ys -> bp<>bg ->
  Mem.range_perm m bp 0 88 Cur Freeable -> Mem.range_perm m bg 0 64 Cur Freeable ->
  (forall i,(i<64)%nat -> Mem.load Mint8unsigned m bg (Z.of_nat i)=Some (Vint (Int.repr (nth i (xs++ys) 0)))) ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_generator_load)
    [Vptr bp Ptrofs.zero;Vptr bg Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bp 0 (map Int64.repr (fe_limbs_of (be_val xs))) /\
  fe_at mf bp 40 (map Int64.repr (fe_limbs_of (be_val ys))) /\
  Mem.load Mint32 mf bp 80=Some (Vint Int.zero) /\
  Mem.range_perm mf bp 0 88 Cur Freeable /\ Mem.range_perm mf bg 0 64 Cur Freeable /\
  (forall i,(i<64)%nat -> Mem.load Mint8unsigned mf bg (Z.of_nat i)=Some (Vint (Int.repr (nth i (xs++ys) 0)))) /\
  lframe (fun b _=>b<>bp /\ b<>bg) m mf /\ readonly_preserved m mf.
Proof.
  intros LX LY BX BY Sep FP FG Bytes.
  destruct (eval_generator_load_symbolic (generator_byte_pair xs ys) [(bp,0);(bg,0)] m
    (generator_load_initial xs ys m bp bg LX LY BX BY Sep FP FG Bytes)) as (mf & Run & Rep & Frame).
  destruct (generator_load_fields xs ys mf bp bg LX LY BX BY Rep) as (X & Y & Flag & FPF & FGF & Source).
  exists mf;split;[exact Run|];split;[exact X|];split;[exact Y|];split;[exact Flag|];
    split;[exact FPF|];split;[exact FGF|];split;[exact Source|];split.
  - exact (curve_frame_two generator_load_regs bp bg m mf eq_refl Frame).
  - eapply (secp_closed_function_preserved f_secp256k1_generator_load);[vm_compute;reflexivity|reflexivity|exact Run].
Qed.
