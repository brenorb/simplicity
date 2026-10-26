(** Actual set_b32 on the generator's owned 40-byte field and 32-byte digest.
    Both return flags are retained; rejection still writes the raw limbs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep
  C.jet_sx_zval C.jet_sx_zrep C.jet_secp_linkage C.jets_secp C.jet_secp_fns
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_fe_b32 C.jet_secp_b32_exec C.jet_secp_local_regions
  C.jet_secp_generator_load C.jet_secp_generator_load_values C.jet_secp_generator_load_storage
  C.jet_secp_owned_slice_fields C.jet_secp_curve_frame C.jet_secp_closed_helpers C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition owned_b32_source := mkreg (C.jet_secp_fe_b32.byte_cells 0 32 0) true (Some 32).
Definition owned_b32_regs := [free_region fe_undef 40;owned_b32_source].
Definition owned_b32_run := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 400
  f_secp256k1_fe_set_b32 [XP 0 0;XP 1 0] owned_b32_regs [] 32.
Definition owned_b32_tree := Eval vm_compute in owned_b32_run.
Definition owned_b32_state := match owned_b32_tree with
  | Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end.
Definition owned_b32_out_regs :=
  [mkreg (u64_cells 0 generator_field_exprs) true (Some 40);owned_b32_source].
Lemma owned_b32_run_eq : owned_b32_run=Some (RDone owned_b32_state ONormal).
Proof. reflexivity. Qed.
Lemma owned_b32_return : (stemps owned_b32_state)!1%positive=Some sb_ret.
Proof. reflexivity. Qed.
Lemma owned_b32_shape : sregs owned_b32_state=owned_b32_out_regs.
Proof. reflexivity. Qed.

Lemma owned_b32_source_initial bytes beta m r : bas beta r=0 ->
  Forall (fun x=>0<=x<=255) bytes -> Mem.range_perm m (blk beta r) 0 32 Cur Freeable ->
  (forall i,(i<32)%nat -> Mem.load Mint8unsigned m (blk beta r) (Z.of_nat i)=
    Some (Vint (Int.repr (nth i bytes 0)))) ->
  region_ok (byte_rho bytes) beta m r owned_b32_source.
Proof.
  intros Base Bytes Free Loads;unfold region_ok;cbn [owned_b32_source rcells rw rfree];rewrite Base.
  split;[lia|];split;[eapply Mem.perm_valid_block;apply (Free 0);lia|];split.
  - apply byte_cells_sorted;lia.
  - split.
    + apply Forall_forall;intros c Member.
      destruct (b32_byte_cells_in 32 0 0 c Member) as (i & Index & ->).
      unfold cell_ok;cbn [cofs cchunk cval size_chunk align_chunk];rewrite Base,!Z.add_0_l,Nat.add_0_l.
      split;[change Ptrofs.max_unsigned with 18446744073709551615;lia|];split;[exists (Z.of_nat i);lia|];split.
      * intros pos Range;eapply Mem.perm_implies;[apply Free;lia|constructor].
      * intros expr Same;injection Same as <-;split;[|reflexivity].
        cbn [den il];rewrite byte_loword_exact by exact Bytes;apply Loads;exact Index.
    + split;[reflexivity|];split;[reflexivity|];split;[exact Free|].
      apply Forall_forall;intros c Member.
      destruct (b32_byte_cells_in 32 0 0 c Member) as (i & Index & ->).
      cbn [cofs cchunk size_chunk];lia.
Qed.
Lemma owned_b32_initial bytes m bt bb : bt<>bb -> Forall (fun x=>0<=x<=255) bytes ->
  Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bb 0 32 Cur Freeable ->
  (forall i,(i<32)%nat -> Mem.load Mint8unsigned m bb (Z.of_nat i)=Some (Vint (Int.repr (nth i bytes 0)))) ->
  rep (byte_rho bytes) [(bt,0);(bb,0)] owned_b32_regs m.
Proof.
  intros Sep Bytes FT FB Loads;apply two_region_rep_separate;[reflexivity|exact Sep| |].
  - apply region_with_freeable.
    + apply region_fe_undefined_from_storage;cbn [blk bas lay nth fst snd];
        [lia|exists 0;reflexivity|change (40<=18446744073709551615);lia|apply freeable_range_writable;exact FT].
    + reflexivity.
    + reflexivity.
    + exact FT.
    + apply fe_undef_storage_size.
  - apply owned_b32_source_initial;[reflexivity|exact Bytes|exact FB|exact Loads].
Qed.

Theorem eval_set_b32_owned bytes m bt bb : length bytes=32%nat -> Forall (fun x=>0<=x<=255) bytes -> bt<>bb ->
  Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bb 0 32 Cur Freeable ->
  (forall i,(i<32)%nat -> Mem.load Mint8unsigned m bb (Z.of_nat i)=Some (Vint (Int.repr (nth i bytes 0)))) ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_set_b32)
    [Vptr bt Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf (Vint (Int.repr (b2z (Z.ltb (be_val bytes) feP)))) /\
  fe_at mf bt 0 (map Int64.repr (fe_limbs_of (be_val bytes))) /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 32 Cur Freeable /\
  (forall i,(i<32)%nat -> Mem.load Mint8unsigned mf bb (Z.of_nat i)=Some (Vint (Int.repr (nth i bytes 0)))) /\
  lframe (fun b _=>b<>bt /\ b<>bb) m mf /\ readonly_preserved m mf.
Proof.
  intros Len Bytes Sep FT FB Loads.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 400 f_secp256k1_fe_set_b32
    [XP 0 0;XP 1 0] owned_b32_regs 32 _ owned_b32_run_eq eq_refl
    (byte_rho bytes) [(bt,0);(bb,0)] m (owned_b32_initial bytes m bt bb Sep Bytes FT FB Loads))
    as (mf & result & Call & Final & Return & Shape & Frame).
  cbn [rsel fst] in Final,Return;rewrite owned_b32_return in Return.
  change (result=den (byte_rho bytes) (lay [(bt,0);(bb,0)]) sb_ret) in Return.
  pose proof (proj1 (den_zval_int (byte_rho bytes) byte_bnd (lay [(bt,0);(bb,0)])
    (byte_rho_bound bytes Bytes) sb_ret 0 1 sb_return_checked sb_return_kind)) as Value.
  rewrite (proj2 (sb_output_numeric bytes Len Bytes)) in Value;rewrite Value in Return;subst result.
  change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_set_b32)
    [Vptr bt Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf
    (Vint (Int.repr (b2z (Z.ltb (be_val bytes) feP))))) in Call.
  rewrite owned_b32_shape in Final.
  pose proof (rep_region _ _ _ _ 0 _ Final eq_refl) as R0.
  pose proof (rep_region _ _ _ _ 1 _ Final eq_refl) as R1.
  pose proof R0 as (_ & _ & _ & _ & _ & _ & FTF & _).
  pose proof R1 as (_ & _ & _ & _ & _ & _ & FBF & _).
  assert (Field:fe_at mf bt 0 (map Int64.repr (fe_limbs_of (be_val bytes)))).
  { eapply owned_region_field_slice with (rho:=byte_rho bytes) (beta:=[(bt,0);(bb,0)]) (r:=0%nat)
      (size:=40) (exprs:=generator_field_exprs).
    - exact R0.
    - lia.
    - exists 0;reflexivity.
    - lia.
    - change (40<=18446744073709551615);lia.
    - exact generator_field_length.
    - rewrite map_length;reflexivity.
    - intros;assumption.
    - apply generator_field_den;assumption. }
  assert (BytesF:forall i,(i<32)%nat ->
    Mem.load Mint8unsigned mf bb (Z.of_nat i)=Some (Vint (Int.repr (nth i bytes 0)))).
  { intros i Index.
    pose proof (region_load _ _ _ 1 _ (Z.of_nat i) Mint8unsigned (XL2I (XLv i)) R1) as Load.
    assert (Member:In (mkcell (Z.of_nat i) Mint8unsigned (Some (XL2I (XLv i))))
      (C.jet_secp_fe_b32.byte_cells 0 32 0)).
    { change (In (mkcell (0+Z.of_nat i) Mint8unsigned (Some (XL2I (XLv (0+i)))))
        (C.jet_secp_fe_b32.byte_cells 0 32 0));apply generator_byte_member;exact Index. }
    specialize (Load Member);change (Mem.load Mint8unsigned mf bb (Z.of_nat i)=
      Some (Vint (Int64.loword (byte_rho bytes i)))) in Load.
    rewrite byte_loword_exact in Load by exact Bytes;exact Load. }
  exists mf;split;[exact Call|];split;[exact Field|];split;[exact FTF|];split;[exact FBF|];
    split;[exact BytesF|];split.
  - exact (curve_frame_two owned_b32_regs bt bb m mf eq_refl Frame).
  - eapply (secp_closed_function_preserved f_secp256k1_fe_set_b32);[reflexivity|reflexivity|exact Call].
Qed.
