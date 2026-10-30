(** Fine memory frame and retained source bytes of the original field parser. *)
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

Require Import C.jet_secp_set_b32_owned.
Theorem eval_set_b32_owned_frame bytes m bt bb : length bytes=32%nat -> Forall (fun x=>0<=x<=255) bytes -> bt<>bb ->
  Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bb 0 32 Cur Freeable ->
  (forall i,(i<32)%nat -> Mem.load Mint8unsigned m bb (Z.of_nat i)=Some (Vint (Int.repr (nth i bytes 0)))) ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_set_b32)
    [Vptr bt Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf (Vint (Int.repr (b2z (Z.ltb (be_val bytes) feP)))) /\
  fe_at mf bt 0 (map Int64.repr (fe_limbs_of (be_val bytes))) /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 32 Cur Freeable /\
  (forall i,(i<32)%nat -> Mem.load Mint8unsigned mf bb (Z.of_nat i)=Some (Vint (Int.repr (nth i bytes 0)))) /\
  lframe (fun b pos=>~foot [(bt,0);(bb,0)] (map rshape owned_b32_regs) b pos) m mf /\ readonly_preserved m mf.
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
  - exact Frame.
  - eapply (secp_closed_function_preserved f_secp256k1_fe_set_b32);[reflexivity|reflexivity|exact Call].
Qed.
Lemma owned_b32_foot_bounds bt bb b pos:
 foot [(bt,0);(bb,0)] (map rshape owned_b32_regs) b pos ->
 (b=bt /\0<=pos<40) \/(b=bb /\0<=pos<32).
Proof.
 intros (r & shape & d & chunk & Region & Cell & Block & Range).
 destruct r as [|[|r]].
 - left;split;[exact Block|].
   cbn [owned_b32_regs free_region fe_undef map nth_error rshape rcells rw rfree] in Region.
   injection Region as <-.
   cbn [map cshape cofs cchunk fst In] in Cell.
   repeat destruct Cell as [Cell|Cell];try contradiction;injection Cell as <- <-;
   cbn [bas lay nth snd size_chunk] in Range;lia.
 - right;split;[exact Block|].
   cbn [owned_b32_regs map nth_error rshape owned_b32_source rcells rw rfree] in Region.
   injection Region as <-.
   apply in_map_iff in Cell as (c & Shape & Member).
   destruct (b32_byte_cells_in 32 0 0 c Member) as (i & Index & Eq);subst c.
   inversion Shape;subst d chunk.
   change (0+(0+Z.of_nat i)<=pos<0+(0+Z.of_nat i)+1) in Range;lia.
 - destruct r;discriminate Region.
Qed.
