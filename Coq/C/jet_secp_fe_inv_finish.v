(** Original fe_inv_var suffix: unpack an already canonical signed62 result
    and reclaim the actual two caller locals. This does not execute or assume
    correctness of the preceding modular-inverse call. Both whole-field and
    embedded output slices are supported, preserving bytes outside the slice. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_fe_inv_statements C.jet_secp_curve_statements C.jet_secp_curve_frame.
Require Import C.jet_secp_signed62_storage C.jet_secp_signed62_repack C.jet_secp_signed62_numeric.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_signed62_slice C.jet_clight_internal_permissions.
Require Import C.jet_secp_square_columns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma fe_inv_local_blocks bt bs : blocks_of_env secp_ge (fe_inv_env bt bs) =
  [(bs,0,40);(bt,0,40)].
Proof. reflexivity. Qed.

Theorem exec_fe_inv_unpack_slice_and_free le m bt bs bd base size w :
  le!_r=Some(Vptr bd(Ptrofs.repr base)) -> bt<>bs -> bd<>bt -> bd<>bs ->
  0<=base -> (8|base) -> base+40<=Ptrofs.max_unsigned -> base+40<=size ->
  signed62_normalized w -> fe_at m bs 0 (words5 w) ->
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bd 0 size Cur Freeable -> exists mf mr,
  Clight2.exec_stmt secp_ge (fe_inv_env bt bs) le m fe_inv_unpack E0 le mf Out_normal /\
  Mem.free_list mf (blocks_of_env secp_ge (fe_inv_env bt bs))=Some mr /\
  fe_at mr bd base (words5(fe_repack_words false w)) /\
  Mem.range_perm mr bd 0 size Cur Freeable /\
  fe_limbs_ok (Int64.unsigned(fe_repack_words false w 0%nat))
    (Int64.unsigned(fe_repack_words false w 1%nat))
    (Int64.unsigned(fe_repack_words false w 2%nat))
    (Int64.unsigned(fe_repack_words false w 3%nat))
    (Int64.unsigned(fe_repack_words false w 4%nat)) /\
  radix_value(fe_repack_words false w)=signed62_unsigned_value w /\
  lframe (fun b pos=>(b<>bd \/ pos<base \/ base+40<=pos) /\ b<>bt /\ b<>bs) m mr.
Proof.
  intros HR TS DT DS Base Align Max Fit Bound Field FS FT FD.
  assert(Write:Mem.range_perm m bd base (base+40) Cur Writable).
  { intros pos Range;eapply Mem.perm_implies;[apply FD;lia|constructor]. }
  destruct(eval_fe_repack_to_slice false w m bd base bs DS Base Align Max Write Field)
    as (mf & Call & Out & Inp & Keep & Frame).
  assert(FTF:Mem.range_perm mf bt 0 40 Cur Freeable) by (intros pos Range;apply Keep,FT;exact Range).
  assert(FSF:Mem.range_perm mf bs 0 40 Cur Freeable) by (intros pos Range;apply Keep,FS;exact Range).
  assert(FDF:Mem.range_perm mf bd 0 size Cur Freeable) by (intros pos Range;apply Keep,FD;exact Range).
  assert(Exec:Clight2.exec_stmt secp_ge (fe_inv_env bt bs) le m fe_inv_unpack E0 le mf Out_normal).
  { unfold fe_inv_unpack;eapply exec_curve_call with
      (vargs:=[Vptr bd(Ptrofs.repr base);Vptr bs Ptrofs.zero]) (v:=Vundef).
    - unfold secp_pure;repeat(first[left;reflexivity|right]).
    - reflexivity.
    - eapply eval_Econs;[apply eval_Etempvar;exact HR|reflexivity|].
      eapply eval_Econs;[unfold fe_inv_s_address;apply eval_Eaddrof;apply eval_Evar_local;reflexivity|
        reflexivity|constructor].
    - exact Call. }
  destruct(free_list_exists [(bs,0,40);(bt,0,40)] mf) as (mr & Free & Unchanged).
  - cbn;repeat constructor;cbn;intuition congruence.
  - intros b lo hi [Eq|[Eq|Nil]];[inversion Eq;subst;exact FSF|inversion Eq;subst;exact FTF|contradiction].
  - assert(Freed:lframe (fun b _=>b<>bt /\ b<>bs) mf mr).
    { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
      intros b pos [NotT NotS] Valid;cbn;intuition congruence. }
    assert(Result:fe_at mr bd base (words5(fe_repack_words false w))).
    { eapply curve_keep_field_range;[reflexivity|exact Out|exact Freed|];intros;split;assumption. }
    assert(FDR:Mem.range_perm mr bd 0 size Cur Freeable).
    { eapply curve_keep_free;[lia|exact FDF|exact Freed|];intros;split;assumption. }
    assert(WholeFrame:lframe (fun b pos=>(b<>bd \/ pos<base \/ base+40<=pos) /\ b<>bt /\ b<>bs) m mr).
    { eapply lframe_trans.
      - eapply lframe_implies;[exact Frame|];intros b pos [Outside [NotT NotS]] Valid;split;assumption.
      - eapply lframe_implies;[exact Freed|];intros b pos [Outside [NotT NotS]] Valid;split;assumption. }
    exists mf,mr;rewrite fe_inv_local_blocks;split;[exact Exec|];split;[exact Free|];split;[exact Result|];
      split;[exact FDR|];split;[apply fe_from62_positioned;exact Bound|];
      split;[apply fe_from62_preserves_value;exact Bound|exact WholeFrame].
Qed.

Theorem exec_fe_inv_unpack_and_free le m bt bs bd w :
  le!_r=Some(Vptr bd Ptrofs.zero) -> bt<>bs -> bd<>bt -> bd<>bs ->
  signed62_normalized w -> fe_at m bs 0 (words5 w) ->
  Mem.range_perm m bs 0 40 Cur Freeable ->
  Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bd 0 40 Cur Freeable -> exists mf mr,
  Clight2.exec_stmt secp_ge (fe_inv_env bt bs) le m fe_inv_unpack E0 le mf Out_normal /\
  Mem.free_list mf (blocks_of_env secp_ge (fe_inv_env bt bs))=Some mr /\
  fe_at mr bd 0 (words5 (fe_repack_words false w)) /\
  Mem.range_perm mr bd 0 40 Cur Freeable /\
  fe_limbs_ok (Int64.unsigned (fe_repack_words false w 0%nat))
    (Int64.unsigned (fe_repack_words false w 1%nat))
    (Int64.unsigned (fe_repack_words false w 2%nat))
    (Int64.unsigned (fe_repack_words false w 3%nat))
    (Int64.unsigned (fe_repack_words false w 4%nat)) /\
  radix_value (fe_repack_words false w)=signed62_unsigned_value w /\
  lframe (fun b _=>b<>bd /\ b<>bt /\ b<>bs) m mr.
Proof.
  intros HR TS DT DS Bound Field FS FT FD.
  destruct(exec_fe_inv_unpack_slice_and_free le m bt bs bd 0 40 w HR TS DT DS
    ltac:(lia) ltac:(exists 0;reflexivity) ltac:(change(40<=18446744073709551615);lia)
    ltac:(lia) Bound Field FS FT FD)
    as (mf & mr & Exec & Free & Result & Owned & Limbs & Value & Frame).
  assert(Outside:lframe (fun b _=>b<>bd /\ b<>bt /\ b<>bs) m mr).
  { eapply lframe_implies;[exact Frame|];intros b pos [NotD [NotT NotS]] Valid.
    split;[left;exact NotD|];split;assumption. }
  exists mf,mr;repeat first[assumption|split].
Qed.

Lemma fe_inv_unpacked_bounds w : signed62_normalized w -> square_input_bounds(fe_repack_words false w).
Proof.
  intro Bound;pose proof(fe_from62_positioned w Bound) as Limbs.
  unfold fe_limbs_ok in Limbs.
  intros i Index;destruct i as [|[|[|[|[|i]]]]];try lia;cbn [Nat.eqb];lia.
Qed.

(** The actual point caller's Z-at-80 return path. X/Y and the entire
    128-byte point allocation survive the conversion and private frees. *)
Theorem exec_fe_inv_unpack_point_and_free le m bt bs bp w x y :
  le!_r=Some(Vptr bp(Ptrofs.repr 80)) -> bt<>bs -> bp<>bt -> bp<>bs ->
  signed62_normalized w -> fe_at m bs 0 (words5 w) ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) ->
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bp 0 128 Cur Freeable -> exists mf mr,
  Clight2.exec_stmt secp_ge (fe_inv_env bt bs) le m fe_inv_unpack E0 le mf Out_normal /\
  Mem.free_list mf (blocks_of_env secp_ge (fe_inv_env bt bs))=Some mr /\
  fe_at mr bp 0 (words5 x) /\ fe_at mr bp 40 (words5 y) /\
  fe_at mr bp 80 (words5(fe_repack_words false w)) /\
  Mem.range_perm mr bp 0 128 Cur Freeable /\ square_input_bounds(fe_repack_words false w) /\
  radix_value(fe_repack_words false w)=signed62_unsigned_value w /\
  lframe (fun b pos=>(b<>bp \/ pos<80 \/ 120<=pos) /\ b<>bt /\ b<>bs) m mr.
Proof.
  intros Result TS PT PS Bound Field X Y FS FT FP.
  destruct(exec_fe_inv_unpack_slice_and_free le m bt bs bp 80 128 w Result TS PT PS
    ltac:(lia) ltac:(exists 10;reflexivity) ltac:(change(120<=18446744073709551615);lia)
    ltac:(lia) Bound Field FS FT FP)
    as (mf & mr & Exec & Free & Z & Owned & Limbs & Value & Frame).
  assert(XR:fe_at mr bp 0 (words5 x)).
  { eapply curve_keep_field_range;[reflexivity|exact X|exact Frame|];intros pos Range.
    split;[right;left;lia|];split;assumption. }
  assert(YR:fe_at mr bp 40 (words5 y)).
  { eapply curve_keep_field_range;[reflexivity|exact Y|exact Frame|];intros pos Range.
    split;[right;left;lia|];split;assumption. }
  pose proof(fe_inv_unpacked_bounds w Bound) as Bounds.
  exists mf,mr;repeat first[assumption|split].
Qed.
