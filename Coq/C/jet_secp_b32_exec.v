(** Actual byte/limb conversion execution, developed outside frozen audit inputs. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_exec C.jet_sx_pure.
Require Import C.jet_sx_zval C.jet_sx_rep C.jet_sx_zrep.
Require Import C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_read8s_layout.
Import ListNotations Values Mem Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition byte_rho (bytes : list Z) (n : nat) : int64 := Int64.repr (nth n bytes 0).
Definition byte_bnd (_ : nat) : Z * Z := (0, 255).

Lemma nth_byte_bound bytes :
  Forall (fun byte => 0 <= byte <= 255) bytes ->
  forall n, 0 <= nth n bytes 0 <= 255.
Proof.
  intros H; induction H; intros [|n]; cbn; try lia; apply IHForall.
Qed.

Lemma byte_rho_unsigned bytes n :
  Forall (fun byte => 0 <= byte <= 255) bytes ->
  Int64.unsigned (byte_rho bytes n) = nth n bytes 0.
Proof.
  intro HBytes; unfold byte_rho; apply Int64.unsigned_repr.
  pose proof (nth_byte_bound bytes HBytes n).
  change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

Lemma byte_rho_bound bytes :
  Forall (fun byte => 0 <= byte <= 255) bytes ->
  forall n, fst (byte_bnd n) <= Int64.unsigned (byte_rho bytes n) <= snd (byte_bnd n).
Proof.
  intros HBytes n; rewrite byte_rho_unsigned by exact HBytes.
  apply nth_byte_bound; exact HBytes.
Qed.

Lemma sb_output_region :
  nth_error (sregs sb_leaf) 0 = Some (mkreg (cells0 sb_leaf) true None).
Proof. vm_compute; reflexivity. Qed.
Lemma sb_output_length : length (cells0 sb_leaf) = 5%nat.
Proof. reflexivity. Qed.
Lemma sb_output_checked : zreg_okb byte_bnd 0 (cells0 sb_leaf) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma sb_return_checked : zb byte_bnd sb_ret = Some (0, 1).
Proof. vm_compute; reflexivity. Qed.
Lemma sb_return_kind : isk KI sb_ret = true.
Proof. vm_compute; reflexivity. Qed.

Lemma sb_output_numeric bytes :
  length bytes = 32%nat -> Forall (fun byte => 0 <= byte <= 255) bytes ->
  zcells (zrho (byte_rho bytes)) (cells0 sb_leaf) = fe_limbs_of (be_val bytes) /\
  zval (zrho (byte_rho bytes)) sb_ret = b2z (Z.ltb (be_val bytes) feP).
Proof.
  intros HLength HBytes.
  assert (HRho : forall n, zrho (byte_rho bytes) n = nth n bytes 0).
  { intro n; exact (byte_rho_unsigned bytes n HBytes). }
  rewrite (zcells_ext _ _ _ HRho), (zval_ext _ _ _ HRho).
  apply sb_math; assumption.
Qed.

Theorem eval_fe_set_b32_from_initial_regions m b ofs bb offset bytes :
  length bytes = 32%nat -> Forall (fun byte => 0 <= byte <= 255) bytes ->
  0 <= ofs -> (8 | ofs) -> ofs + 40 <= Ptrofs.max_unsigned ->
  rep (byte_rho bytes) [(b, ofs); (bb, offset)]
    [fe_undef; mkreg (jet_secp_fe_b32.byte_cells 0 32 0) false None] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_set_b32)
      [Vptr b (Ptrofs.repr ofs); Vptr bb (Ptrofs.repr offset)] E0 mf
      (Vint (Int.repr (b2z (Z.ltb (be_val bytes) feP)))) /\
    fe_at mf b ofs (map Int64.repr (fe_limbs_of (be_val bytes))) /\
    lframe (fun block pos =>
      ~ foot [(b, ofs); (bb, offset)]
        (map rshape [fe_undef; mkreg (jet_secp_fe_b32.byte_cells 0 32 0) false None])
        block pos) m mf.
Proof.
  intros HLength HBytes HOfs HAlign HMax HRep.
  set (rho := byte_rho bytes) in *.
  pose proof (byte_rho_bound bytes HBytes) as Hb; fold rho in Hb.
  pose proof (sb_output_numeric bytes HLength HBytes) as [HLimbs HReturn]; fold rho in HLimbs, HReturn.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 400 f_secp256k1_fe_set_b32
      [XP 0 0; XP 1 0]
      [fe_undef; mkreg (jet_secp_fe_b32.byte_cells 0 32 0) false None]
      32 _ sb_run_eq eq_refl rho [(b, ofs); (bb, offset)] m HRep)
    as [mf [result [HExec [HFinal [HRet [HShape HFrame]]]]]].
  cbn [rsel fst] in HFinal, HRet.
  change (result = den rho (lay [(b, ofs); (bb, offset)]) sb_ret) in HRet.
  pose proof (proj1 (den_zval_int rho byte_bnd (lay [(b, ofs); (bb, offset)]) Hb
    sb_ret 0 1 sb_return_checked sb_return_kind)) as HDen.
  rewrite HReturn in HDen; rewrite HDen in HRet; subst result.
  change (map (den rho (lay [(b, ofs); (bb, offset)])) [XP 0 0; XP 1 0]) with
    [Vptr b (Ptrofs.repr (ofs + 0)); Vptr bb (Ptrofs.repr (offset + 0))] in HExec.
  rewrite !Z.add_0_r in HExec.
  exists mf; split; [exact HExec|]; split; [|exact HFrame].
  destruct (rep_region rho [(b, ofs); (bb, offset)] _ mf 0 _ HFinal sb_output_region)
    as [_ [_ [_ [HCells _]]]].
  destruct (zreg_load rho byte_bnd [(b, ofs); (bb, offset)] Hb mf 0 true
    (cells0 sb_leaf) 0 sb_output_checked HCells) as [HLoad HPerm].
  rewrite sb_output_length in HPerm.
  cbn [blk bas lay nth fst snd] in HLoad, HPerm.
  rewrite !Z.add_0_r in HPerm.
  change (Mem.range_perm mf b ofs (ofs + 40) Cur Writable) in HPerm.
  split; [exact HOfs|]; split; [exact HAlign|]; split; [exact HMax|]; split; [exact HPerm|].
  rewrite <- HLimbs.
  intros i value HNth; rewrite nth_error_map in HNth.
  destruct (nth_error (zcells (zrho rho) (cells0 sb_leaf)) i) as [z|] eqn:HZ; [|discriminate].
  inversion HNth; subst value.
  rewrite <- (HLoad i z HZ); f_equal; lia.
Qed.

Lemma fold_be_bytes_bound bytes :
  Forall (fun byte => 0 <= byte <= 255) bytes ->
  forall acc, 0 <= acc ->
    acc * 256 ^ Z.of_nat (length bytes) <= fold_left (fun v byte => v * 256 + byte) bytes acc <
    (acc + 1) * 256 ^ Z.of_nat (length bytes).
Proof.
  intros HBytes; induction HBytes; intros acc HAcc.
  - cbn; lia.
  - cbn [fold_left length].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    pose proof (IHHBytes (acc * 256 + x) ltac:(nia)) as HNext.
    pose proof (Z.pow_pos_nonneg 256 (Z.of_nat (length l)) ltac:(lia) ltac:(lia)) as HPow.
    nia.
Qed.

Lemma be_32_bytes_bound bytes :
  length bytes = 32%nat -> Forall (fun byte => 0 <= byte <= 255) bytes ->
  0 <= be_val bytes < 2 ^ 256.
Proof.
  intros HLength HBytes.
  pose proof (fold_be_bytes_bound bytes HBytes 0 ltac:(lia)) as HBound.
  rewrite HLength in HBound.
  change (0 <= be_val bytes < 2 ^ 256) in HBound; exact HBound.
Qed.

Lemma canonical_limbs_from_bytes_bound bytes :
  length bytes = 32%nat -> Forall (fun byte => 0 <= byte <= 255) bytes ->
  Forall (fun limb => 0 <= limb <= 2 ^ 60) (fe_limbs_of (be_val bytes)).
Proof.
  intros HLength HBytes.
  pose proof (proj1 (fe_limbs_of_ok (be_val bytes)
    (be_32_bytes_bound bytes HLength HBytes))) as HBounds.
  unfold fe_limbs_ok in HBounds; unfold fe_limbs_of.
  repeat constructor; change (2 ^ 60) with 1152921504606846976;
    change (2 ^ 52) with 4503599627370496 in *;
    change (2 ^ 48) with 281474976710656 in *; lia.
Qed.

Lemma canonical_limb_unsigned limb :
  0 <= limb <= 2 ^ 60 -> Int64.unsigned (Int64.repr limb) = limb.
Proof.
  intro HBound; apply Int64.unsigned_repr.
  change (2 ^ 60) with 1152921504606846976 in HBound;
    change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

Lemma set_b32_normalization_bounds_derived bytes :
  length bytes = 32%nat -> Forall (fun byte => 0 <= byte <= 255) bytes ->
  Forall (fun limb => Int64.unsigned limb <= 2 ^ 60)
    (map Int64.repr (fe_limbs_of (be_val bytes))).
Proof.
  intros HLength HBytes; apply Forall_map.
  eapply Forall_impl; [|exact (canonical_limbs_from_bytes_bound bytes HLength HBytes)].
  intros limb HBound; rewrite canonical_limb_unsigned by exact HBound.
  exact (proj2 HBound).
Qed.

Fixpoint zbyte_reg_okb (bnd : nat -> Z * Z) (ofs : Z) (cells : list cell) : bool :=
  match cells with
  | [] => true
  | c :: tail =>
    Z.eqb (cofs c) ofs && chunk_eqb (cchunk c) Mint8unsigned &&
    match cval c with
    | Some x => isk KI x && match zb bnd x with Some _ => true | None => false end
    | None => false
    end && zbyte_reg_okb bnd (ofs + 1) tail
  end.

Lemma zbyte_region_load rho bnd layout
    (HB : forall n, fst (bnd n) <= Int64.unsigned (rho n) <= snd (bnd n)) m r writable cells :
  forall offset,
    zbyte_reg_okb bnd offset cells = true ->
    Forall (cell_ok rho layout m r writable) cells ->
    forall i z, nth_error (zcells (zrho rho) cells) i = Some z ->
      Mem.load Mint8unsigned m (blk layout r) (bas layout r + (offset + Z.of_nat i)) =
      Some (Vint (Int.repr z)).
Proof.
  induction cells as [|c tail IH]; intros offset HCheck HCells i z HNth.
  - destruct i; discriminate.
  - cbn in HCheck.
    apply andb_true_iff in HCheck; destruct HCheck as [HCheck HTail].
    apply andb_true_iff in HCheck; destruct HCheck as [HCheck HValue].
    apply andb_true_iff in HCheck; destruct HCheck as [HOffset HChunk].
    apply Z.eqb_eq in HOffset; apply chunk_eqb_eq in HChunk.
    destruct (cval c) as [x|] eqn:HCVal; [|discriminate].
    apply andb_true_iff in HValue; destruct HValue as [HKind HZ].
    destruct (zb bnd x) as [[lo hi]|] eqn:HZB; [|discriminate].
    inversion HCells as [|? ? HCell HRest]; subst.
    destruct HCell as [_ [_ [_ HLoad]]].
    destruct i.
    + cbn [zcells map nth_error] in HNth; rewrite HCVal in HNth.
      inversion HNth; subst z.
      destruct (HLoad x HCVal) as [HL _].
      rewrite HChunk in HL; change (Z.of_nat 0) with 0.
      rewrite Z.add_0_r, HL.
      rewrite (proj1 (den_zval_int rho bnd (lay layout) HB x lo hi HZB HKind)); reflexivity.
    + cbn [zcells map nth_error] in HNth.
      replace (cofs c + Z.of_nat (S i)) with (cofs c + 1 + Z.of_nat i) by lia.
      eapply IH; [exact HTail|exact HRest|exact HNth].
Qed.

Definition limb52_bnd (_ : nat) : Z * Z := (0, 2 ^ 52 - 1).
Lemma gb_output_region :
  nth_error (sregs gb_leaf) 0 = Some (mkreg (cells0 gb_leaf) true None).
Proof. vm_compute; reflexivity. Qed.
Lemma gb_output_length : length (cells0 gb_leaf) = 32%nat.
Proof. reflexivity. Qed.
Lemma gb_output_checked : zbyte_reg_okb limb52_bnd 0 (cells0 gb_leaf) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma gb_return_empty : (stemps gb_leaf)!1%positive = None.
Proof. reflexivity. Qed.

Definition limb_rho (value : Z) (n : nat) : int64 :=
  Int64.repr (nth n (fe_limbs_of value) 0).

Lemma limb_list_52_bound value :
  0 <= value < 2 ^ 256 ->
  Forall (fun limb => 0 <= limb <= 2 ^ 52 - 1) (fe_limbs_of value).
Proof.
  intro HValue; pose proof (proj1 (fe_limbs_of_ok value HValue)) as HBounds.
  unfold fe_limbs_ok in HBounds; unfold fe_limbs_of.
  repeat constructor;
    change (2 ^ 52) with 4503599627370496 in *;
    change (2 ^ 48) with 281474976710656 in *; lia.
Qed.

Lemma nth_limb_52_bound limbs :
  Forall (fun limb => 0 <= limb <= 2 ^ 52 - 1) limbs ->
  forall n, 0 <= nth n limbs 0 <= 2 ^ 52 - 1.
Proof.
  intros H; induction H; intros [|n]; cbn; try lia; apply IHForall.
Qed.

Lemma limb_rho_unsigned value n :
  0 <= value < 2 ^ 256 ->
  Int64.unsigned (limb_rho value n) = nth n (fe_limbs_of value) 0.
Proof.
  intro HValue; unfold limb_rho; apply Int64.unsigned_repr.
  pose proof (nth_limb_52_bound _ (limb_list_52_bound value HValue) n) as HBound.
  change (2 ^ 52) with 4503599627370496 in HBound;
    change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

Lemma limb_rho_bound value :
  0 <= value < 2 ^ 256 ->
  forall n, fst (limb52_bnd n) <= Int64.unsigned (limb_rho value n) <= snd (limb52_bnd n).
Proof.
  intros HValue n; rewrite limb_rho_unsigned by exact HValue.
  apply nth_limb_52_bound; apply limb_list_52_bound; exact HValue.
Qed.

Lemma gb_output_numeric value :
  0 <= value < 2 ^ 256 ->
  zcells (zrho (limb_rho value)) (cells0 gb_leaf) = be_bytes value.
Proof.
  intro HValue.
  rewrite (zcells_ext _ (fun n => nth n (fe_limbs_of value) 0) _).
  - apply gb_math; exact HValue.
  - intro n; exact (limb_rho_unsigned value n HValue).
Qed.

Theorem eval_fe_get_b32_from_initial_regions m b offset bf base value :
  0 <= value < 2 ^ 256 ->
  rep (limb_rho value) [(b, offset); (bf, base)]
    [mkreg (jet_secp_fe_b32.byte_undef 0 32) true None;
     mkreg (u64_cells 0 (vars5 0)) false None] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_get_b32)
      [Vptr b (Ptrofs.repr offset); Vptr bf (Ptrofs.repr base)] E0 mf Vundef /\
    uint8_array_at mf b offset (map Int.repr (be_bytes value)) /\
    lframe (fun block pos =>
      ~ foot [(b, offset); (bf, base)]
        (map rshape [mkreg (jet_secp_fe_b32.byte_undef 0 32) true None;
                     mkreg (u64_cells 0 (vars5 0)) false None]) block pos) m mf.
Proof.
  intros HValue HRep; set (rho := limb_rho value) in *.
  pose proof (limb_rho_bound value HValue) as Hb; fold rho in Hb.
  pose proof (gb_output_numeric value HValue) as HBytes; fold rho in HBytes.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 400 f_secp256k1_fe_get_b32
      [XP 0 0; XP 1 0]
      [mkreg (jet_secp_fe_b32.byte_undef 0 32) true None;
       mkreg (u64_cells 0 (vars5 0)) false None]
      5 _ gb_run_eq eq_refl rho [(b, offset); (bf, base)] m HRep)
    as [mf [result [HExec [HFinal [HRet [HShape HFrame]]]]]].
  cbn [rsel fst] in HFinal, HRet.
  rewrite gb_return_empty in HRet; subst result.
  change (map (den rho (lay [(b, offset); (bf, base)])) [XP 0 0; XP 1 0]) with
    [Vptr b (Ptrofs.repr (offset + 0)); Vptr bf (Ptrofs.repr (base + 0))] in HExec.
  rewrite !Z.add_0_r in HExec.
  exists mf; split; [exact HExec|]; split; [|exact HFrame].
  destruct (rep_region rho [(b, offset); (bf, base)] _ mf 0 _ HFinal gb_output_region)
    as [_ [_ [_ [HCells _]]]].
  pose proof (zbyte_region_load rho limb52_bnd [(b, offset); (bf, base)] Hb mf 0 true
    (cells0 gb_leaf) 0 gb_output_checked HCells) as HLoad.
  cbn [blk bas lay nth fst snd] in HLoad.
  unfold uint8_array_at; rewrite <- HBytes.
  intros i byte HNth; rewrite nth_error_map in HNth.
  destruct (nth_error (zcells (zrho rho) (cells0 gb_leaf)) i) as [z|] eqn:HZ; [|discriminate].
  inversion HNth; subst byte.
  rewrite <- (HLoad i z HZ); f_equal; lia.
Qed.

Lemma writable_undefined_cell rho layout m r chunk offset :
  bas layout r + offset + size_chunk chunk <= Ptrofs.max_unsigned ->
  (align_chunk chunk | bas layout r + offset) ->
  Mem.range_perm m (blk layout r) (bas layout r + offset)
    (bas layout r + offset + size_chunk chunk) Cur Writable ->
  cell_ok rho layout m r true (mkcell offset chunk None).
Proof.
  intros HMax HAlign HPerm; split; [exact HMax|].
  split; [exact HAlign|]; split; [exact HPerm|].
  intros x HImpossible; discriminate.
Qed.

Lemma region_fe_undefined_from_storage rho layout m r :
  0 <= bas layout r -> (8 | bas layout r) ->
  bas layout r + 40 <= Ptrofs.max_unsigned ->
  Mem.range_perm m (blk layout r) (bas layout r) (bas layout r + 40) Cur Writable ->
  region_ok rho layout m r fe_undef.
Proof.
  intros HBase HAlign HMax HPerm.
  split; [exact HBase|]; split.
  - eapply Mem.perm_valid_block; apply (HPerm (bas layout r)); lia.
  - split; [reflexivity|]; split; [|exact I].
    apply Forall_forall; intros c HIn.
    cbn [fe_undef rcells In] in HIn.
    repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
      try contradiction; subst c;
      apply writable_undefined_cell; cbn [size_chunk align_chunk]; try lia.
    all: try (intros pos HRange; apply HPerm; lia).
    all: apply Z.divide_add_r; [exact HAlign|].
    all: match goal with |- (8 | ?offset) => exists (offset / 8); reflexivity end.
Qed.

Lemma byte_cells_sorted count : forall offset start lower,
  lower <= offset ->
  cells_sorted lower (jet_secp_fe_b32.byte_cells offset count start) = true.
Proof.
  induction count as [|count IH]; intros offset start lower HLower; cbn; [reflexivity|].
  apply andb_true_iff; split; [apply Z.leb_le; exact HLower|].
  apply IH; cbn; lia.
Qed.

Lemma b32_byte_cells_in count : forall offset start c,
  In c (jet_secp_fe_b32.byte_cells offset count start) ->
  exists i, (i < count)%nat /\
    c = mkcell (offset + Z.of_nat i) Mint8unsigned (Some (XL2I (XLv (start + i)))).
Proof.
  induction count as [|count IH]; intros offset start c HIn; cbn in HIn; [contradiction|].
  destruct HIn as [HHead|HTail].
  - subst c; exists 0%nat; split; [lia|].
    rewrite Nat.add_0_r, Z.add_0_r; reflexivity.
  - destruct (IH _ _ _ HTail) as [i [HIndex HCell]].
    exists (S i); split; [lia|]; rewrite HCell; f_equal; [lia|].
    replace (start + S i)%nat with (S start + i)%nat by lia; reflexivity.
Qed.

Lemma byte_loword_exact bytes n :
  Forall (fun byte => 0 <= byte <= 255) bytes ->
  Int64.loword (byte_rho bytes n) = Int.repr (nth n bytes 0).
Proof.
  intro HBytes; unfold Int64.loword; rewrite byte_rho_unsigned by exact HBytes.
  reflexivity.
Qed.

Lemma region_b32_bytes_from_storage bytes layout m r :
  length bytes = 32%nat ->
  Forall (fun byte => 0 <= byte <= 255) bytes ->
  0 <= bas layout r -> bas layout r + 32 <= Ptrofs.max_unsigned ->
  Mem.range_perm m (blk layout r) (bas layout r) (bas layout r + 32) Cur Readable ->
  (forall i, (i < 32)%nat ->
     Mem.load Mint8unsigned m (blk layout r) (bas layout r + Z.of_nat i) =
       Some (Vint (Int.repr (nth i bytes 0)))) ->
  region_ok (byte_rho bytes) layout m r
    (mkreg (jet_secp_fe_b32.byte_cells 0 32 0) false None).
Proof.
  intros HLength HBytes HBase HMax HPerm HLoad.
  split; [exact HBase|]; split.
  - eapply Mem.perm_valid_block; apply (HPerm (bas layout r)); lia.
  - split; [apply byte_cells_sorted; lia|]; split; [|exact I].
    apply Forall_forall; intros c HIn.
    destruct (b32_byte_cells_in _ _ _ _ HIn) as [i [HIndex HCell]].
    rewrite HCell; unfold cell_ok; cbn [rw cofs cchunk cval size_chunk align_chunk].
    rewrite Z.add_0_l, Nat.add_0_l.
    split; [lia|]; split; [exists (bas layout r + Z.of_nat i); lia|].
    split; [intros pos HRange; apply HPerm; lia|].
    intros x HSome; inversion HSome; subst x; split; [|reflexivity].
    cbn [den il]; rewrite byte_loword_exact by exact HBytes.
    apply HLoad; exact HIndex.
Qed.

Lemma two_region_rep_separate rho layout m left right :
  length layout = 2%nat -> blk layout 0 <> blk layout 1 ->
  region_ok rho layout m 0 left -> region_ok rho layout m 1 right ->
  rep rho layout [left; right] m.
Proof.
  intros HLength HDifferent HLeft HRight.
  split; [exact HLength|]; split.
  - intros r1 r2 reg1 reg2 HNe E1 E2.
    assert (HB1 : (r1 < 2)%nat).
    { change (r1 < length [left; right])%nat; apply nth_error_Some; congruence. }
    assert (HB2 : (r2 < 2)%nat).
    { change (r2 < length [left; right])%nat; apply nth_error_Some; congruence. }
    destruct r1 as [|[|r1]], r2 as [|[|r2]]; try lia;
      left; congruence.
  - intros r reg HGet.
    assert (HB : (r < 2)%nat).
    { change (r < length [left; right])%nat; apply nth_error_Some; congruence. }
    destruct r as [|[|r]]; try lia; cbn in HGet;
      inversion HGet; subst reg; assumption.
Qed.

Theorem set_b32_initial_rep_derived bytes bfe feofs bbytes byteofs m :
  length bytes = 32%nat ->
  Forall (fun byte => 0 <= byte <= 255) bytes ->
  0 <= feofs -> (8 | feofs) -> feofs + 40 <= Ptrofs.max_unsigned ->
  Mem.range_perm m bfe feofs (feofs + 40) Cur Writable ->
  0 <= byteofs -> byteofs + 32 <= Ptrofs.max_unsigned ->
  Mem.range_perm m bbytes byteofs (byteofs + 32) Cur Readable ->
  (forall i, (i < 32)%nat ->
    Mem.load Mint8unsigned m bbytes (byteofs + Z.of_nat i) =
      Some (Vint (Int.repr (nth i bytes 0)))) ->
  bfe <> bbytes ->
  rep (byte_rho bytes) [(bfe, feofs); (bbytes, byteofs)]
    [fe_undef; mkreg (jet_secp_fe_b32.byte_cells 0 32 0) false None] m.
Proof.
  intros HLength HBytes HFeBase HFeAlign HFeMax HFePerm HByteBase HByteMax HBytePerm HLoad HDifferent.
  apply two_region_rep_separate; [reflexivity|exact HDifferent| |].
  - apply region_fe_undefined_from_storage; assumption.
  - apply region_b32_bytes_from_storage; assumption.
Qed.

Theorem eval_fe_set_b32_from_storage m b ofs bb offset bytes :
  length bytes = 32%nat -> Forall (fun byte => 0 <= byte <= 255) bytes ->
  0 <= ofs -> (8 | ofs) -> ofs + 40 <= Ptrofs.max_unsigned ->
  Mem.range_perm m b ofs (ofs + 40) Cur Writable ->
  0 <= offset -> offset + 32 <= Ptrofs.max_unsigned ->
  Mem.range_perm m bb offset (offset + 32) Cur Readable ->
  (forall i, (i < 32)%nat ->
    Mem.load Mint8unsigned m bb (offset + Z.of_nat i) =
      Some (Vint (Int.repr (nth i bytes 0)))) ->
  b <> bb ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_set_b32)
      [Vptr b (Ptrofs.repr ofs); Vptr bb (Ptrofs.repr offset)] E0 mf
      (Vint (Int.repr (b2z (Z.ltb (be_val bytes) feP)))) /\
    fe_at mf b ofs (map Int64.repr (fe_limbs_of (be_val bytes))) /\
    lframe (fun block pos =>
      ~ foot [(b, ofs); (bb, offset)]
        (map rshape [fe_undef; mkreg (jet_secp_fe_b32.byte_cells 0 32 0) false None])
        block pos) m mf.
Proof.
  intros HLength HBytes HBase HAlign HMax HPerm HByteBase HByteMax HBytePerm HLoad HDifferent.
  apply eval_fe_set_b32_from_initial_regions; try assumption.
  apply set_b32_initial_rep_derived; assumption.
Qed.

Lemma b32_undefined_cells_sorted count : forall offset lower,
  lower <= offset ->
  cells_sorted lower (jet_secp_fe_b32.byte_undef offset count) = true.
Proof.
  induction count as [|count IH]; intros offset lower HLower; cbn; [reflexivity|].
  apply andb_true_iff; split; [apply Z.leb_le; exact HLower|].
  apply IH; cbn; lia.
Qed.

Lemma b32_undefined_cells_in count : forall offset c,
  In c (jet_secp_fe_b32.byte_undef offset count) ->
  exists i, (i < count)%nat /\ c = mkcell (offset + Z.of_nat i) Mint8unsigned None.
Proof.
  induction count as [|count IH]; intros offset c HIn; cbn in HIn; [contradiction|].
  destruct HIn as [HHead|HTail].
  - subst c; exists 0%nat; split; [lia|]; rewrite Z.add_0_r; reflexivity.
  - destruct (IH _ _ HTail) as [i [HIndex HCell]].
    exists (S i); split; [lia|]; rewrite HCell; f_equal; lia.
Qed.

Lemma region_b32_undefined_from_storage rho layout m r :
  0 <= bas layout r -> bas layout r + 32 <= Ptrofs.max_unsigned ->
  Mem.range_perm m (blk layout r) (bas layout r) (bas layout r + 32) Cur Writable ->
  region_ok rho layout m r (mkreg (jet_secp_fe_b32.byte_undef 0 32) true None).
Proof.
  intros HBase HMax HPerm.
  split; [exact HBase|]; split.
  - eapply Mem.perm_valid_block; apply (HPerm (bas layout r)); lia.
  - split; [apply b32_undefined_cells_sorted; lia|]; split; [|exact I].
    apply Forall_forall; intros c HIn.
    destruct (b32_undefined_cells_in _ _ _ HIn) as [i [HIndex HCell]].
    rewrite HCell; apply writable_undefined_cell; cbn [size_chunk align_chunk]; rewrite Z.add_0_l.
    + lia.
    + exists (bas layout r + Z.of_nat i); lia.
    + intros pos HRange; apply HPerm; lia.
Qed.

Lemma vars5_zero_nth i x :
  nth_error (vars5 0) i = Some x -> (i < 5)%nat /\ x = XLv i.
Proof.
  destruct i as [|[|[|[|[|i]]]]]; cbn [vars5 nth_error]; intros H;
    try (inversion H; subst x; split; [lia|reflexivity]).
  destruct i; discriminate.
Qed.

Lemma region_canonical_limbs_from_fe_at value layout m r :
  fe_at m (blk layout r) (bas layout r) (map Int64.repr (fe_limbs_of value)) ->
  region_ok (limb_rho value) layout m r (mkreg (u64_cells 0 (vars5 0)) false None).
Proof.
  intros [HBase [HAlign [HMax [HPerm HLoad]]]].
  apply region_u64.
  - exact HBase.
  - exact HAlign.
  - change (bas layout r + 40 <= Ptrofs.max_unsigned); exact HMax.
  - eapply Mem.perm_valid_block; apply (HPerm (bas layout r)); lia.
  - change (Mem.range_perm m (blk layout r) (bas layout r) (bas layout r + 40) Cur Readable).
    intros pos HRange; eapply Mem.perm_implies; [apply HPerm; exact HRange|constructor].
  - intros i x HNth; destruct (vars5_zero_nth i x HNth) as [HIndex HValue].
    rewrite HValue; split; [|reflexivity].
    cbn [den]; unfold limb_rho; apply HLoad.
    rewrite nth_error_map, (nth_error_nth' _ 0).
    + reflexivity.
    + change (i < 5)%nat; exact HIndex.
Qed.

Theorem get_b32_initial_rep_derived value bbytes byteofs bfe feofs m :
  0 <= byteofs -> byteofs + 32 <= Ptrofs.max_unsigned ->
  Mem.range_perm m bbytes byteofs (byteofs + 32) Cur Writable ->
  fe_at m bfe feofs (map Int64.repr (fe_limbs_of value)) ->
  bbytes <> bfe ->
  rep (limb_rho value) [(bbytes, byteofs); (bfe, feofs)]
    [mkreg (jet_secp_fe_b32.byte_undef 0 32) true None;
     mkreg (u64_cells 0 (vars5 0)) false None] m.
Proof.
  intros HBase HMax HPerm HFe HDifferent.
  apply two_region_rep_separate; [reflexivity|exact HDifferent| |].
  - apply region_b32_undefined_from_storage; assumption.
  - apply region_canonical_limbs_from_fe_at; exact HFe.
Qed.

Theorem eval_fe_get_b32_from_storage m b offset bf base value :
  0 <= value < 2 ^ 256 ->
  0 <= offset -> offset + 32 <= Ptrofs.max_unsigned ->
  Mem.range_perm m b offset (offset + 32) Cur Writable ->
  fe_at m bf base (map Int64.repr (fe_limbs_of value)) ->
  b <> bf ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_get_b32)
      [Vptr b (Ptrofs.repr offset); Vptr bf (Ptrofs.repr base)] E0 mf Vundef /\
    uint8_array_at mf b offset (map Int.repr (be_bytes value)) /\
    lframe (fun block pos =>
      ~ foot [(b, offset); (bf, base)]
        (map rshape [mkreg (jet_secp_fe_b32.byte_undef 0 32) true None;
                     mkreg (u64_cells 0 (vars5 0)) false None]) block pos) m mf.
Proof.
  intros HValue HBase HMax HPerm HFe HDifferent.
  apply eval_fe_get_b32_from_initial_regions; [exact HValue|].
  apply get_b32_initial_rep_derived; assumption.
Qed.
