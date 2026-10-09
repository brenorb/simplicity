(** Derive the original initializer and zero coordinates from initial point storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events Values Maps.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv.
Require Import C.jet_secp_fe_clear_memory C.jet_secp_gej_infinity_body.
Require Import C.jet_secp_gej_infinity_flag_memory.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma zero_fe_at_preserved m mf b base :
  fe_at m b base (repeat Int64.zero 5) ->
  (forall b' ofs k p, Mem.perm mf b' ofs k p <-> Mem.perm m b' ofs k p) ->
  (forall i, (i < 5)%nat ->
    Mem.load Mint64 mf b (base + 8 * Z.of_nat i) =
    Mem.load Mint64 m b (base + 8 * Z.of_nat i)) ->
  fe_at mf b base (repeat Int64.zero 5).
Proof.
  intros (HB & HA & HM & HP & HL) HE HF.
  split; [exact HB|]. split; [exact HA|]. split; [exact HM|]. split.
  - intros ofs HOfs. apply (proj2 (HE b ofs Cur Writable)); apply HP; exact HOfs.
  - intros i x HI.
    assert (HIndex : (i < 5)%nat).
    { rewrite <- (repeat_length Int64.zero 5). apply (proj1 (nth_error_Some _ _)); rewrite HI; discriminate. }
    rewrite HF by exact HIndex; apply HL; exact HI.
Qed.

Theorem eval_gej_infinity_initializer_owned m b base :
  0 <= base -> (8 | base) -> base + 128 <= Ptrofs.max_unsigned ->
  Mem.range_perm m b base (base + 128) Cur Writable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_set_infinity)
      [Vptr b (Ptrofs.repr base)] E0 mf Vundef /\
    fe_at mf b base (repeat Int64.zero 5) /\
    fe_at mf b (base + 40) (repeat Int64.zero 5) /\
    fe_at mf b (base + 80) (repeat Int64.zero 5) /\
    Mem.load Mint32 mf b (base + 120) = Some (Vint Int.one) /\
    (forall chunk b' ofs,
      b' <> b \/ ofs + size_chunk chunk <= base \/ base + 128 <= ofs ->
      Mem.load chunk mf b' ofs = Mem.load chunk m b' ofs) /\
    (forall b' ofs k p, Mem.perm mf b' ofs k p <-> Mem.perm m b' ofs k p) /\
    (forall b', Mem.valid_block m b' -> Mem.valid_block mf b').
Proof.
  intros HB HA HM HP.
  assert (HR : (gej_infinity_env b base)!_r = Some (Vptr b (Ptrofs.repr base))).
  { unfold gej_infinity_env; apply PTree.gss. }
  destruct (exec_gej_infinity_flag_owned (gej_infinity_env b base) m b base HB HA HM HR HP)
    as (mi & HFlag & HFlagLoad & HFlagFrame & HFlagPerm & HFlagValid).
  assert (HPi : Mem.range_perm mi b base (base + 40) Cur Writable).
  { intros ofs HOfs. apply (proj2 (HFlagPerm b ofs Cur Writable)); apply HP; lia. }
  destruct (eval_fe_clear_owned mi b base HB HA ltac:(lia) HPi)
    as (mx & HX & HFieldX & HFrameX & HPermX & HValidX).
  assert (HA40 : (8 | base + 40)).
  { destruct HA as [k HK]; exists (k + 5); lia. }
  assert (HPx : Mem.range_perm mx b (base + 40) (base + 40 + 40) Cur Writable).
  { intros ofs HOfs. apply (proj2 (HPermX b ofs Cur Writable)).
    apply (proj2 (HFlagPerm b ofs Cur Writable)); apply HP; lia. }
  destruct (eval_fe_clear_owned mx b (base + 40) ltac:(lia) HA40 ltac:(lia) HPx)
    as (my & HY & HFieldY & HFrameY & HPermY & HValidY).
  assert (HA80 : (8 | base + 80)).
  { destruct HA as [k HK]; exists (k + 10); lia. }
  assert (HPy : Mem.range_perm my b (base + 80) (base + 80 + 40) Cur Writable).
  { intros ofs HOfs. apply (proj2 (HPermY b ofs Cur Writable)).
    apply (proj2 (HPermX b ofs Cur Writable)).
    apply (proj2 (HFlagPerm b ofs Cur Writable)); apply HP; lia. }
  destruct (eval_fe_clear_owned my b (base + 80) ltac:(lia) HA80 ltac:(lia) HPy)
    as (mf & HZ & HFieldZ & HFrameZ & HPermZ & HValidZ).
  assert (HXY : fe_at my b base (repeat Int64.zero 5)).
  { eapply zero_fe_at_preserved; [exact HFieldX|exact HPermY|].
    intros i HI. apply HFrameY. right; left. change (size_chunk Mint64) with 8.
    pose proof (Nat2Z.is_nonneg i). assert (Z.of_nat i < 5) by lia; lia. }
  assert (HXF : fe_at mf b base (repeat Int64.zero 5)).
  { eapply zero_fe_at_preserved; [exact HXY|exact HPermZ|].
    intros i HI. apply HFrameZ. right; left. change (size_chunk Mint64) with 8.
    pose proof (Nat2Z.is_nonneg i). assert (Z.of_nat i < 5) by lia; lia. }
  assert (HYF : fe_at mf b (base + 40) (repeat Int64.zero 5)).
  { eapply zero_fe_at_preserved; [exact HFieldY|exact HPermZ|].
    intros i HI. apply HFrameZ. right; left. change (size_chunk Mint64) with 8.
    pose proof (Nat2Z.is_nonneg i). assert (Z.of_nat i < 5) by lia; lia. }
  exists mf; split.
  - eapply eval_gej_infinity_initializer_from_calls with (mi := mi) (mx := mx) (my := my);
      try eassumption.
    replace (base + 0) with base by lia; exact HX.
  - split; [exact HXF|]. split; [exact HYF|]. split; [exact HFieldZ|]. split.
    + rewrite HFrameZ by (right;right;lia).
      rewrite HFrameY by (right;right;lia).
      rewrite HFrameX by (right;right;lia). exact HFlagLoad.
    + split.
      * intros chunk b' ofs HOther.
        rewrite HFrameZ by (destruct HOther as [H|[H|H]];
          [left;exact H|right;left;lia|right;right;lia]).
        rewrite HFrameY by (destruct HOther as [H|[H|H]];
          [left;exact H|right;left;lia|right;right;lia]).
        rewrite HFrameX by (destruct HOther as [H|[H|H]];
          [left;exact H|right;left;lia|right;right;lia]).
        apply HFlagFrame. destruct HOther as [H|[H|H]];
          [left;exact H|right;left;lia|right;right;lia].
      * split.
        -- intros b' ofs k p. rewrite HPermZ, HPermY, HPermX, HFlagPerm; reflexivity.
        -- intros b' HV. apply HValidZ, HValidY, HValidX, HFlagValid; exact HV.
Qed.
Print Assumptions eval_gej_infinity_initializer_owned.
