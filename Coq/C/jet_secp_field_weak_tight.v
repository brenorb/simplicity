(** Actual weak normalization on a private field with positioned limbs.
    Reuse its execution and carry identity; do not assume the call or result. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_field_add_initial C.jet_secp_multiply_normalize_bridge C.jet_secp_curve_weak
  C.jet_secp_point_weak_values C.jet_secp_curve_frame C.jet_secp_square_spec_bridge
  C.jet_secp_point_field_bridge C.jet_secp_multiply_input_input C.jet_secp_b32_exec C.jet_secp_local_regions.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition weak_shift_words (w : nat -> int64) n := match n with
  | O => Int64.zero | S i => w i end.
Lemma weak_shift_values w : field_values (weak_shift_words w) 1=words5 w.
Proof. reflexivity. Qed.

Theorem eval_field_weak_tight w m b :
  fe_limbs_ok (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
    (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat)) ->
  fe_at m b 0 (words5 w) -> Mem.range_perm m b 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_weak)
    [Vptr b Ptrofs.zero] E0 mf Vundef /\
  fe_at mf b 0 (words5 w) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
  lframe (fun b' _=>b'<>b) m mf.
Proof.
  intros HB HF HP.
  assert (HBound : forall n, (1<=n<=5)%nat -> Int64.unsigned (weak_shift_words w n)<=2^60).
  { intros n HN;unfold fe_limbs_ok in HB;destruct HB as (B0 & B1 & B2 & B3 & B4).
    do 6 (destruct n as [|n];[cbn [weak_shift_words];try lia|]);lia. }
  rewrite <-weak_shift_values in HF.
  destruct (eval_curve_weak_owned (weak_shift_words w) m b HF HP HBound)
    as (mf & HC & HO & HFree & HL).
  assert (HMath : curve_weak_math
    (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat)) (Int64.unsigned (w 2%nat))
    (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat))=
    (Int64.unsigned (w 0%nat),Int64.unsigned (w 1%nat),Int64.unsigned (w 2%nat),
     Int64.unsigned (w 3%nat),Int64.unsigned (w 4%nat))).
  { apply point_weak_math_positioned_identity;exact HB. }
  unfold curve_weak_math_list in HO;cbn [weak_shift_words] in HO.
  rewrite HMath in HO;cbn in HO;rewrite !Int64.repr_unsigned in HO.
  exists mf;split;[exact HC|];split;[exact HO|];split;[exact HFree|].
  eapply curve_frame_one with (regs:=local_write_initial_regs);[reflexivity|exact HL].
Qed.

Lemma square_reader_positioned x :
  fe_limbs_ok (Int64.unsigned (square_reader_rho x 0%nat))
    (Int64.unsigned (square_reader_rho x 1%nat)) (Int64.unsigned (square_reader_rho x 2%nat))
    (Int64.unsigned (square_reader_rho x 3%nat)) (Int64.unsigned (square_reader_rho x 4%nat)).
Proof.
  exact (proj1 (point_reader_limb_model (normalized_value x) (normalized_value_range x))).
Qed.
