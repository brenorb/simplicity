(** Reusable loose-operand contract for actual point-coordinate fe_mul calls.
    The 56/52-bit inputs include the 52/49-bit outputs of earlier calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_state C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_checkpoint_columns C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_square_columns C.jet_secp_point_write_run C.jet_secp_point_mul_run C.jet_secp_point_mul_storage.
Require Import C.jet_secp_field_mul_word_math C.jet_secp_field_mul_word_model.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque fm_t0 fm_t1 fm_t2 fm_t3 fm_t4 fm_rho secp_ge.

Lemma field_operand_from_bounds w : square_input_bounds w ->
  field_mul_operand_ok (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
    (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat)).
Proof.
  intro HB.
  pose proof (HB 0%nat ltac:(lia)); pose proof (HB 1%nat ltac:(lia));
  pose proof (HB 2%nat ltac:(lia)); pose proof (HB 3%nat ltac:(lia)); pose proof (HB 4%nat ltac:(lia)).
  pose proof (Int64.unsigned_range (w 0%nat)); pose proof (Int64.unsigned_range (w 1%nat));
  pose proof (Int64.unsigned_range (w 2%nat)); pose proof (Int64.unsigned_range (w 3%nat));
  pose proof (Int64.unsigned_range (w 4%nat)).
  unfold field_mul_operand_ok; cbn [Nat.eqb] in *; repeat split; lia.
Qed.

Lemma radix_value_as_fe_val w : radix_value w = fe_val
  (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat)) (Int64.unsigned (w 2%nat))
  (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat)).
Proof. unfold radix_value, fe_val, radix; ring. Qed.

Theorem point_mul_value_and_bounds a b : square_input_bounds a -> square_input_bounds b ->
  radix_value (point_mul_words a b) mod field_prime = (radix_value a * radix_value b) mod field_prime /\
  square_input_bounds (point_mul_words a b).
Proof.
  intros HA HB.
  destruct (fm_mul_values (a 0%nat) (a 1%nat) (a 2%nat) (a 3%nat) (a 4%nat)
    (b 0%nat) (b 1%nat) (b 2%nat) (b 3%nat) (b 4%nat)
    (field_operand_from_bounds a HA) (field_operand_from_bounds b HB)) as (B0 & B1 & B2 & B3 & B4 & HV).
  split.
  - rewrite !radix_value_as_fe_val; exact HV.
  - intros i HI; destruct i as [|[|[|[|[|i]]]]]; try lia;
      cbn [point_mul_words nth Nat.eqb]; lia.
Qed.

Theorem eval_point_mul_numeric k a b m bp bs :
  square_input_bounds a -> square_input_bounds b -> bp <> bs ->
  fe_at m bp (point_coordinate_offset k) (words5 a) -> Mem.range_perm m bp 0 128 Cur Freeable ->
  fe_at m bs 0 (words5 b) -> Mem.range_perm m bs 0 40 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
      [Vptr bp (Ptrofs.repr (point_coordinate_offset k));
       Vptr bp (Ptrofs.repr (point_coordinate_offset k));Vptr bs Ptrofs.zero] E0 mf Vundef /\
    fe_at mf bp (point_coordinate_offset k) (words5 (point_mul_words a b)) /\
    Mem.range_perm mf bp 0 128 Cur Freeable /\ fe_at mf bs 0 (words5 b) /\
    Mem.range_perm mf bs 0 40 Cur Freeable /\
    radix_value (point_mul_words a b) mod field_prime = (radix_value a * radix_value b) mod field_prime /\
    square_input_bounds (point_mul_words a b) /\
    lframe (fun bx pos => ~ foot [(bp,0);(bs,0)] (map rshape (point_mul_regs k)) bx pos) m mf.
Proof.
  intros HA HB HNe HField HFree HScalar HFreeS.
  destruct (eval_point_mul_from_storage k a b m bp bs HNe HField HFree HScalar HFreeS)
    as (mf & HC & HF & HFP & HS & HFS & HFrame).
  destruct (point_mul_value_and_bounds a b HA HB) as [HV HBounds].
  exists mf; split; [exact HC|]; split; [exact HF|]; split; [exact HFP|].
  split; [exact HS|]; split; [exact HFS|]; split; [exact HV|]; split; assumption.
Qed.
