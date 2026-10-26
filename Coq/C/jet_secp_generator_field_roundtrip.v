(** The original generator serialization span from the actual affine fields.
    Derive the private representation and byte round-trip internally. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Translate.
Require Import C.jet_toZ C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_frame_inv C.jet_output_layout
  C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_field_add_initial
  C.jet_secp_field_pair_multiply C.jet_secp_multiply_first_arithmetic
  C.jet_secp_square_columns C.jet_secp_rescale_literal C.jet_secp_multiply_checkpoint_columns
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_numeric
  C.jet_secp_generator_save_values C.jet_secp_generator_codec C.jet_secp_generator_load_write
  C.jet_secp_generator_roundtrip C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Simplicity.Translate.encode rescale_field_output.

Lemma generator_field_pair_bounds x y : square_input_bounds x -> square_input_bounds y ->
  forall i,(i<10)%nat -> Int64.unsigned (field_pair_valuation x y i)<=2^60.
Proof.
  intros X Y i Index;pose proof (field_pair_input_bounds x y X Y i Index) as Bound.
  destruct (orb (Nat.eqb i 4) (Nat.eqb i 9));lia.
Qed.

Lemma generator_field_pair_values x y (second:bool) :
  generator_save_value (field_pair_valuation x y) (if second then 5 else 0)=
    radix_value (if second then y else x) mod field_prime.
Proof.
  destruct second;rewrite radix_value_as_fe_val,field_prime_matches_normalizer;reflexivity.
Qed.

Lemma generator_field_pair_output x y :
  generator_loaded_output (generator_saved_bytes (field_pair_valuation x y) 0)
    (generator_saved_bytes (field_pair_valuation x y) 5)=
  (rescale_field_output x,rescale_field_output y).
Proof.
  unfold generator_loaded_output;f_equal;apply (toZ_injective (WordToZ 8));
    rewrite generator_saved_output_value,rescale_field_output_value.
  - exact (generator_field_pair_values x y false).
  - exact (generator_field_pair_values x y true).
Qed.

Theorem eval_generator_field_roundtrip m0 bd base bw edge cursor N bi (rc:Z) x y flag m br bg :
  write_frame_at m0 bd base bw edge cursor N -> 512<=N ->
  finv m0 bd base bw edge cursor N bi m false [] ->
  br<>bg -> square_input_bounds x -> square_input_bounds y ->
  fe_at m br 0 (words5 x) -> fe_at m br 40 (words5 y) ->
  Mem.load Mint32 m br 80=Some (Vint flag) ->
  Mem.range_perm m br 0 88 Cur Freeable -> Mem.range_perm m bg 0 64 Cur Freeable ->
  xsep (extA m0 bd bw bi) [(br,0);(bg,0)] -> exists ms ml mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_generator_save)
    [Vptr bg Ptrofs.zero;Vptr br Ptrofs.zero] E0 ms Vundef /\
  Clight2.eval_funcall secp_ge ms (Internal f_secp256k1_generator_load)
    [Vptr br Ptrofs.zero;Vptr bg Ptrofs.zero] E0 ml Vundef /\
  Clight2.eval_funcall secp_ge ml (Internal f_write_ge)
    [Vptr bd (Ptrofs.repr base);Vptr br Ptrofs.zero] E0 mf Vundef /\
  finv m0 bd base bw edge cursor N bi mf true
    (@Simplicity.Translate.encode (Ty.Prod (Word 8) (Word 8)) (rescale_field_output x,rescale_field_output y)) /\
  Mem.range_perm mf br 0 88 Cur Freeable /\ Mem.range_perm mf bg 0 64 Cur Freeable /\
  lframe (fun b _=>b<>br /\ b<>bg /\ ~extA m0 bd bw bi b) m mf /\ readonly_preserved m mf.
Proof.
  intros Output Cap Inv Separate BX BY X Y Flag FR FG External.
  assert (PX:fe_at m br 0 (field_values (field_pair_valuation x y) 0)) by
    (rewrite field_pair_left;exact X).
  assert (PY:fe_at m br 40 (field_values (field_pair_valuation x y) 5)) by
    (rewrite field_pair_right;exact Y).
  destruct (eval_generator_save_load_write m0 bd base bw edge cursor N bi rc
    (field_pair_valuation x y) flag m br bg Output Cap Inv Separate PX PY Flag FR FG External
    (generator_field_pair_bounds x y BX BY))
    as (ms & ml & mf & Save & Load & Write & Final & FRF & FGF & Frame & Readonly).
  rewrite generator_field_pair_output in Final.
  exists ms,ml,mf;repeat first [assumption|split].
Qed.
