(** The existing literal-program mismatch witness, extended below with actual
    whole-public Clight execution on fresh initialized frames. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_secp_add_literal C.jet_secp_mixed_dispatch_literal C.jet_secp_literal_gej_predicate
 C.jet_secp_canonical_zero C.jet_secp_canonical_normalize C.jet_secp_curve_literal
 C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric C.jet_secp_literal_infinity
 C.jet_secp_negate_literal_contract C.jet_secp_square_execution C.jet_secp_multiply_literal_spec
 C.jet_secp_rescale_literal C.jet_secp_double_literal C.jet_secp_fe_math C.jet_secp_write_fe_wide_exec.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube literal_fe_negate
 literal_fe_multiply_int canonical_fe_is_zero canonical_fe_normalize literal_fe_one256
 literal_fe_zero256 literal_gej_double literal_gej_infinity literal_gej_is_infinity.

Lemma extended_ratio_equal_branch (ax ay az bx byword : Ty.tySem (Word 8)) :
 @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt ->
 @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)=inr tt ->
 @canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i ay az byword)=inr tt ->
 fst (@literal_gej_ge_add_ex Alg.CoreFunSem (((ax,ay),az),(bx,byword)))=ay.
Proof.
 intros HA HH HI.
 change (fst (@literal_gej_add_ex Alg.CoreFunSem
   (((ax,ay),az),((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt)))=ay).
 unfold literal_gej_add_ex.
 cbn -[literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube literal_fe_negate
  literal_fe_multiply_int canonical_fe_is_zero canonical_fe_normalize literal_fe_one256
  literal_fe_zero256 literal_gej_double literal_gej_infinity literal_gej_is_infinity].
 match goal with |- fst (match ?c with inl _ => _ | inr _ => _ end)=_ =>
   assert (HC : c=inl tt) by exact HA;rewrite HC end.
 match goal with |- fst (match ?c with inl _ => _ | inr _ => _ end)=_ =>
   assert (HC' : c=inl tt) by exact mixed_literal_one_finite;rewrite HC' end.
 match goal with |- fst (match ?c with inl _ => _ | inr _ => _ end)=_ =>
   assert (HC'' : c=inr tt) by exact HH;rewrite HC'' end.
 match goal with |- fst (match ?c with inl _ => _ | inr _ => _ end)=_ =>
   assert (HC''' : c=inr tt) by exact HI;rewrite HC''' end.
 reflexivity.
Qed.

Theorem extended_ratio_p_witness :
 @toZ (WordToZ 8) (fst (@literal_gej_ge_add_ex Alg.CoreFunSem
  (((@literal_fe_zero256 Alg.CoreFunSem tt,canonical_field_word),@literal_fe_one256 Alg.CoreFunSem tt),
   (@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt))))=canonical_field_order.
Proof.
 assert (HZ : @toZ (WordToZ 8) (@literal_fe_zero256 Alg.CoreFunSem tt)=0).
 { change (@toZ (WordToZ 8) (@Word.zero 8 Alg.CoreFunSem tt)=0);rewrite Word.zero_correct;reflexivity. }
 assert (HRH : @toZ (WordToZ 8) (mixed_literal_h (@literal_fe_zero256 Alg.CoreFunSem tt)
   (@literal_fe_one256 Alg.CoreFunSem tt) (@literal_fe_zero256 Alg.CoreFunSem tt)) mod feP=0).
 { rewrite mixed_literal_h_numeric,HZ,literal_fe_one256_value.
   change ((0 mod feP) mod feP=0);rewrite !Z.mod_0_l by (unfold feP,feR;lia);reflexivity. }
 assert (HRI : @toZ (WordToZ 8) (mixed_literal_i canonical_field_word
   (@literal_fe_one256 Alg.CoreFunSem tt) (@literal_fe_zero256 Alg.CoreFunSem tt)) mod feP=0).
 { rewrite mixed_literal_i_numeric,HZ,literal_fe_one256_value,canonical_field_word_value,canonical_field_order_matches_limb_model.
   change ((feP mod feP) mod feP=0);rewrite Z.mod_same,Z.mod_0_l by (unfold feP,feR;lia);reflexivity. }
 rewrite extended_ratio_equal_branch;[exact canonical_field_word_value| | |].
 - rewrite literal_gej_is_infinity_value;exact mixed_literal_one_finite.
 - pose proof (literal_curve_zero_numeric (mixed_literal_h (@literal_fe_zero256 Alg.CoreFunSem tt)
     (@literal_fe_one256 Alg.CoreFunSem tt) (@literal_fe_zero256 Alg.CoreFunSem tt))) as HH.
   rewrite HRH,Z.eqb_refl in HH.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h (@literal_fe_zero256 Alg.CoreFunSem tt)
     (@literal_fe_one256 Alg.CoreFunSem tt) (@literal_fe_zero256 Alg.CoreFunSem tt))) as [u|u];destruct u;
     [discriminate HH|reflexivity].
 - pose proof (literal_curve_zero_numeric (mixed_literal_i canonical_field_word
     (@literal_fe_one256 Alg.CoreFunSem tt) (@literal_fe_zero256 Alg.CoreFunSem tt))) as HI.
   rewrite HRI,Z.eqb_refl in HI.
   destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i canonical_field_word
     (@literal_fe_one256 Alg.CoreFunSem tt) (@literal_fe_zero256 Alg.CoreFunSem tt))) as [u|u];destruct u;
     [discriminate HI|reflexivity].
Qed.

Theorem extended_ratio_p_normalizes_to_zero :
 @toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem canonical_field_word)=0.
Proof.
 rewrite canonical_fe_normalize_numeric,canonical_field_word_value,Z.mod_same;
   [reflexivity|pose proof canonical_field_order_range;lia].
Qed.

Theorem extended_ratio_p_not_writer_output t0 t1 t2 t3 t4 :
 wide_fe_output t0 t1 t2 t3 t4<>canonical_field_word.
Proof.
 intro HE;apply (f_equal (@toZ (WordToZ 8))) in HE.
 rewrite wide_fe_output_value,canonical_field_word_value,canonical_field_order_matches_limb_model in HE.
 pose proof (Z.mod_pos_bound
   (fe_val (Integers.Int64.unsigned t0) (Integers.Int64.unsigned t1)
     (Integers.Int64.unsigned t2) (Integers.Int64.unsigned t3) (Integers.Int64.unsigned t4))
   feP ltac:(unfold feP,feR;lia)) as HB;lia.
Qed.

From Coq Require Import List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events Globalenvs.
Require Import Simplicity.Translate C.jet_encoding C.jet_frame_layout C.jet_output_layout C.jet_frame_inv
  C.jet_frame_constructible C.jet_secp_linkage C.jets_secp
  C.jet_secp_mixed_ex_public_call C.jet_secp_mixed_ex_public_rest C.jet_secp_square_spec_bridge
  C.jet_secp_multiply_input_input C.jet_secp_multiply_writer_bridge C.jet_secp_rescale_literal
  C.jet_secp_mixed_finite_return C.jet_secp_multiply_finish_product C.jet_secp_square_numeric
  C.jet_secp_multiply_normalize_bridge C.jet_secp_gej_negate_literal.
Import ListNotations Ctypes Values.
Local Opaque secp_ge Genv.init_mem jets_secp.prog Simplicity.Translate.encode.

Definition extended_ratio_input : Ty.tySem
  (Ty.Prod (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (Ty.Prod (Word 8) (Word 8))) :=
  (((@literal_fe_zero256 Alg.CoreFunSem tt,canonical_field_word),@literal_fe_one256 Alg.CoreFunSem tt),
    (@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt)).
Definition extended_ratio_actual_cells := mixed_ex_equal_output
  (@literal_fe_zero256 Alg.CoreFunSem tt) canonical_field_word (@literal_fe_one256 Alg.CoreFunSem tt).
Definition extended_ratio_literal_cells :=
  Simplicity.Translate.encode (@literal_gej_ge_add_ex Alg.CoreFunSem extended_ratio_input).

Lemma extended_zero_value : @toZ (WordToZ 8) (@literal_fe_zero256 Alg.CoreFunSem tt)=0.
Proof.
  change (@toZ (WordToZ 8) (@Word.zero 8 Alg.CoreFunSem tt)=0).
  rewrite Word.zero_correct;reflexivity.
Qed.

Lemma extended_ratio_reader_h_zero :
  radix_value (mixed_h_words (square_reader_rho (@literal_fe_zero256 Alg.CoreFunSem tt))
    (square_reader_rho (@literal_fe_one256 Alg.CoreFunSem tt))
    (square_reader_rho (@literal_fe_zero256 Alg.CoreFunSem tt))) mod feP=0.
Proof.
  apply Z.eqb_eq;rewrite mixed_h_reader_test,literal_curve_zero_numeric,mixed_literal_h_numeric,
    extended_zero_value,literal_fe_one256_value.
  change (Z.eqb ((0 mod feP) mod feP) 0=true).
  rewrite !Z.mod_0_l by (unfold feP,feR;lia);reflexivity.
Qed.

Lemma extended_ratio_reader_i_zero :
  radix_value (mixed_i_words (square_reader_rho canonical_field_word)
    (square_reader_rho (@literal_fe_one256 Alg.CoreFunSem tt))
    (square_reader_rho (@literal_fe_zero256 Alg.CoreFunSem tt))) mod feP=0.
Proof.
  apply Z.eqb_eq;rewrite mixed_i_reader_test,literal_curve_zero_numeric,mixed_literal_i_numeric,
    extended_zero_value,literal_fe_one256_value,canonical_field_word_value,canonical_field_order_matches_limb_model.
  change (Z.eqb ((feP mod feP) mod feP) 0=true).
  rewrite Z.mod_same,Z.mod_0_l by (unfold feP,feR;lia);reflexivity.
Qed.

Lemma extended_ratio_actual_value :
  @toZ (WordToZ 8) (rescale_field_output (square_reader_rho canonical_field_word))=0.
Proof.
  rewrite rescale_field_output_value,field_prime_matches_normalizer.
  unfold square_reader_rho;rewrite radix_limb_rho by apply normalized_value_range.
  unfold normalized_value;rewrite extended_ratio_p_normalizes_to_zero.
  rewrite Z.mod_0_l by (unfold feP,feR;lia);reflexivity.
Qed.

Lemma extended_ratio_actual_head : nth_error extended_ratio_actual_cells 0=Some (Some false).
Proof.
  unfold extended_ratio_actual_cells,mixed_ex_equal_output.
  rewrite nth_error_app1 by (rewrite Simplicity.Translate.encode_length;cbn;lia).
  rewrite encode_word,nth_error_map,nth_error_word_bits by (cbn;lia).
  rewrite extended_ratio_actual_value;reflexivity.
Qed.

Lemma extended_ratio_literal_head : nth_error extended_ratio_literal_cells 0=Some (Some true).
Proof.
  pose proof extended_ratio_p_witness as Value.
  unfold extended_ratio_literal_cells,extended_ratio_input.
  destruct (@literal_gej_ge_add_ex Alg.CoreFunSem
    (((@literal_fe_zero256 Alg.CoreFunSem tt,canonical_field_word),@literal_fe_one256 Alg.CoreFunSem tt),
      (@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt))) as (r & p) eqn:Out.
  change (@toZ (WordToZ 8) r=canonical_field_order) in Value.
  change (nth_error (Simplicity.Translate.encode r++Simplicity.Translate.encode p) 0=Some (Some true)).
  rewrite nth_error_app1 by (rewrite Simplicity.Translate.encode_length;cbn;lia).
  rewrite encode_word,nth_error_map,nth_error_word_bits by (cbn;lia).
  rewrite Value.
  change (Some (Some (Z.testbit canonical_field_order 255))=Some (Some true)).
  assert (Top : Z.testbit canonical_field_order 255=true) by (timeout 10 vm_compute;reflexivity).
  rewrite Top;reflexivity.
Qed.

Lemma extended_ratio_cells_differ : extended_ratio_actual_cells<>extended_ratio_literal_cells.
Proof.
  intro HE;apply (f_equal (fun xs=>nth_error xs 0)) in HE.
  rewrite extended_ratio_actual_head,extended_ratio_literal_head in HE;discriminate.
Qed.

Lemma extended_ratio_output_length : length extended_ratio_actual_cells=1024%nat.
Proof.
  unfold extended_ratio_actual_cells,mixed_ex_equal_output.
  rewrite !app_length,!Simplicity.Translate.encode_length;reflexivity.
Qed.

Lemma extended_ratio_output_conflict m bw edge cursor :
  frame_output_cells_at m bw edge cursor extended_ratio_actual_cells ->
  ~frame_output_cells_at m bw edge cursor extended_ratio_literal_cells.
Proof.
  intros Actual Literal.
  destruct (Actual 0%nat (Some false) extended_ratio_actual_head) as (_ & w & LW & BW).
  destruct (Literal 0%nat (Some true) extended_ratio_literal_head) as (_ & v & LV & BV).
  assert (w=v) by congruence;subst v;congruence.
Qed.

Require Import C.jet_secp_scalar_lambda_init_exists.

(** A real successful execution on fresh disjoint frames extending the actual
    program's initialized memory, whose first output bit contradicts the
    fixed literal program.  No caller or intermediate execution is assumed. *)
Theorem gej_ge_add_ex_public_counterexample env :
  exists minit m bd bs bi bw edge mf,
  Genv.init_mem jets_secp.prog=Some minit /\
  frame_base_valid 0 /\ (8|0) /\
  frame_fields_at m bs 0 bi edge 0 /\
  frame_input_cells_at m bi edge 0 (Simplicity.Translate.encode extended_ratio_input) /\
  write_frame_at m bd 0 bw 0 1024 1024 /\
  (bd<>bi /\ bd<>bw /\ bd<>bs /\ bi<>bw /\ bs<>bi /\ bs<>bw) /\
  (forall b, Mem.valid_block minit b ->
    Mem.valid_block m b /\ b<>bd /\ b<>bs /\ b<>bi /\ b<>bw /\
    (forall chunk ofs, Mem.load chunk m b ofs=Mem.load chunk minit b ofs) /\
    (forall ofs k p, Mem.perm m b ofs k p -> Mem.perm minit b ofs k p)) /\
  Clight2.eval_funcall secp_ge m (Internal f_simplicity_gej_ge_add_ex)
    [Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero;env] E0 mf (Vint Int.one) /\
  frame_fields_at mf bd 0 bw 0 0 /\
  frame_output_cells_at mf bw 0 1024 extended_ratio_actual_cells /\
  ~frame_output_cells_at mf bw 0 1024 extended_ratio_literal_cells.
Proof.
  destruct secp_initial_memory_exists as (minit & Init).
  destruct (jet_frames_constructible minit (Simplicity.Translate.encode extended_ratio_input) 1024)
    as (m & bd & bs & bi & bw & edge & Base & Align & Source & Input & Output & Sep & Old).
  - rewrite Simplicity.Translate.encode_length;change (1280<=18446744073709551615);lia.
  - change (0<=1024<=18446744073709551615);lia.
  - pose proof Input as FullInput.
    unfold extended_ratio_input in Input.
    rewrite (@point_encode_pair (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))
      (Ty.Prod (Word 8) (Word 8))) in Input.
    rewrite (@point_encode_pair (Ty.Prod (Word 8) (Word 8)) (Word 8)),
      !(@point_encode_pair (Word 8) (Word 8)) in Input.
    rewrite !frame_input_cells_at_app,!app_length,!encode_word_length in Input.
    destruct Input as (((HX & HY) & HZ) & HU & HV).
    change (frame_input_cells_at m bi edge 256 (Simplicity.Translate.encode canonical_field_word)) in HY.
    change (frame_input_cells_at m bi edge 512 (Simplicity.Translate.encode (@literal_fe_one256 Alg.CoreFunSem tt))) in HZ.
    change (frame_input_cells_at m bi edge 768 (Simplicity.Translate.encode (@literal_fe_zero256 Alg.CoreFunSem tt))) in HU.
    change (frame_input_cells_at m bi edge 1024 (Simplicity.Translate.encode (@literal_fe_zero256 Alg.CoreFunSem tt))) in HV.
    rewrite encode_word in HX,HY,HZ,HU,HV.
    destruct (eval_gej_ge_add_ex_equal_public env m bd 0 bs 0 bw 0 1024 1024 bi edge 0
      (@literal_fe_zero256 Alg.CoreFunSem tt) canonical_field_word (@literal_fe_one256 Alg.CoreFunSem tt)
      (@literal_fe_zero256 Alg.CoreFunSem tt) (@literal_fe_zero256 Alg.CoreFunSem tt)
      Output ltac:(lia) Base Align Source HX HY HZ HU HV ltac:(lia)
      ltac:(change (1280<=18446744073709551615);lia)
      mixed_literal_one_finite extended_ratio_reader_h_zero extended_ratio_reader_i_zero)
      as (mf & Call & Final & Frame).
    change (finv m bd 0 bw 0 1024 1024 bi mf true extended_ratio_actual_cells) in Final.
    destruct Final as (Valid & Output0 & Len & (Cells & Prefix & Fields & Loads & Perms) & Written).
    rewrite extended_ratio_output_length in Fields;change (frame_fields_at mf bd 0 bw 0 0) in Fields.
    exists minit,m,bd,bs,bi,bw,edge,mf.
    split;[exact Init|];split;[exact Base|];split;[exact Align|];split;[exact Source|].
    split;[exact FullInput|];split;[exact Output|];split;[exact Sep|];split;[exact Old|];split;[exact Call|].
    split;[exact Fields|];split;[exact Cells|].
    exact (extended_ratio_output_conflict mf bw 0 1024 Cells).
Qed.
