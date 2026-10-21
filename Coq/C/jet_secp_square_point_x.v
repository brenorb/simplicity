(** Original square into X of an owned point, from a distinct private field.
    A 40-byte permission view is sufficient for execution; precise framing
    restores the full real 128-byte allocation and its untouched coordinates. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_sx_state C.jet_sx_rep C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math.
Require Import C.jet_secp_square_separate_layout C.jet_secp_square_separate_numeric
  C.jet_secp_square_separate_caller C.jet_secp_square_execution C.jet_secp_curve_frame
  C.jet_secp_square_columns C.jet_secp_square_numeric
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_multiply_checkpoint_columns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words.

Definition square_two_ranges (bout bin b : block) (pos : Z) :=
  ~((b=bout /\ 0<=pos<40) \/ (b=bin /\ 0<=pos<40)).

Lemma square_separate_foot bout bin b pos :
  foot [(bout,0);(bin,0)] (map rshape (separate_regs true (Some 40))) b pos ->
  (b=bout /\ 0<=pos<40) \/ (b=bin /\ 0<=pos<40).
Proof.
  intros (r & sh & d & ch & HN & HC & HB & HP).
  destruct r as [|[|r]].
  - left;split;[exact HB|].
    change (d<=pos<d+size_chunk ch) in HP.
    cbn [separate_regs map nth_error] in HN;injection HN as <-.
    cbn [rshape rcells rw rfree fst map cshape cofs cchunk] in HC.
    destruct HC as [HE|[HE|[HE|[HE|[HE|HE]]]]];try contradiction;
      inversion HE;subst;change (size_chunk Mint64) with 8 in HP;lia.
  - right;split;[exact HB|].
    change (d<=pos<d+size_chunk ch) in HP.
    cbn [separate_regs map nth_error] in HN;injection HN as <-.
    cbn [separate_input u64_cells rshape rcells rw rfree fst map cshape cofs cchunk] in HC.
    destruct HC as [HE|[HE|[HE|[HE|[HE|HE]]]]];try contradiction;
      inversion HE;subst;change (size_chunk Mint64) with 8 in HP;lia.
  - cbn [separate_regs map nth_error] in HN;destruct r;discriminate.
Qed.

Theorem eval_square_separate_precise w m bout bin :
  square_input_bounds w -> Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin 0 (words5 w) -> Mem.range_perm m bin 0 40 Cur Freeable -> bout<>bin ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bout 0 (words5 (square_words w)) /\ Mem.range_perm mf bout 0 40 Cur Freeable /\
  fe_at mf bin 0 (words5 w) /\ Mem.range_perm mf bin 0 40 Cur Freeable /\
  lframe (square_two_ranges bout bin) m mf.
Proof.
  intros HB HO HI HF HNe.
  destruct (eval_original_square_separate_numeric w [(bout,0);(bin,0)] m true (Some 40) HB
    (separate_square_initial_rep w m bout bin HO HI HF HNe))
    as (mf & HC & HP & HW & HV & HBounds & HL).
  destruct (separate_output_field w [(bout,0);(bin,0)] mf true (Some 40) HB HP) as [FO FOF].
  pose proof (rep_region _ _ _ mf 1 _ HP eq_refl) as HIn.
  pose proof (separate_input_field w [(bout,0);(bin,0)] mf 1 (Some 40) HIn) as FI.
  pose proof HIn as (_ & _ & _ & _ & _ & _ & FIF & _).
  exists mf;split;[exact HC|];split;[exact FO|];split;[exact FOF|];
    split;[exact FI|];split;[exact FIF|].
  eapply lframe_implies;[exact HL|]. intros b pos HOutside HB' HFoot.
  apply HOutside;exact (square_separate_foot bout bin b pos HFoot).
Qed.

Theorem eval_square_point_x w m ba bl :
  square_input_bounds w -> Mem.range_perm m ba 0 128 Cur Freeable ->
  fe_at m bl 0 (words5 w) -> Mem.range_perm m bl 0 40 Cur Freeable -> ba<>bl ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef /\
  fe_at mf ba 0 (words5 (square_words w)) /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
  fe_at mf bl 0 (words5 w) /\ Mem.range_perm mf bl 0 40 Cur Freeable /\
  radix_value (square_words w) mod feP=(radix_value w*radix_value w) mod feP /\
  square_input_bounds (square_words w) /\
  (forall i, (i<5)%nat -> Int64.unsigned (square_words w i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
  lframe (square_two_ranges ba bl) m mf.
Proof.
  intros HB HA HI HL HNe.
  assert (HA40 : Mem.range_perm m ba 0 40 Cur Freeable) by (intros pos HP;apply HA;lia).
  destruct (eval_square_separate_precise w m ba bl HB HA40 HI HL HNe)
    as (mf & HC & FO & FOF & FI & FIF & HF).
  assert (HValid : Mem.valid_block m ba) by (eapply Mem.perm_valid_block;apply (HA 0);lia).
  assert (HFull : Mem.range_perm mf ba 0 128 Cur Freeable).
  { intros pos HP;destruct (Z_lt_ge_dec pos 40).
    - apply FOF;lia.
    - apply (proj1 (proj2 HF));[exact HValid| |apply HA;exact HP].
      unfold square_two_ranges;intros [[_ HE]|[HE _]];[lia|congruence]. }
  exists mf;split;[exact HC|];split;[exact FO|];split;[exact HFull|];
    split;[exact FI|];split;[exact FIF|].
  split;[exact (square_output_numeric w HB)|];split;[apply square_result_reusable;exact HB|].
  split;[intros i HI';exact (proj2 (square_output_bounds w HB i HI'))|exact HF].
Qed.
