(** Numeric interpretation of the actual read_fe symbolic run. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import AST Ctypes Integers Values Maps.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_zval C.jet_sx_zrep.
Require Import C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_secp_fe_math.
Require Import C.jet_secp_wrapper_run C.jet_secp_symbolic_substitution C.jet_secp_input_bytes.
Require Import C.jet_frame_bits.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition read_byte_shift (n : nat) : sx := XLv (S n).
Definition read_set_limbs : list sx :=
  map (fun c => match cval c with
    | Some x => sx_subst read_byte_shift x
    | None => XLc Int64.zero end) (cells0 sb_leaf).
Definition read_nv_variables (n : nat) : sx := nth n read_set_limbs (XLc Int64.zero).
Definition read_fe_condition input_edge edge : sx :=
  match read_fe_result input_edge edge with RIf c _ _ => c | _ => XIc Int.zero end.
Definition read_fe_nv_condition input_edge edge : sx :=
  match read_fe_result input_edge edge with RIf _ (RIf c _ _) _ => c | _ => XIc Int.zero end.
Definition read_fe_nv_true input_edge edge : list cell :=
  match read_fe_result input_edge edge with RIf _ (RIf _ (RDone state _) _) _ => cells0 state | _ => [] end.
Definition read_fe_nv_false input_edge edge : list cell :=
  match read_fe_result input_edge edge with RIf _ (RIf _ _ (RDone state _)) _ => cells0 state | _ => [] end.
Definition read_fe_no_normalize input_edge edge : list cell :=
  match read_fe_result input_edge edge with RIf _ _ (RDone state _) => cells0 state | _ => [] end.

Lemma read_fe_condition_from_set_b32 input_edge edge :
  read_fe_condition input_edge edge = XIz (sx_subst read_byte_shift sb_ret).
Proof. reflexivity. Qed.
Lemma read_fe_condition_from_normalizer input_edge edge :
  read_fe_nv_condition input_edge edge = sx_subst read_nv_variables nv_c.
Proof. reflexivity. Qed.
Lemma read_fe_nv_true_cells input_edge edge :
  read_fe_nv_true input_edge edge = map (cell_subst read_nv_variables) (cells0 nv_a).
Proof. reflexivity. Qed.
Lemma read_fe_nv_false_cells input_edge edge :
  read_fe_nv_false input_edge edge = map (cell_subst read_nv_variables) (cells0 nv_b).
Proof. reflexivity. Qed.
Lemma read_fe_no_normalize_cells input_edge edge :
  read_fe_no_normalize input_edge edge = map (cell_subst read_byte_shift) (cells0 sb_leaf).
Proof. reflexivity. Qed.

Definition read_bounds (n : nat) : Z * Z :=
  match n with O => (0, Int64.max_unsigned) | S _ => (0, 255) end.
Lemma read_fe_condition_checked input_edge edge :
  zb read_bounds (read_fe_condition input_edge edge) = Some (0, 1) /\
  isk KI (read_fe_condition input_edge edge) = true.
Proof. split; vm_compute; reflexivity. Qed.
Lemma read_fe_nv_condition_checked input_edge edge :
  zb read_bounds (read_fe_nv_condition input_edge edge) = Some (0, 1) /\
  isk KI (read_fe_nv_condition input_edge edge) = true.
Proof. split; vm_compute; reflexivity. Qed.
Lemma read_fe_nv_true_checked input_edge edge :
  zreg_okb read_bounds 0 (read_fe_nv_true input_edge edge) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma read_fe_nv_false_checked input_edge edge :
  zreg_okb read_bounds 0 (read_fe_nv_false input_edge edge) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma read_fe_no_normalize_checked input_edge edge :
  zreg_okb read_bounds 0 (read_fe_no_normalize input_edge edge) = true.
Proof. vm_compute; reflexivity. Qed.


Lemma read_rho_bounds bits rc : forall n,
  fst (read_bounds n) <= Int64.unsigned (read_fe_rho bits rc n) <= snd (read_bounds n).
Proof.
  intros [|n].
  - cbn [read_bounds read_fe_rho fst snd]; apply Int64.unsigned_range_2.
  - cbn [read_bounds read_fe_rho fst snd].
    rewrite Int64.unsigned_repr.
    + apply ifield_byte_bounds.
    + pose proof (ifield_byte_bounds bits (8 * n)).
      change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

Lemma read_shifted_input_value bits rc n :
  length bits = 256%nat ->
  zval (zrho (read_fe_rho bits rc)) (read_byte_shift n) = nth n (input_bytes 32 bits) 0.
Proof.
  intro HLength; change (Int64.unsigned (Int64.repr (ifield bits (8 * n) 8)) =
    nth n (input_bytes 32 bits) 0).
  rewrite Int64.unsigned_repr.
  - symmetry; apply input_bytes_nth_total; exact HLength.
  - pose proof (ifield_byte_bounds bits (8 * n)).
    change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

Lemma read_set_values bits rc :
  length bits = 256%nat ->
  map (zval (zrho (read_fe_rho bits rc))) read_set_limbs =
    fe_limbs_of (be_val (input_bytes 32 bits)).
Proof.
  intro HLength; unfold read_set_limbs; rewrite map_map.
  replace (map
    (fun c => zval (zrho (read_fe_rho bits rc))
      match cval c with Some x => sx_subst read_byte_shift x | None => XLc Int64.zero end)
    (cells0 sb_leaf)) with (zcells (fun n => nth n (input_bytes 32 bits) 0) (cells0 sb_leaf)).
  - apply (proj1 (sb_math (input_bytes 32 bits) (input_bytes_length 32 bits)
      (input_bytes_bounds 32 bits HLength))).
  - unfold zcells; apply map_ext; intros c; destruct (cval c) as [x|]; [|reflexivity].
    rewrite zval_sx_subst; apply zval_ext; intro n; symmetry; apply read_shifted_input_value; exact HLength.
Qed.

Lemma read_nv_variable_value bits rc n :
  length bits = 256%nat ->
  zval (zrho (read_fe_rho bits rc)) (read_nv_variables n) =
    nth n (fe_limbs_of (be_val (input_bytes 32 bits))) 0.
Proof.
  intro HLength; unfold read_nv_variables.
  rewrite <- (map_nth (zval (zrho (read_fe_rho bits rc))) read_set_limbs (XLc Int64.zero) n).
  rewrite read_set_values by exact HLength; reflexivity.
Qed.

Lemma read_set_return_value bits rc :
  length bits = 256%nat ->
  zval (zrho (read_fe_rho bits rc)) (sx_subst read_byte_shift sb_ret) =
    b2z (Z.ltb (be_val (input_bytes 32 bits)) feP).
Proof.
  intro HLength; rewrite zval_sx_subst.
  rewrite (zval_ext _ (fun n => nth n (input_bytes 32 bits) 0))
    by (intro n; apply read_shifted_input_value; exact HLength).
  apply (proj2 (sb_math (input_bytes 32 bits) (input_bytes_length 32 bits)
    (input_bytes_bounds 32 bits HLength))).
Qed.

Definition read_math_rho bits n : Z := nth n (fe_limbs_of (be_val (input_bytes 32 bits))) 0.
Lemma read_fe_invalid_condition bits rc input_edge edge layout :
  length bits = 256%nat ->
  truth (read_fe_rho bits rc) layout (read_fe_condition input_edge edge) =
    negb (Z.ltb (be_val (input_bytes 32 bits)) feP).
Proof.
  intro HLength.
  rewrite (truth_zval (read_fe_rho bits rc) read_bounds layout (read_rho_bounds bits rc)
    (read_fe_condition input_edge edge) 0 1
    (proj1 (read_fe_condition_checked input_edge edge))
    (proj2 (read_fe_condition_checked input_edge edge))).
  rewrite read_fe_condition_from_set_b32.
  change (negb (Z.eqb (b2z (Z.eqb
    (zval (zrho (read_fe_rho bits rc)) (sx_subst read_byte_shift sb_ret)) 0)) 0) =
      negb (Z.ltb (be_val (input_bytes 32 bits)) feP)).
  rewrite read_set_return_value by exact HLength.
  destruct (Z.ltb (be_val (input_bytes 32 bits)) feP); reflexivity.
Qed.
Lemma read_fe_normalizer_condition bits rc input_edge edge layout :
  length bits = 256%nat ->
  truth (read_fe_rho bits rc) layout (read_fe_nv_condition input_edge edge) =
    negb (Z.eqb (zval (read_math_rho bits) nv_c) 0).
Proof.
  intro HLength.
  rewrite (truth_zval (read_fe_rho bits rc) read_bounds layout (read_rho_bounds bits rc)
    (read_fe_nv_condition input_edge edge) 0 1
    (proj1 (read_fe_nv_condition_checked input_edge edge))
    (proj2 (read_fe_nv_condition_checked input_edge edge))).
  rewrite read_fe_condition_from_normalizer, zval_sx_subst.
  f_equal; f_equal; apply zval_ext; intro n; apply read_nv_variable_value; exact HLength.
Qed.
Lemma read_fe_nv_true_values bits rc input_edge edge :
  length bits = 256%nat ->
  zcells (zrho (read_fe_rho bits rc)) (read_fe_nv_true input_edge edge) =
    zcells (read_math_rho bits) (cells0 nv_a).
Proof.
  intro HLength; rewrite read_fe_nv_true_cells, zcells_cell_subst.
  apply zcells_ext; intro n; apply read_nv_variable_value; exact HLength.
Qed.
Lemma read_fe_nv_false_values bits rc input_edge edge :
  length bits = 256%nat ->
  zcells (zrho (read_fe_rho bits rc)) (read_fe_nv_false input_edge edge) =
    zcells (read_math_rho bits) (cells0 nv_b).
Proof.
  intro HLength; rewrite read_fe_nv_false_cells, zcells_cell_subst.
  apply zcells_ext; intro n; apply read_nv_variable_value; exact HLength.
Qed.
Lemma read_fe_no_normalize_values bits rc input_edge edge :
  length bits = 256%nat ->
  zcells (zrho (read_fe_rho bits rc)) (read_fe_no_normalize input_edge edge) =
    fe_limbs_of (be_val (input_bytes 32 bits)).
Proof.
  intro HLength; rewrite read_fe_no_normalize_cells, zcells_cell_subst.
  rewrite (zcells_ext _ (fun n => nth n (input_bytes 32 bits) 0))
    by (intro n; apply read_shifted_input_value; exact HLength).
  apply (proj1 (sb_math (input_bytes 32 bits) (input_bytes_length 32 bits)
    (input_bytes_bounds 32 bits HLength))).
Qed.

Fixpoint selected_cells rho layout rr : list cell :=
  match rr with
  | RDone state _ => cells0 state
  | RIf c a b => if truth rho layout c then selected_cells rho layout a else selected_cells rho layout b
  end.
Lemma selected_cells_rsel rho layout rr :
  cells0 (fst (rsel rho layout rr)) = selected_cells rho layout rr.
Proof.
  induction rr as [state outcome|condition a IHa b IHb]; cbn [rsel selected_cells].
  - reflexivity.
  - destruct (truth rho layout condition); assumption.
Qed.
Lemma read_fe_selected_cells rho layout input_edge edge :
  cells0 (fst (rsel rho layout (read_fe_result input_edge edge))) =
  if truth rho layout (read_fe_condition input_edge edge) then
    if truth rho layout (read_fe_nv_condition input_edge edge)
    then read_fe_nv_true input_edge edge else read_fe_nv_false input_edge edge
  else read_fe_no_normalize input_edge edge.
Proof. rewrite selected_cells_rsel; reflexivity. Qed.

Lemma input_bytes_256_range bits :
  length bits = 256%nat -> 0 <= be_val (input_bytes 32 bits) < 2 ^ 256.
Proof.
  intro HLength; rewrite input_bytes_value by exact HLength.
  pose proof (bits_val_range bits) as HRange; rewrite HLength in HRange; exact HRange.
Qed.
Lemma nvz_canonical_input_limbs W :
  0 <= W < 2 ^ 256 ->
  nvz_list (W mod 2 ^ 52) ((W / 2 ^ 52) mod 2 ^ 52)
    ((W / 2 ^ 104) mod 2 ^ 52) ((W / 2 ^ 156) mod 2 ^ 52) (W / 2 ^ 208) =
    fe_limbs_of (W mod feP).
Proof.
  intro HRange; destruct (fe_limbs_of_ok W HRange) as [HBounds HValue].
  assert (B0 : 0 <= W mod 2 ^ 52 <= 2 ^ 60) by (unfold fe_limbs_ok in HBounds; change (2^60) with 1152921504606846976; lia).
  assert (B1 : 0 <= (W / 2 ^ 52) mod 2 ^ 52 <= 2 ^ 60) by (unfold fe_limbs_ok in HBounds; change (2^60) with 1152921504606846976; lia).
  assert (B2 : 0 <= (W / 2 ^ 104) mod 2 ^ 52 <= 2 ^ 60) by (unfold fe_limbs_ok in HBounds; change (2^60) with 1152921504606846976; lia).
  assert (B3 : 0 <= (W / 2 ^ 156) mod 2 ^ 52 <= 2 ^ 60) by (unfold fe_limbs_ok in HBounds; change (2^60) with 1152921504606846976; lia).
  assert (B4 : 0 <= W / 2 ^ 208 <= 2 ^ 60) by (unfold fe_limbs_ok in HBounds; change (2^60) with 1152921504606846976; lia).
  pose proof (nvz_spec _ _ _ _ _ B0 B1 B2 B3 B4) as HSpec.
  unfold nvz_list.
  destruct (nvz _ _ _ _ _) as [[[[r0 r1] r2] r3] r4].
  destruct HSpec as [HOutput HMod].
  apply fe_limbs_unique; [exact HOutput|].
  rewrite HValue in HMod; exact HMod.
Qed.
Lemma zcells_cond (rho : nat -> Z) (c : bool) (a b : list cell) :
  zcells rho (if c then a else b) = if c then zcells rho a else zcells rho b.
Proof. destruct c; reflexivity. Qed.

Theorem read_fe_selected_numeric bits rc input_edge edge layout :
  length bits = 256%nat ->
  zcells (zrho (read_fe_rho bits rc))
    (cells0 (fst (rsel (read_fe_rho bits rc) layout (read_fe_result input_edge edge)))) =
    fe_limbs_of (be_val (input_bytes 32 bits) mod feP).
Proof.
  intro HLength; rewrite read_fe_selected_cells, zcells_cond.
  rewrite read_fe_invalid_condition by exact HLength.
  destruct (Z.ltb (be_val (input_bytes 32 bits)) feP) eqn:HValid; cbn [negb].
  - rewrite read_fe_no_normalize_values by exact HLength.
    rewrite Z.mod_small; [reflexivity|].
    apply Z.ltb_lt in HValid.
    pose proof (input_bytes_256_range bits HLength); lia.
  - rewrite zcells_cond, read_fe_normalizer_condition,
      read_fe_nv_true_values, read_fe_nv_false_values by exact HLength.
    set (W := be_val (input_bytes 32 bits)).
    change ((if negb (Z.eqb (zval
      (zrho5 (W mod 2 ^ 52) ((W / 2 ^ 52) mod 2 ^ 52)
        ((W / 2 ^ 104) mod 2 ^ 52) ((W / 2 ^ 156) mod 2 ^ 52) (W / 2 ^ 208)) nv_c) 0)
      then zcells (zrho5 (W mod 2 ^ 52) ((W / 2 ^ 52) mod 2 ^ 52)
        ((W / 2 ^ 104) mod 2 ^ 52) ((W / 2 ^ 156) mod 2 ^ 52) (W / 2 ^ 208)) (cells0 nv_a)
      else zcells (zrho5 (W mod 2 ^ 52) ((W / 2 ^ 52) mod 2 ^ 52)
        ((W / 2 ^ 104) mod 2 ^ 52) ((W / 2 ^ 156) mod 2 ^ 52) (W / 2 ^ 208)) (cells0 nv_b)) =
        fe_limbs_of (W mod feP)).
    rewrite <- nv_bridge; apply nvz_canonical_input_limbs.
    apply input_bytes_256_range; exact HLength.
Qed.

Require Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_encoding C.jet_input_layout.
Require Import C.jet_secp_canonical_normalize.
Theorem read_fe_selected_canonical (value : Ty.tySem (Word.Word 8)) rc input_edge edge layout :
  zcells (zrho (read_fe_rho (frame_input_word_bits value) rc))
    (cells0 (fst (rsel (read_fe_rho (frame_input_word_bits value) rc) layout
      (read_fe_result input_edge edge)))) =
    fe_limbs_of (@Word.ToZ.Theory.toZ (Word.WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)).
Proof.
  rewrite read_fe_selected_numeric by (rewrite frame_input_word_bits_length; reflexivity).
  rewrite input_bytes_word256_value, canonical_fe_normalize_numeric,
    canonical_field_order_matches_limb_model; reflexivity.
Qed.

Fixpoint all_leaf_fe_shape rr : Prop :=
  match rr with
  | RDone state _ =>
      nth_error (sregs state) 0 = Some (mkreg (cells0 state) true None) /\
      length (cells0 state) = 5%nat
  | RIf _ a b => all_leaf_fe_shape a /\ all_leaf_fe_shape b
  end.
Lemma all_leaf_fe_shape_selected rr :
  all_leaf_fe_shape rr -> forall rho layout,
    nth_error (sregs (fst (rsel rho layout rr))) 0 =
      Some (mkreg (cells0 (fst (rsel rho layout rr))) true None) /\
    length (cells0 (fst (rsel rho layout rr))) = 5%nat.
Proof.
  induction rr as [state outcome|condition a IHa b IHb]; cbn [all_leaf_fe_shape rsel].
  - intros H rho layout; exact H.
  - intros [HA HB] rho layout; destruct (truth rho layout condition); auto.
Qed.
Lemma read_fe_all_leaf_shape input_edge edge :
  all_leaf_fe_shape (read_fe_result input_edge edge).
Proof. split; [split; split; reflexivity|split; reflexivity]. Qed.
Lemma read_fe_selected_shape rho layout input_edge edge :
  nth_error (sregs (fst (rsel rho layout (read_fe_result input_edge edge)))) 0 =
    Some (mkreg (cells0 (fst (rsel rho layout (read_fe_result input_edge edge)))) true None) /\
  length (cells0 (fst (rsel rho layout (read_fe_result input_edge edge)))) = 5%nat.
Proof. apply all_leaf_fe_shape_selected; apply read_fe_all_leaf_shape. Qed.
Lemma read_fe_selected_checked rho layout input_edge edge :
  zreg_okb read_bounds 0
    (cells0 (fst (rsel rho layout (read_fe_result input_edge edge)))) = true.
Proof.
  rewrite read_fe_selected_cells.
  destruct (truth rho layout (read_fe_condition input_edge edge)).
  - destruct (truth rho layout (read_fe_nv_condition input_edge edge));
      [apply read_fe_nv_true_checked|apply read_fe_nv_false_checked].
  - apply read_fe_no_normalize_checked.
Qed.

From compcert Require Import Memory.
Require Import C.jet_sx_mem C.jet_sx_rep.
(** Representation lemma used on the postcondition of the proved Clight call. *)
Lemma read_fe_final_field_numeric m layout bits rc input_edge edge :
  length bits = 256%nat ->
  0 <= bas layout 0 -> (8 | bas layout 0) -> bas layout 0 + 40 <= Ptrofs.max_unsigned ->
  rep (read_fe_rho bits rc) layout
    (sregs (fst (rsel (read_fe_rho bits rc) (lay layout) (read_fe_result input_edge edge)))) m ->
  fe_at m (blk layout 0) (bas layout 0)
    (map Int64.repr (fe_limbs_of (be_val (input_bytes 32 bits) mod feP))).
Proof.
  intros HLength HBase HAlign HMax HRep.
  pose proof (read_fe_selected_shape (read_fe_rho bits rc) (lay layout) input_edge edge)
    as [HRegion HCellCount].
  destruct (rep_region _ _ _ _ _ _ HRep HRegion) as (_ & _ & _ & HCells & _).
  cbn [rcells rw] in HCells.
  destruct (zreg_load (read_fe_rho bits rc) read_bounds layout (read_rho_bounds bits rc)
    m 0 true (cells0 (fst (rsel (read_fe_rho bits rc) (lay layout)
      (read_fe_result input_edge edge)))) 0
    (read_fe_selected_checked (read_fe_rho bits rc) (lay layout) input_edge edge) HCells)
      as [HLoad HPerm].
  rewrite HCellCount in HPerm.
  rewrite read_fe_selected_numeric in HLoad by exact HLength.
  split; [exact HBase|]; split; [exact HAlign|]; split; [exact HMax|]; split.
  - intros pos HPos; apply HPerm; lia.
  - intros i x HNth; rewrite nth_error_map in HNth.
    destruct (nth_error (fe_limbs_of (be_val (input_bytes 32 bits) mod feP)) i)
      as [z|] eqn:HZ; [|discriminate].
    inversion HNth; subst x.
    rewrite <- (HLoad i z HZ); f_equal; lia.
Qed.
Lemma read_fe_final_field_canonical m layout (value : Ty.tySem (Word.Word 8)) rc input_edge edge :
  0 <= bas layout 0 -> (8 | bas layout 0) -> bas layout 0 + 40 <= Ptrofs.max_unsigned ->
  rep (read_fe_rho (frame_input_word_bits value) rc) layout
    (sregs (fst (rsel (read_fe_rho (frame_input_word_bits value) rc) (lay layout)
      (read_fe_result input_edge edge)))) m ->
  fe_at m (blk layout 0) (bas layout 0)
    (map Int64.repr
      (fe_limbs_of (@Word.ToZ.Theory.toZ (Word.WordToZ 8)
        (@canonical_fe_normalize Alg.CoreFunSem value)))).
Proof.
  intros HBase HAlign HMax HRep.
  rewrite canonical_fe_normalize_numeric, canonical_field_order_matches_limb_model,
    <- input_bytes_word256_value.
  apply read_fe_final_field_numeric with (rc := rc) (input_edge := input_edge) (edge := edge);
    try assumption.
  rewrite frame_input_word_bits_length; reflexivity.
Qed.

From compcert Require Import ClightBigstep Events.
Require Import C.jet_output_layout C.jet_secp_linkage C.jets_secp.
(** Whole original read_fe function, including read8s, temporary buffer and
    normalization. The caller must still construct its initial region/frame
    facts; this support theorem is not a registered jet equivalence. *)
Theorem eval_read_fe_against_canonical_program
    m0 bd dbase bw outedge cursor N bi edge rc (value : Ty.tySem (Word.Word 8)) outs0 cap
    m layout :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  0 <= bas layout 0 -> (8 | bas layout 0) -> bas layout 0 + 40 <= Ptrofs.max_unsigned ->
  rep (read_fe_rho (frame_input_word_bits value) rc) layout
    (read_fe_initial_regs bi (Ptrofs.repr edge)) m ->
  xsep (jet_secp_wrapper_run.read_ext m0 bd bw bi) layout ->
  jet_secp_wrapper_run.read_inv m0 bd dbase bw outedge cursor N bi rc outs0 cap
    (read_fe_rho (frame_input_word_bits value) rc) [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_read_fe)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))] E0 mf Vundef /\
    fe_at mf (blk layout 0) (bas layout 0)
      (map Int64.repr (fe_limbs_of
        (@Word.ToZ.Theory.toZ (Word.WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)))) /\
    jet_secp_wrapper_run.read_inv m0 bd dbase bw outedge cursor N bi rc outs0 cap
      (read_fe_rho (frame_input_word_bits value) rc) (read_fe_log bi (Ptrofs.repr edge)) mf /\
    lframe (frame (jet_secp_wrapper_run.read_ext m0 bd bw bi) layout (read_fe_initial_regs bi (Ptrofs.repr edge)) m) m mf.
Proof.
  intros HOutput HInput HCursor HMaxCursor HBase HAlign HMax HRep HSep HInv.
  assert (HLength : length (frame_input_word_bits value) = 256%nat).
  { rewrite frame_input_word_bits_length; reflexivity. }
  assert (HCursorMax : rc + Z.of_nat (length (frame_input_word_bits value)) <= Int64.max_unsigned).
  { rewrite HLength; exact HMaxCursor. }
  destruct (eval_read_fe_from_initial_regions m0 bd dbase bw outedge cursor N bi edge rc
    (frame_input_word_bits value) outs0 cap HOutput HInput HCursor HCursorMax HLength
    m layout HRep HSep HInv) as [mf [HExec [HFinal [HFinalInv HFrame]]]].
  exists mf; split; [exact HExec|]; split; [|split; assumption].
  apply read_fe_final_field_canonical with (rc := rc) (input_edge := bi) (edge := Ptrofs.repr edge);
    assumption.
Qed.
