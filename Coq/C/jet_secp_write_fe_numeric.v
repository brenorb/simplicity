(** Numeric interpretation of the unchanged write_fe Clight wrapper. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import AST Ctypes Integers Values Maps.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_zval C.jet_sx_zrep.
Require Import C.jet_write8_sequence C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_secp_fe_math.
Require Import C.jet_secp_write_fe_wrapper C.jet_secp_symbolic_substitution.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition write_limb_shift (n : nat) : sx := XLv (S n).
Definition write_normalized_variables state n : sx :=
  nth n (map (fun c => sx_subst write_limb_shift (cell_sx c)) (cells0 state)) (XLc Int64.zero).
Definition write_fe_condition bd base : sx :=
  match write_fe_result bd base with RIf c _ _ => c | _ => XIc Int.zero end.
Definition write_fe_true_event bd base : event :=
  match write_fe_result bd base with RIf _ (RDone state _) _ =>
    hd (mkev tWR8 6 0 []) (slog state) | _ => mkev tWR8 6 0 [] end.
Definition write_fe_false_event bd base : event :=
  match write_fe_result bd base with RIf _ _ (RDone state _) =>
    hd (mkev tWR8 6 0 []) (slog state) | _ => mkev tWR8 6 0 [] end.
Definition write_fe_true_bytes bd base := tl (eargs (write_fe_true_event bd base)).
Definition write_fe_false_bytes bd base := tl (eargs (write_fe_false_event bd base)).
Lemma write_fe_condition_from_normalizer bd base :
  write_fe_condition bd base = sx_subst write_limb_shift nv_c.
Proof. reflexivity. Qed.
Lemma write_fe_true_bytes_from_get_b32 bd base :
  write_fe_true_bytes bd base =
    map (sx_subst (write_normalized_variables nv_a)) (map cell_sx (cells0 gb_leaf)).
Proof. reflexivity. Qed.
Lemma write_fe_false_bytes_from_get_b32 bd base :
  write_fe_false_bytes bd base =
    map (sx_subst (write_normalized_variables nv_b)) (map cell_sx (cells0 gb_leaf)).
Proof. reflexivity. Qed.
Definition write_bounds n : Z * Z :=
  match n with O => (0, Int64.max_unsigned) | S _ => (0, 2 ^ 52 - 1) end.
Lemma write_fe_condition_checked bd base :
  zb write_bounds (write_fe_condition bd base) = Some (0, 1) /\
  isk KI (write_fe_condition bd base) = true.
Proof. split; vm_compute; reflexivity. Qed.
Lemma write_fe_true_bytes_checked bd base :
  Forall (fun x => zb write_bounds x = Some (0, 255) /\ isk KI x = true)
    (write_fe_true_bytes bd base).
Proof. repeat constructor; vm_compute; reflexivity. Qed.
Lemma write_fe_false_bytes_checked bd base :
  Forall (fun x => zb write_bounds x = Some (0, 255) /\ isk KI x = true)
    (write_fe_false_bytes bd base).
Proof. repeat constructor; vm_compute; reflexivity. Qed.

Require Import C.jet_secp_b32_exec C.jet_secp_read_fe_numeric.
Definition write_fe_rho value rc n : int64 :=
  match n with O => Int64.repr rc | S j => limb_rho value j end.
Definition write_math_rho value n : Z := nth n (fe_limbs_of value) 0.
Lemma write_rho_bounds value rc :
  0 <= value < 2 ^ 256 -> forall n,
  fst (write_bounds n) <= Int64.unsigned (write_fe_rho value rc n) <= snd (write_bounds n).
Proof.
  intros HValue [|n].
  - apply Int64.unsigned_range_2.
  - change (0 <= Int64.unsigned (limb_rho value n) <= 2 ^ 52 - 1).
    rewrite limb_rho_unsigned by exact HValue.
    apply nth_limb_52_bound; apply limb_list_52_bound; exact HValue.
Qed.
Lemma write_shifted_limb_value value rc n :
  0 <= value < 2 ^ 256 ->
  zval (zrho (write_fe_rho value rc)) (write_limb_shift n) = write_math_rho value n.
Proof. intro HValue; apply limb_rho_unsigned; exact HValue. Qed.
Lemma write_normalized_values value rc state :
  0 <= value < 2 ^ 256 ->
  map (zval (zrho (write_fe_rho value rc)))
    (map (fun c => sx_subst write_limb_shift (cell_sx c)) (cells0 state)) =
    zcells (write_math_rho value) (cells0 state).
Proof.
  intro HValue; rewrite map_map; unfold zcells; apply map_ext; intro c.
  destruct (cval c) as [x|] eqn:EC.
  - unfold cell_sx; rewrite EC, zval_sx_subst.
    apply zval_ext; intro n; apply write_shifted_limb_value; exact HValue.
  - unfold cell_sx; rewrite EC; reflexivity.
Qed.
Lemma write_normalized_variable_value value rc state n :
  0 <= value < 2 ^ 256 ->
  zval (zrho (write_fe_rho value rc)) (write_normalized_variables state n) =
    nth n (zcells (write_math_rho value) (cells0 state)) 0.
Proof.
  intro HValue; unfold write_normalized_variables.
  rewrite <- (map_nth (zval (zrho (write_fe_rho value rc)))
    (map (fun c => sx_subst write_limb_shift (cell_sx c)) (cells0 state)) (XLc Int64.zero) n).
  rewrite write_normalized_values by exact HValue; reflexivity.
Qed.
Lemma write_fe_normalizer_condition value rc bd base layout :
  0 <= value < 2 ^ 256 ->
  truth (write_fe_rho value rc) layout (write_fe_condition bd base) =
    negb (Z.eqb (zval (write_math_rho value) nv_c) 0).
Proof.
  intro HValue.
  rewrite (truth_zval (write_fe_rho value rc) write_bounds layout (write_rho_bounds value rc HValue)
    (write_fe_condition bd base) 0 1
    (proj1 (write_fe_condition_checked bd base)) (proj2 (write_fe_condition_checked bd base))).
  rewrite write_fe_condition_from_normalizer, zval_sx_subst.
  f_equal; f_equal; apply zval_ext; intro n; apply write_shifted_limb_value; exact HValue.
Qed.
Lemma write_get_b32_substituted_value value rc state :
  0 <= value < 2 ^ 256 ->
  map (zval (zrho (write_fe_rho value rc)))
    (map (sx_subst (write_normalized_variables state)) (map cell_sx (cells0 gb_leaf))) =
  zcells (fun n => nth n (zcells (write_math_rho value) (cells0 state)) 0) (cells0 gb_leaf).
Proof.
  intro HValue; rewrite !map_map; unfold zcells at 2; apply map_ext; intro c.
  destruct (cval c) as [x|] eqn:EC.
  - unfold cell_sx; rewrite EC, zval_sx_subst.
    apply zval_ext; intro n; apply write_normalized_variable_value; exact HValue.
  - unfold cell_sx; rewrite EC; reflexivity.
Qed.

Definition write_fe_selected_bytes rho layout bd base : list sx :=
  if truth rho layout (write_fe_condition bd base)
  then write_fe_true_bytes bd base else write_fe_false_bytes bd base.
Definition write_normalized_limbs value : list Z :=
  if negb (Z.eqb (zval (write_math_rho value) nv_c) 0)
  then zcells (write_math_rho value) (cells0 nv_a)
  else zcells (write_math_rho value) (cells0 nv_b).
Lemma write_normalized_limbs_canonical value :
  0 <= value < 2 ^ 256 -> write_normalized_limbs value = fe_limbs_of (value mod feP).
Proof.
  intro HValue; unfold write_normalized_limbs, write_math_rho.
  change ((if negb (Z.eqb (zval (zrho5 (value mod 2 ^ 52)
    ((value / 2 ^ 52) mod 2 ^ 52) ((value / 2 ^ 104) mod 2 ^ 52)
    ((value / 2 ^ 156) mod 2 ^ 52) (value / 2 ^ 208)) nv_c) 0)
    then zcells (zrho5 (value mod 2 ^ 52) ((value / 2 ^ 52) mod 2 ^ 52)
      ((value / 2 ^ 104) mod 2 ^ 52) ((value / 2 ^ 156) mod 2 ^ 52) (value / 2 ^ 208)) (cells0 nv_a)
    else zcells (zrho5 (value mod 2 ^ 52) ((value / 2 ^ 52) mod 2 ^ 52)
      ((value / 2 ^ 104) mod 2 ^ 52) ((value / 2 ^ 156) mod 2 ^ 52) (value / 2 ^ 208)) (cells0 nv_b)) =
    fe_limbs_of (value mod feP)).
  rewrite <- nv_bridge.
  apply C.jet_secp_read_fe_numeric.nvz_canonical_input_limbs; exact HValue.
Qed.

Lemma write_get_b32_selected_value value rc bd base layout :
  0 <= value < 2 ^ 256 ->
  map (zval (zrho (write_fe_rho value rc)))
    (write_fe_selected_bytes (write_fe_rho value rc) layout bd base) =
  zcells (fun n => nth n (write_normalized_limbs value) 0) (cells0 gb_leaf).
Proof.
  intro HValue; unfold write_fe_selected_bytes.
  rewrite write_fe_normalizer_condition by exact HValue.
  unfold write_normalized_limbs.
  destruct (negb (Z.eqb (zval (write_math_rho value) nv_c) 0)).
  - rewrite write_fe_true_bytes_from_get_b32; apply write_get_b32_substituted_value; exact HValue.
  - rewrite write_fe_false_bytes_from_get_b32; apply write_get_b32_substituted_value; exact HValue.
Qed.
Lemma field_mod_256_range value : 0 <= value mod feP < 2 ^ 256.
Proof.
  assert (HP : 0 < feP < 2 ^ 256) by (unfold feP, feR; lia).
  pose proof (Z.mod_pos_bound value feP ltac:(lia)); lia.
Qed.
Theorem write_fe_selected_bytes_numeric value rc bd base layout :
  0 <= value < 2 ^ 256 ->
  map (zval (zrho (write_fe_rho value rc)))
    (write_fe_selected_bytes (write_fe_rho value rc) layout bd base) = be_bytes (value mod feP).
Proof.
  intro HValue; rewrite write_get_b32_selected_value, write_normalized_limbs_canonical by exact HValue.
  apply gb_math; apply field_mod_256_range.
Qed.
Lemma write_fe_selected_bytes_checked rho bd base layout :
  Forall (fun x => zb write_bounds x = Some (0, 255) /\ isk KI x = true)
    (write_fe_selected_bytes rho layout bd base).
Proof.
  unfold write_fe_selected_bytes; destruct (truth rho layout (write_fe_condition bd base));
    [apply write_fe_true_bytes_checked|apply write_fe_false_bytes_checked].
Qed.
Theorem write_fe_selected_machine_bytes value rc bd base layout :
  0 <= value < 2 ^ 256 ->
  map (fun x => ii (den (write_fe_rho value rc) layout x))
    (write_fe_selected_bytes (write_fe_rho value rc) layout bd base) =
      map Int.repr (be_bytes (value mod feP)).
Proof.
  intro HValue; rewrite <- (write_fe_selected_bytes_numeric value rc bd base layout HValue), map_map.
  apply map_ext_in; intros x HIn.
  destruct (proj1 (Forall_forall _ _) (write_fe_selected_bytes_checked
    (write_fe_rho value rc) bd base layout) x HIn) as [HCheck HKind].
  rewrite (proj1 (den_zval_int (write_fe_rho value rc) write_bounds layout
    (write_rho_bounds value rc HValue) x 0 255 HCheck HKind)); reflexivity.
Qed.
Fixpoint selected_events rho layout rr : list event :=
  match rr with RDone state _ => slog state
    | RIf c a b => if truth rho layout c then selected_events rho layout a else selected_events rho layout b end.
Lemma selected_events_rsel rho layout rr : slog (fst (rsel rho layout rr)) = selected_events rho layout rr.
Proof.
  induction rr as [state outcome|condition a IHa b IHb]; cbn [rsel selected_events].
  - reflexivity.
  - destruct (truth rho layout condition); assumption.
Qed.
Lemma write_fe_selected_log rho layout bd base :
  slog (fst (rsel rho layout (write_fe_result bd base))) =
    if truth rho layout (write_fe_condition bd base)
    then [write_fe_true_event bd base] else [write_fe_false_event bd base].
Proof. rewrite selected_events_rsel; reflexivity. Qed.
Lemma write_fe_written_count rho layout bd base :
  written (slog (fst (rsel rho layout (write_fe_result bd base)))) = 256.
Proof.
  rewrite write_fe_selected_log; destruct (truth rho layout (write_fe_condition bd base)); reflexivity.
Qed.
Lemma write_fe_has_written rho layout bd base :
  has_wr (slog (fst (rsel rho layout (write_fe_result bd base)))) = true.
Proof.
  rewrite write_fe_selected_log; destruct (truth rho layout (write_fe_condition bd base)); reflexivity.
Qed.
Lemma write_fe_selected_outs_bytes rho layout bd base :
  outsA rho (slog (fst (rsel rho layout (write_fe_result bd base)))) =
    byte_sequence_cells (map (fun x => ii (den rho β0 x)) (write_fe_selected_bytes rho layout bd base)).
Proof.
  rewrite write_fe_selected_log; unfold write_fe_selected_bytes.
  destruct (truth rho layout (write_fe_condition bd base));
    unfold outsA, is_wr, wr_bytes; cbn [map concat etag]; rewrite app_nil_r; reflexivity.
Qed.

Require Import C.jet_sx_mem.
Lemma write_fe_selected_outs_numeric value rc bd base layout :
  0 <= value < 2 ^ 256 ->
  outsA (write_fe_rho value rc)
    (slog (fst (rsel (write_fe_rho value rc) layout (write_fe_result bd base)))) =
    byte_sequence_cells (map Int.repr (be_bytes (value mod feP))).
Proof.
  intro HValue; rewrite write_fe_selected_outs_bytes.
  replace (map (fun x => ii (den (write_fe_rho value rc) β0 x))
    (write_fe_selected_bytes (write_fe_rho value rc) layout bd base)) with
    (map (fun x => ii (den (write_fe_rho value rc) layout x))
      (write_fe_selected_bytes (write_fe_rho value rc) layout bd base)).
  - rewrite write_fe_selected_machine_bytes by exact HValue; reflexivity.
  - apply map_ext; intro x; apply (proj1 (den_proj_indep (write_fe_rho value rc) x layout β0)).
Qed.
Require Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_word_repr.
Require Import C.jet_secp_output_bytes C.jet_secp_canonical_normalize.
Theorem write_fe_selected_outs_canonical (value : Ty.tySem (Word.Word 8)) rc bd base layout :
  outsA (write_fe_rho (@Word.ToZ.Theory.toZ (Word.WordToZ 8) value) rc)
    (slog (fst (rsel (write_fe_rho (@Word.ToZ.Theory.toZ (Word.WordToZ 8) value) rc) layout
      (write_fe_result bd base)))) =
      Simplicity.Translate.encode (@canonical_fe_normalize Alg.CoreFunSem value).
Proof.
  rewrite write_fe_selected_outs_numeric by apply word_toZ_range.
  rewrite <- canonical_field_order_matches_limb_model, <- canonical_fe_normalize_numeric.
  apply be_bytes_canonical_encoding.
Qed.

From compcert Require Import ClightBigstep Events Memory.
Require Import C.jet_frame_inv C.jet_output_layout C.jet_secp_linkage C.jets_secp.
(** Whole original write_fe call. Initial field-region and frame facts must be
    constructed by the public caller; this remains support, not jet coverage. *)
Theorem eval_write_fe_against_canonical_program m0 bd dbase bw outedge cursor N bi rc
    (value : Ty.tySem (Word.Word 8)) w0 outs0 m layout :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  rep (write_fe_rho (@Word.ToZ.Theory.toZ (Word.WordToZ 8) value) rc)
    layout write_fe_initial_regs m ->
  xsep (jet_secp_write_fe_wrapper.write_ext m0 bd bw bi) layout ->
  jet_secp_write_fe_wrapper.write_inv m0 bd dbase bw outedge cursor N bi rc w0 outs0
    (write_fe_rho (@Word.ToZ.Theory.toZ (Word.WordToZ 8) value) rc) [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase);
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf Vundef /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (outs0 ++ Simplicity.Translate.encode (@canonical_fe_normalize Alg.CoreFunSem value)) /\
    lframe (frame (jet_secp_write_fe_wrapper.write_ext m0 bd bw bi) layout
      write_fe_initial_regs m) m mf.
Proof.
  intros HOutput HRep HSep HInv.
  destruct (eval_write_fe_from_initial_regions m0 bd dbase bw outedge cursor N bi 0 rc []
    w0 outs0 HOutput m layout (write_fe_rho (@Word.ToZ.Theory.toZ (Word.WordToZ 8) value) rc)
    HRep HSep HInv) as [mf [HExec [HFinal [HFinalInv HFrame]]]].
  exists mf; split; [exact HExec|]; split; [|exact HFrame].
  unfold jet_secp_write_fe_wrapper.write_inv, invA in HFinalInv.
  rewrite write_fe_has_written, orb_true_r, write_fe_selected_outs_canonical in HFinalInv.
  exact (proj1 (proj2 HFinalInv)).
Qed.

Require Import C.jet_sx_rep.
Lemma vars5_one_nth i x :
  nth_error (vars5 1) i = Some x -> (i < 5)%nat /\ x = XLv (S i).
Proof.
  destruct i as [|[|[|[|[|i]]]]]; cbn [vars5 nth_error]; intros H;
    try (inversion H; subst x; split; [lia|reflexivity]).
  destruct i; discriminate.
Qed.
Lemma write_fe_region_from_field value rc layout m r :
  fe_at m (blk layout r) (bas layout r) (map Int64.repr (fe_limbs_of value)) ->
  region_ok (write_fe_rho value rc) layout m r (fe_reg (vars5 1)).
Proof.
  intros [HBase [HAlign [HMax [HPerm HLoad]]]].
  apply region_u64.
  - exact HBase.
  - exact HAlign.
  - change (bas layout r + 40 <= Ptrofs.max_unsigned); exact HMax.
  - eapply Mem.perm_valid_block; apply (HPerm (bas layout r)); lia.
  - change (Mem.range_perm m (blk layout r) (bas layout r) (bas layout r + 40) Cur Writable); exact HPerm.
  - intros i x HNth; destruct (vars5_one_nth i x HNth) as [HIndex HValue].
    rewrite HValue; split; [|reflexivity].
    change (Mem.load Mint64 m (blk layout r) (bas layout r + 8 * Z.of_nat i) =
      Some (Vlong (Int64.repr (nth i (fe_limbs_of value) 0)))).
    apply HLoad; rewrite nth_error_map, (nth_error_nth' _ 0).
    + reflexivity.
    + change (i < 5)%nat; exact HIndex.
Qed.
Lemma write_fe_initial_rep_from_field value rc m b ofs :
  fe_at m b ofs (map Int64.repr (fe_limbs_of value)) ->
  rep (write_fe_rho value rc) [(b, ofs)] write_fe_initial_regs m.
Proof.
  intro HField; apply (rep_add _ [] [] m b ofs).
  - apply rep_nil.
  - cbn; tauto.
  - apply write_fe_region_from_field; exact HField.
Qed.
Theorem eval_write_fe_from_canonical_field m0 bd dbase bw outedge cursor N bi rc
    (value : Ty.tySem (Word.Word 8)) w0 outs0 m b ofs :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  fe_at m b ofs (map Int64.repr (fe_limbs_of (@Word.ToZ.Theory.toZ (Word.WordToZ 8) value))) ->
  xsep (jet_secp_write_fe_wrapper.write_ext m0 bd bw bi) [(b, ofs)] ->
  jet_secp_write_fe_wrapper.write_inv m0 bd dbase bw outedge cursor N bi rc w0 outs0
    (write_fe_rho (@Word.ToZ.Theory.toZ (Word.WordToZ 8) value) rc) [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase); Vptr b (Ptrofs.repr ofs)] E0 mf Vundef /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (outs0 ++ Simplicity.Translate.encode (@canonical_fe_normalize Alg.CoreFunSem value)) /\
    lframe (frame (jet_secp_write_fe_wrapper.write_ext m0 bd bw bi) [(b, ofs)]
      write_fe_initial_regs m) m mf.
Proof.
  intros HOutput HField HSep HInv.
  apply (eval_write_fe_against_canonical_program m0 bd dbase bw outedge cursor N bi rc
    value w0 outs0 m [(b, ofs)] HOutput).
  - apply write_fe_initial_rep_from_field; exact HField.
  - exact HSep.
  - exact HInv.
Qed.

Require Import C.jet_secp_wrapper_run C.jet_input_layout.
Lemma read_fe_final_inv_to_write_initial m0 bd dbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word.Word 8)) m :
  jet_secp_wrapper_run.read_inv m0 bd dbase bw outedge cursor N bi rc [] 256
    (read_fe_rho (frame_input_word_bits value) rc) (read_fe_log bi (Ptrofs.repr edge)) m ->
  jet_secp_write_fe_wrapper.write_inv m0 bd dbase bw outedge cursor N bi rc false []
    (write_fe_rho (@Word.ToZ.Theory.toZ (Word.WordToZ 8)
      (@canonical_fe_normalize Alg.CoreFunSem value)) rc) [] m.
Proof.
  intro HInv.
  change (Int64.repr rc = Int64.repr rc /\
    finv m0 bd dbase bw outedge cursor N bi m false [] /\ 256 <= N /\ 0 <= 256) in HInv.
  change (Int64.repr rc = Int64.repr rc /\
    finv m0 bd dbase bw outedge cursor N bi m false [] /\ 256 <= N /\ 0 <= 256).
  exact HInv.
Qed.
Local Opaque finv canonical_fe_normalize Simplicity.Translate.encode.
Theorem eval_write_fe_after_read_field m0 bd dbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word.Word 8)) m b ofs :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  fe_at m b ofs (map Int64.repr (fe_limbs_of
    (@Word.ToZ.Theory.toZ (Word.WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)))) ->
  xsep (jet_secp_write_fe_wrapper.write_ext m0 bd bw bi) [(b, ofs)] ->
  jet_secp_wrapper_run.read_inv m0 bd dbase bw outedge cursor N bi rc [] 256
    (read_fe_rho (frame_input_word_bits value) rc) (read_fe_log bi (Ptrofs.repr edge)) m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase); Vptr b (Ptrofs.repr ofs)] E0 mf Vundef /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (Simplicity.Translate.encode (@canonical_fe_normalize Alg.CoreFunSem value)) /\
    lframe (frame (jet_secp_write_fe_wrapper.write_ext m0 bd bw bi) [(b, ofs)]
      write_fe_initial_regs m) m mf.
Proof.
  intros HOutput HField HSep HReadInv.
  destruct (eval_write_fe_from_canonical_field m0 bd dbase bw outedge cursor N bi rc
    (@canonical_fe_normalize Alg.CoreFunSem value) false [] m b ofs HOutput HField HSep
    (read_fe_final_inv_to_write_initial m0 bd dbase bw outedge cursor N bi edge rc value m HReadInv))
    as [mf [HExec [HFinal HFrame]]].
  rewrite (canonical_fe_normalize_idempotent value) in HFinal.
  cbn [app] in HFinal.
  exists mf; split; [exact HExec|]; split; [exact HFinal|exact HFrame].
Qed.
