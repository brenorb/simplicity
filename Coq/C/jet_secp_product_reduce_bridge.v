(** Actual initialized product buffer becomes the next reduction input.
    Reindexing and rho adaptation change no concrete memory. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Memory Values Clight ClightBigstep Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_sx_eval.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar.
Require Import C.jet_sx_u64_transport C.jet_secp_scalar_mul512_fresh
  C.jet_secp_scalar_mul512_run C.jet_secp_scalar_mul512_machine
  C.jet_secp_scalar_mul512_symbolic C.jet_secp_scalar_mul512_accumulate
  C.jet_secp_scalar_mul512_owned_product
  C.jet_secp_scalar_mul512_low C.jet_secp_scalar_mul512_product
  C.jet_secp_scalar_reduce512_run C.jet_secp_reduce512_final_stage
  C.jet_secp_reduce512_final_atomic C.jet_secp_reduce512_body_numeric
  C.jet_secp_reduce512_function_numeric.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition product_reduce_rho (rho : nat -> int64) n :=
  if Nat.ltb n 8 then nth n (scalar_mul512_machine_outputs rho) Int64.zero
  else rho (n - 8)%nat.
Definition product_reduce_layout beta : layout := [lay beta 1; lay beta 0].
Lemma eight_words_nth (xs : list int64) : length xs = 8%nat ->
  xs = [nth 0 xs Int64.zero; nth 1 xs Int64.zero; nth 2 xs Int64.zero; nth 3 xs Int64.zero;
        nth 4 xs Int64.zero; nth 5 xs Int64.zero; nth 6 xs Int64.zero; nth 7 xs Int64.zero].
Proof.
  intro H; do 8 (destruct xs as [|? xs]; [discriminate|]).
  destruct xs; [reflexivity|cbn [length] in H; lia].
Qed.
Lemma product_reduce_input_map rho beta :
  map (den (product_reduce_rho rho) beta) [XLv 0; XLv 1; XLv 2; XLv 3; XLv 4; XLv 5; XLv 6; XLv 7] =
  map Vlong (scalar_mul512_machine_outputs rho).
Proof.
  pose proof (eight_words_nth _ (scalar_mul512_machine_length rho)) as H.
  change ([Vlong (nth 0 (scalar_mul512_machine_outputs rho) Int64.zero);
    Vlong (nth 1 (scalar_mul512_machine_outputs rho) Int64.zero);
    Vlong (nth 2 (scalar_mul512_machine_outputs rho) Int64.zero);
    Vlong (nth 3 (scalar_mul512_machine_outputs rho) Int64.zero);
    Vlong (nth 4 (scalar_mul512_machine_outputs rho) Int64.zero);
    Vlong (nth 5 (scalar_mul512_machine_outputs rho) Int64.zero);
    Vlong (nth 6 (scalar_mul512_machine_outputs rho) Int64.zero);
    Vlong (nth 7 (scalar_mul512_machine_outputs rho) Int64.zero)] =
    map Vlong (scalar_mul512_machine_outputs rho)).
  rewrite H at 9; reflexivity.
Qed.
Lemma product_reduce_output_map rho beta beta' :
  map (den (product_reduce_rho rho) beta') [XLv 8; XLv 9; XLv 10; XLv 11] =
  map (den rho beta) [XLv 0; XLv 1; XLv 2; XLv 3].
Proof. reflexivity. Qed.
Local Opaque scalar_mul512_machine_outputs scalar_mul512_state.
Lemma empty_region_index n : @nth_error region [] n = None.
Proof. destruct n; reflexivity. Qed.
Theorem product_reduce_entry_rep rho beta m :
  rep rho beta (sregs scalar_mul512_state) m ->
  rep (product_reduce_rho rho) (product_reduce_layout beta) scalar_reduce512_initial_regs m.
Proof.
  intro HR; rewrite scalar_mul512_output in HR.
  destruct HR as (HL & HS & HC).
  unfold rep; split; [reflexivity|]. split.
  - intros r1 r2 reg1 reg2 Hne E1 E2.
    destruct r1 as [|[|r1]], r2 as [|[|r2]];
      cbn [scalar_reduce512_initial_regs nth_error] in E1,E2; try discriminate;
      try (rewrite empty_region_index in E1; discriminate);
      try (rewrite empty_region_index in E2; discriminate);
      try (exfalso; apply Hne; reflexivity).
    + inversion E1; inversion E2; subst.
      destruct (HS 1%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl) as [HD|[HF _]].
      * left; exact HD.
      * discriminate.
    + inversion E1; inversion E2; subst.
      destruct (HS 0%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) as [HD|[HF _]].
      * left; exact HD.
      * discriminate.
  - intros r reg E; destruct r as [|[|r]]; cbn [scalar_reduce512_initial_regs nth_error] in E; try discriminate;
      try (rewrite empty_region_index in E; discriminate).
    + inversion E; subst reg.
      eapply region_u64_transport with (rho := rho) (beta := beta)
        (r := 1%nat) (xs := [XLv 0; XLv 1; XLv 2; XLv 3]) (ys := [XLv 8; XLv 9; XLv 10; XLv 11]).
      * reflexivity.
      * reflexivity.
      * apply product_reduce_output_map.
      * reflexivity.
      * exact (HC 1%nat _ eq_refl).
    + inversion E; subst reg.
      eapply region_u64_transport with (rho := rho) (beta := beta)
        (r := 0%nat) (xs := scalar_mul512_limbs)
        (ys := [XLv 0; XLv 1; XLv 2; XLv 3; XLv 4; XLv 5; XLv 6; XLv 7]).
      * reflexivity.
      * symmetry; apply scalar_mul512_limbs_length.
      * rewrite product_reduce_input_map,scalar_mul512_outputs_machine; reflexivity.
      * reflexivity.
      * exact (HC 0%nat _ eq_refl).
Qed.
Lemma product_reduce_integer rho :
  reduce512_input_integer (product_reduce_rho rho) =
    scalar_mul512_input_value rho 0 * scalar_mul512_input_value rho 4.
Proof.
  rewrite <- scalar_mul512_machine_product.
  unfold reduce512_input_integer,scalar_mul512_input_value,product_reduce_rho.
  cbn [Nat.add Nat.ltb Nat.leb].
  pose proof (eight_words_nth _ (scalar_mul512_machine_length rho)) as H.
  rewrite H at 9.
  cbn [column_words_value].
  change C.jet_secp_reduce512_fold_bounds.reduce512_radix with
    (Int64.modulus * Int64.modulus * Int64.modulus * Int64.modulus).
  ring.
Qed.
Lemma product_reduce_foot_embed beta b ofs :
  foot (product_reduce_layout beta) (map rshape scalar_reduce512_initial_regs) b ofs ->
  foot beta (map rshape scalar_mul512_fresh_regs) b ofs.
Proof.
  intros (r & sh & d & ch & Hs & Hin & Hb & Hr).
  destruct r as [|[|r]].
  - exists 1%nat,sh,d,ch; exact (conj Hs (conj Hin (conj Hb Hr))).
  - exists 0%nat,sh,d,ch; exact (conj Hs (conj Hin (conj Hb Hr))).
  - cbn [scalar_reduce512_initial_regs map nth_error] in Hs;
      destruct r; discriminate.
Qed.
Theorem eval_product_then_reduce rho beta m :
  rep rho beta scalar_mul512_fresh_regs m ->
  exists mp mf,
    Clight2.eval_funcall secp_ge m (Ctypes.Internal f_secp256k1_scalar_mul_512)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
       Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mp Vundef /\
    Clight2.eval_funcall secp_ge mp (Ctypes.Internal f_secp256k1_scalar_reduce_512)
      [Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
       Vptr (blk beta 0) (Ptrofs.repr (bas beta 0))] E0 mf Vundef /\
    rep (product_reduce_rho rho) (product_reduce_layout beta)
      (reduce512_numeric_owned_regs (product_reduce_rho rho)) mf /\
    final_output_value (reduce512_body_digits (product_reduce_rho rho))
      (reduce512_body_carry (product_reduce_rho rho))
      (product_reduce_rho rho) (lay (product_reduce_layout beta)) =
      (scalar_mul512_input_value rho 0 * scalar_mul512_input_value rho 4) mod canonical_group_order /\
    lframe (fun b ofs => ~ foot beta (map rshape scalar_mul512_fresh_regs) b ofs) m mp /\
    lframe (fun b ofs => ~ foot (product_reduce_layout beta)
      (map rshape scalar_reduce512_initial_regs) b ofs) mp mf.
Proof.
  intro HR; destruct (eval_scalar_mul512_fresh rho beta m HR) as (mp & HP & HRP & HFP).
  pose proof (product_reduce_entry_rep rho beta mp HRP) as Hentry.
  destruct (eval_reduce512_numeric_owned (product_reduce_rho rho)
    (product_reduce_layout beta) mp Hentry) as (mf & HC & Hout & Hvalue & HF).
  rewrite product_reduce_integer in Hvalue.
  exists mp,mf; exact (conj HP (conj HC (conj Hout (conj Hvalue (conj HFP HF))))).
Qed.
