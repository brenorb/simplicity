(** Factored expressions with uint64 top and the actual promotion casts. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Ctypes.
Require Import C.jet_sx_expr C.jet_secp_scalar_bind C.jet_secp_scalar_reduce_numeric.
Require Import C.jet_secp_umul128_exec C.jet_secp_umul128_numeric
  C.jet_secp_scalar_mul512_machine C.jet_secp_scalar_mul512_symbolic
  C.jet_secp_reduce512_wide.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition wide_symbolic_C0 := XLb Badd (XLnot (XLc (Int64.repr (-4624529908474429119)))) (XI2L Signed (XIc Int.one)).
Definition wide_symbolic_C1 := XLnot (XLc (Int64.repr (-4994812053365940165))).
Definition wide_C0 := Int64.repr 4624529908474429119.
Definition wide_C1 := Int64.repr 4994812053365940164.
Lemma wide_C0_den rho beta : den rho beta wide_symbolic_C0 = Vlong wide_C0.
Proof. exact (f_equal Vlong scalar_reduce_delta0_constant). Qed.
Lemma wide_C1_den rho beta : den rho beta wide_symbolic_C1 = Vlong wide_C1.
Proof. exact (f_equal Vlong scalar_reduce_delta1_constant). Qed.
Definition wide_bind a b x := scalar_bind (fun n => if Nat.eqb n 0 then a else b) (XL2I b) x.
Definition wide_symbolic_product_lo a b := wide_bind a b umul128_lo.
Definition wide_symbolic_product_hi a b := wide_bind a b umul128_hi.
Lemma wide_bind_den rho beta a b x A B : den rho beta a = Vlong A -> den rho beta b = Vlong B ->
  den rho beta (wide_bind a b x) = den (fun n => if Nat.eqb n 0 then A else B) beta x.
Proof.
  intros HA HB; apply scalar_bind_den.
  - intro n; destruct (Nat.eqb n 0); assumption.
  - cbn [den]; rewrite HB; reflexivity.
Qed.
Lemma wide_product_lo_den rho beta a b A B : den rho beta a = Vlong A -> den rho beta b = Vlong B ->
  den rho beta (wide_symbolic_product_lo a b) = Vlong (umul128_lo_machine A B).
Proof. intros HA HB; unfold wide_symbolic_product_lo; rewrite (wide_bind_den _ _ _ _ _ _ _ HA HB),umul128_lo_den; reflexivity. Qed.
Lemma wide_product_hi_den rho beta a b A B : den rho beta a = Vlong A -> den rho beta b = Vlong B ->
  den rho beta (wide_symbolic_product_hi a b) = Vlong (umul128_hi_machine A B).
Proof. intros HA HB; unfold wide_symbolic_product_hi; rewrite (wide_bind_den _ _ _ _ _ _ _ HA HB),umul128_hi_den; reflexivity. Qed.
Definition wide_symbolic_carry sg a b := XI2L sg (XLcmp Clt Unsigned (XLb Badd a b) b).
Lemma wide_carry_den rho beta sg a b A B : den rho beta a = Vlong A -> den rho beta b = Vlong B ->
  den rho beta (wide_symbolic_carry sg a b) = Vlong (column_carry64 A B).
Proof.
  intros HA HB; unfold wide_symbolic_carry; cbn [den]; rewrite HA,HB.
  change (Vlong (i2l sg (if Int64.ltu (Int64.add A B) B then Int.one else Int.zero)) = Vlong (column_carry64 A B)).
  unfold column_carry64; destruct sg; destruct (Int64.ltu (Int64.add A B) B); reflexivity.
Qed.
Definition wide_symbolic_from_word x := scolumn x (XI2L Signed (XIc Int.zero)) (XI2L Signed (XIc Int.zero)).
Definition wide_symbolic_lo_add a b s := XLb Badd (sc_lo s) (wide_symbolic_product_lo a b).
Definition wide_symbolic_hi_add a b s := XLb Badd (wide_symbolic_product_hi a b)
  (wide_symbolic_carry Signed (sc_lo s) (wide_symbolic_product_lo a b)).
Definition wide_symbolic_muladd a b s := scolumn (wide_symbolic_lo_add a b s)
  (XLb Badd (sc_hi s) (wide_symbolic_hi_add a b s))
  (XLb Badd (sc_top s) (wide_symbolic_carry Signed (sc_hi s) (wide_symbolic_hi_add a b s))).
Definition wide_symbolic_muladd_fast a b s := scolumn (wide_symbolic_lo_add a b s)
  (XLb Badd (sc_hi s) (wide_symbolic_hi_add a b s)) (sc_top s).
Definition wide_symbolic_sumadd x s := scolumn (XLb Badd (sc_lo s) x)
  (XLb Badd (sc_hi s) (wide_symbolic_carry Unsigned (sc_lo s) x))
  (XLb Badd (sc_top s) (wide_symbolic_carry Signed (sc_hi s) (wide_symbolic_carry Unsigned (sc_lo s) x))).
Definition wide_symbolic_sumadd_fast x s := scolumn (XLb Badd (sc_lo s) x)
  (XLb Badd (sc_hi s) (wide_symbolic_carry Signed (sc_lo s) x)) (sc_top s).
Definition wide_symbolic_extract s := scolumn (sc_hi s) (sc_top s) (XI2L Signed (XIc Int.zero)).
Definition wide_symbolic_extract_fast s := scolumn (sc_hi s) (XI2L Signed (XIc Int.zero)) (sc_top s).
Definition wide_rep rho beta sy ma := den rho beta (sc_lo sy) = Vlong (wlo ma) /\
  den rho beta (sc_hi sy) = Vlong (whi ma) /\ den rho beta (sc_top sy) = Vlong (wtop ma).
Lemma wide_from_word_rep rho beta x X : den rho beta x = Vlong X ->
  wide_rep rho beta (wide_symbolic_from_word x) (wide_from_word X).
Proof. intro H; split; [exact H|]; split; reflexivity. Qed.
Lemma wide_lo_add_rep rho beta a b A B sy ma : den rho beta a = Vlong A -> den rho beta b = Vlong B ->
  wide_rep rho beta sy ma -> den rho beta (wide_symbolic_lo_add a b sy) = Vlong (column_product_lo A B (wide_lower ma)).
Proof.
  intros HA HB (HL & HH & HT); unfold wide_symbolic_lo_add,column_product_lo; cbn [wide_lower col_lo].
  apply column_ladd_den; [exact HL|apply wide_product_lo_den; assumption].
Qed.
Lemma wide_hi_add_rep rho beta a b A B sy ma : den rho beta a = Vlong A -> den rho beta b = Vlong B ->
  wide_rep rho beta sy ma -> den rho beta (wide_symbolic_hi_add a b sy) = Vlong (column_product_hi_add A B (wide_lower ma)).
Proof.
  intros HA HB (HL & HH & HT); unfold wide_symbolic_hi_add,column_product_hi_add; cbn [wide_lower col_lo].
  apply column_ladd_den; [apply wide_product_hi_den; assumption|].
  apply wide_carry_den; [exact HL|apply wide_product_lo_den; assumption].
Qed.
Lemma wide_muladd_rep rho beta a b A B sy ma : den rho beta a = Vlong A -> den rho beta b = Vlong B ->
  wide_rep rho beta sy ma -> wide_rep rho beta (wide_symbolic_muladd a b sy) (wide_muladd A B ma).
Proof.
  intros HA HB H; pose proof (wide_lo_add_rep _ _ _ _ _ _ _ _ HA HB H) as HL.
  pose proof (wide_hi_add_rep _ _ _ _ _ _ _ _ HA HB H) as HH.
  destruct H as (_ & Hhi & Htop).
  unfold wide_rep; cbn [wide_symbolic_muladd wide_muladd sc_lo sc_hi sc_top wlo whi wtop].
  split; [exact HL|]. split; [apply column_ladd_den; assumption|].
  apply column_ladd_den; [exact Htop|apply wide_carry_den; assumption].
Qed.
Lemma wide_muladd_fast_rep rho beta a b A B sy ma : den rho beta a = Vlong A -> den rho beta b = Vlong B ->
  wide_rep rho beta sy ma -> wide_rep rho beta (wide_symbolic_muladd_fast a b sy) (wide_muladd_fast A B ma).
Proof.
  intros HA HB H; pose proof (wide_lo_add_rep _ _ _ _ _ _ _ _ HA HB H) as HL.
  pose proof (wide_hi_add_rep _ _ _ _ _ _ _ _ HA HB H) as HH.
  destruct H as (_ & Hhi & Htop).
  unfold wide_rep; cbn [wide_symbolic_muladd_fast wide_muladd_fast sc_lo sc_hi sc_top wlo whi wtop].
  split; [exact HL|]. split; [apply column_ladd_den; assumption|exact Htop].
Qed.
Lemma wide_sumadd_rep rho beta x X sy ma : den rho beta x = Vlong X -> wide_rep rho beta sy ma ->
  wide_rep rho beta (wide_symbolic_sumadd x sy) (wide_sumadd X ma).
Proof.
  intros HX (HL & HH & HT).
  assert (HC : den rho beta (wide_symbolic_carry Unsigned (sc_lo sy) x) = Vlong (column_carry64 (wlo ma) X))
    by (apply wide_carry_den; assumption).
  unfold wide_rep; cbn [wide_symbolic_sumadd wide_sumadd sc_lo sc_hi sc_top wlo whi wtop].
  split; [apply column_ladd_den; assumption|]. split; [apply column_ladd_den; assumption|].
  apply column_ladd_den; [exact HT|apply wide_carry_den; assumption].
Qed.
Lemma wide_sumadd_fast_rep rho beta x X sy ma : den rho beta x = Vlong X -> wide_rep rho beta sy ma ->
  wide_rep rho beta (wide_symbolic_sumadd_fast x sy) (wide_sumadd_fast X ma).
Proof.
  intros HX (HL & HH & HT).
  unfold wide_rep; cbn [wide_symbolic_sumadd_fast wide_sumadd_fast sc_lo sc_hi sc_top wlo whi wtop].
  split; [apply column_ladd_den; assumption|]. split; [|exact HT].
  apply column_ladd_den; [exact HH|apply wide_carry_den; assumption].
Qed.
Lemma wide_extract_rep rho beta sy ma : wide_rep rho beta sy ma ->
  wide_rep rho beta (wide_symbolic_extract sy) (wide_extract ma).
Proof. intros (_ & HH & HT); split; [exact HH|]. split; [exact HT|reflexivity]. Qed.
Lemma wide_extract_fast_rep rho beta sy ma : wide_rep rho beta sy ma ->
  wide_rep rho beta (wide_symbolic_extract_fast sy) (wide_extract_fast ma).
Proof. intros (_ & HH & HT); split; [exact HH|]. split; [reflexivity|exact HT]. Qed.
