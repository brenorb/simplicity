(** Establish the inverse invariant from the actual caller's initialized
    objects and copies. The matrix remains uninitialized: this prefix stops
    before the first divstep call and does not assume that call's result. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_exec C.jet_sx_eval C.jet_sx_mem C.jet_sx_u64_transport.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_copies.
Require Import C.jet_secp_modinv_var_de C.jet_secp_modinv_var_fg C.jet_secp_modinv_var_post.
Require Import C.jet_secp_modinv_var_invariant C.jet_secp_modinv_de_numeric C.jet_secp_modinv_fg_loop_numeric.
Require Import C.jet_secp_modinv_normalize62_words C.jet_secp_signed62_numeric.
Require Import C.jet_secp_modinfo_fe_global C.jet_secp_modinfo_fe_copy C.jet_secp_fe_math.
Require Import C.jet_secp_multiply_normalize_bridge C.divstep.
Require Import C.jet_secp_modinv_var_ranges.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition inv_seed_rho (w : nat->int64) n := nth n
  (words5 w ++ words5 (inv_init_word false) ++ words5 (inv_init_word true) ++
   words5 modinfo_fe_limb ++ words5 w) Int64.zero.
Definition inv_seed_matrix := mkreg
  [mkcell 0 Mint64 None;mkcell 8 Mint64 None;mkcell 16 Mint64 None;mkcell 24 Mint64 None]
  true (Some 32).
Definition inv_seed_regs := upd inv_loop_regs 6 inv_seed_matrix.
Lemma inv_seed_matrix_source : nth 6 inv_fg_regs (mkreg [] true None)=inv_seed_matrix.
Proof. reflexivity. Qed.

Lemma inv_seed_shapes : map rshape inv_seed_regs=map rshape inv_fg_regs.
Proof. reflexivity. Qed.

Theorem inv_seed_rep w beta m : rep w beta inv_fg_regs m ->
  rep (inv_seed_rho w) beta inv_seed_regs m.
Proof.
  intros Rep;pose proof Rep as (Len & Sep & Regions);split;[exact Len|];split.
  - eapply rsep_shape;[apply inv_seed_shapes|exact Sep].
  - intros r reg At;assert (R : (r<7)%nat) by
      (change (r<length inv_seed_regs)%nat;apply nth_error_Some;rewrite At;discriminate).
    destruct r as [|[|[|[|[|[|[|r]]]]]]];try lia;
      cbn [inv_seed_regs inv_loop_regs upd nth_error] in At;injection At as <-.
    + eapply region_u64_transport with (rho:=w) (beta:=beta) (r:=0%nat)
        (xs:=vars5 0) (ys:=vars5 0);try reflexivity;exact (Regions 0%nat _ eq_refl).
    + eapply region_u64_transport with (rho:=w) (beta:=beta) (r:=1%nat)
        (xs:=map XLc modinfo_fe_words) (ys:=map XLc modinfo_fe_words);
        try reflexivity;exact (Regions 1%nat _ eq_refl).
    + eapply region_u64_transport with (rho:=w) (beta:=beta) (r:=2%nat)
        (xs:=map (inv_init_sx false) [0;1;2;3;4]%nat) (ys:=vars5 5);
        try reflexivity;exact (Regions 2%nat _ eq_refl).
    + eapply region_u64_transport with (rho:=w) (beta:=beta) (r:=3%nat)
        (xs:=map (inv_init_sx true) [0;1;2;3;4]%nat) (ys:=vars5 10);
        try reflexivity;exact (Regions 3%nat _ eq_refl).
    + eapply region_u64_transport with (rho:=w) (beta:=beta) (r:=4%nat)
        (xs:=inv_modulus_exprs) (ys:=vars5 15);try reflexivity;exact (Regions 4%nat _ eq_refl).
    + eapply region_u64_transport with (rho:=w) (beta:=beta) (r:=5%nat)
        (xs:=inv_input_exprs) (ys:=vars5 20);try reflexivity;exact (Regions 5%nat _ eq_refl).
    + eapply inv_region_undefined;[repeat constructor|].
      rewrite <-inv_seed_matrix_source;exact (Regions 6%nat _ eq_refl).
Qed.

Lemma inv_seed_input_signed w : signed62_normalized w -> forall i,(i<5)%nat ->
  Int64.signed (w i)=Int64.unsigned (w i).
Proof.
  intros Bounds i I;apply Int64.signed_eq_unsigned.
  pose proof (Bounds i I);change Int64.max_signed with 9223372036854775807.
  destruct (Nat.eqb i 4);lia.
Qed.
Lemma inv_seed_input_value w : signed62_normalized w ->
  norm62_value_z 4 (fun i=>Int64.signed (w i))=signed62_unsigned_value w.
Proof.
  intro Bounds;cbn [norm62_value_z];unfold signed62_unsigned_value.
  rewrite !inv_seed_input_signed by (try exact Bounds;lia);ring.
Qed.
Lemma inv_seed_input_range w : signed62_normalized w -> 0<=signed62_unsigned_value w<2^256.
Proof.
  intro Bounds;pose proof (Bounds 0%nat ltac:(lia)) as B0;
  pose proof (Bounds 1%nat ltac:(lia)) as B1;pose proof (Bounds 2%nat ltac:(lia)) as B2;
  pose proof (Bounds 3%nat ltac:(lia)) as B3;pose proof (Bounds 4%nat ltac:(lia)) as B4.
  change (0<=Int64.unsigned (w 0%nat)<2^62) in B0.
  change (0<=Int64.unsigned (w 1%nat)<2^62) in B1.
  change (0<=Int64.unsigned (w 2%nat)<2^62) in B2.
  change (0<=Int64.unsigned (w 3%nat)<2^62) in B3.
  change (0<=Int64.unsigned (w 4%nat)<2^8) in B4.
  unfold signed62_unsigned_value;lia.
Qed.
Lemma inv_seed_modulus_value : norm62_value_z 4 (fun i=>Int64.signed (modinfo_fe_limb i))=feP.
Proof. vm_compute;reflexivity. Qed.
Lemma inv_seed_modulus_odd : Zodd feP.
Proof. vm_compute;exact I. Qed.
Definition inv_seed_state w := init feP (signed62_unsigned_value w) inv_seed_modulus_odd.

Lemma inv_seed_de_value w high : de62_input_value (inv_de_rho (inv_seed_rho w)) high=
  if high then 1 else 0.
Proof. destruct high;reflexivity. Qed.
Lemma inv_seed_de_word w high i : (i<5)%nat ->
  de62_array (inv_de_rho (inv_seed_rho w)) high i=inv_init_word high i.
Proof. destruct high;destruct i as [|[|[|[|[|i]]]]];intro I;try lia;reflexivity. Qed.
Lemma inv_seed_de_bounds w : de62_state_bounds (inv_de_rho (inv_seed_rho w)).
Proof.
  pose proof (inv_initial_de_bounds (inv_de_rho (inv_seed_rho w))) as (Limbs & Values).
  split.
  - intros high i I;rewrite inv_seed_de_word by exact I.
    rewrite <-(inv_initial_de_word (inv_de_rho (inv_seed_rho w)) high i I);apply Limbs;exact I.
  - intro high;rewrite inv_seed_de_value;specialize (Values high).
    rewrite inv_initial_de_value in Values;exact Values.
Qed.
Lemma inv_seed_fg_value w high : signed62_normalized w ->
  inv_fg_active_value 5 (inv_seed_rho w) high=if high then signed62_unsigned_value w else feP.
Proof.
  intro Bounds;destruct high.
  - change (norm62_value_z 4 (fun i=>Int64.signed (inv_seed_rho w (20+i)%nat))=signed62_unsigned_value w).
    rewrite <-inv_seed_input_value by exact Bounds;apply norm62_value_ext;
      intros i I;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity.
  - change (norm62_value_z 4 (fun i=>Int64.signed (inv_seed_rho w (15+i)%nat))=feP).
    rewrite <-inv_seed_modulus_value;apply norm62_value_ext;
      intros i I;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity.
Qed.
Lemma inv_seed_coefficient_link w : signed62_normalized w ->
  inv_coefficient_link (signed62_unsigned_value w) 5 (inv_seed_rho w).
Proof.
  intros Bounds high;unfold inv_coefficient_link;rewrite inv_seed_de_value,inv_seed_fg_value by exact Bounds.
  destruct high;[rewrite Z.mul_1_r;reflexivity|
    rewrite Z.mul_0_r,Zmod_0_l,(Z.mod_same feP inv_field_modulus_nonzero);reflexivity].
Qed.
Lemma inv_seed_state_matches w : signed62_normalized w ->
  inv_state_matches 5 (inv_seed_rho w) (inv_seed_state w).
Proof.
  intro Bounds;split;rewrite inv_seed_fg_value by exact Bounds;reflexivity.
Qed.

Lemma inv_seed_fg_word w high j : (j<5)%nat ->
  fg_array_word (inv_fg_rho 5 (inv_seed_rho w)) high j=
    if high then w j else modinfo_fe_limb j.
Proof. destruct high;destruct j as [|[|[|[|[|j]]]]];intro J;try lia;reflexivity. Qed.
Lemma inv_seed_fg_bounds w : signed62_normalized w -> forall high j,(j<5)%nat ->
  Z.abs (Int64.signed (fg_array_word (inv_fg_rho 5 (inv_seed_rho w)) high j))<=2^62.
Proof.
  intros Bounds high j J;rewrite inv_seed_fg_word by exact J;destruct high.
  - rewrite inv_seed_input_signed by assumption;rewrite Z.abs_eq by apply Int64.unsigned_range.
    pose proof (Bounds j J);destruct (Nat.eqb j 4);lia.
  - destruct j as [|[|[|[|[|j]]]]];try lia;vm_compute;discriminate.
Qed.
Lemma inv_seed_state_range w : signed62_normalized w ->
  delta (inv_seed_state w)=1 /\ eta (inv_seed_state w)= -1 /\
  Z.abs (f (inv_seed_state w))<=2^256 /\ Z.abs (g (inv_seed_state w))<=2^256.
Proof.
  intro Bounds;pose proof (inv_seed_input_range w Bounds) as Range.
  change (1=1 /\ -1= -1 /\ Z.abs feP<=2^256 /\ Z.abs (signed62_unsigned_value w)<=2^256).
  rewrite !Z.abs_eq by (unfold feP,feR in *;lia);unfold feP,feR;repeat split;lia.
Qed.

Lemma inv_seed_limb_bounds w : signed62_normalized w -> inv_fg_limb_bounds (inv_seed_rho w).
Proof.
  intros Bounds high j J;rewrite <-(inv_fg_limb_array 5 (inv_seed_rho w) high j J).
  exact (inv_seed_fg_bounds w Bounds high j J).
Qed.
Lemma inv_seed_value_capacity w : signed62_normalized w -> inv_fg_value_capacity 5 (inv_seed_rho w).
Proof.
  intros Bounds high;pose proof (inv_seed_input_range w Bounds) as Range.
  rewrite inv_seed_fg_value by exact Bounds;destruct high;
    unfold feP,feR in *;rewrite Z.abs_eq by lia;lia.
Qed.

Theorem inv_entry_establishes_invariant w beta m : signed62_normalized w ->
  rep w beta inv_start_regs m -> bas beta 1=0 -> exists betaN e le mi lef mf,
  function_entry2 secp_ge f_secp256k1_modinv64_var (map (den w (lay beta)) inv_start_args) m e le mi /\
  Clight2.exec_stmt secp_ge e le mi inv_ready_prefix E0 lef mf Out_normal /\
  rep (inv_seed_rho w) (beta++betaN) inv_seed_regs mf /\
  tmatch w (beta++betaN) inv_loop_start_temps lef /\
  ematch (beta++betaN) (snd inv_start_alloc) e /\
  lef!_len=Some (Vint (Int.repr 5)) /\ lef!_eta=Some (Vlong (Int64.repr (-1))) /\
  de62_state_bounds (inv_de_rho (inv_seed_rho w)) /\
  inv_coefficient_link (signed62_unsigned_value w) 5 (inv_seed_rho w) /\
  inv_state_matches 5 (inv_seed_rho w) (inv_seed_state w) /\
  (forall high j,(j<5)%nat ->
    Z.abs (Int64.signed (fg_array_word (inv_fg_rho 5 (inv_seed_rho w)) high j))<=2^62) /\
  inv_fg_limb_bounds (inv_seed_rho w) /\ inv_fg_value_capacity 5 (inv_seed_rho w) /\
  delta (inv_seed_state w)=1 /\ eta (inv_seed_state w)= -1 /\
  Z.abs (f (inv_seed_state w))<=2^256 /\ Z.abs (g (inv_seed_state w))<=2^256 /\
  Forall (fun p=>~Mem.valid_block m (fst p)) betaN /\
  lframe (fun b ofs=>~foot (beta++betaN) (map rshape (sregs inv_start_state)) b ofs) m mf.
Proof.
  intros Bounds Rep Base.
  destruct (inv_entry_to_loop w beta m Rep Base)
    as (betaN & e & le & mi & lef & mf & Entry & Run & Objects & Temps & Env & Len & Eta & Fresh & Frame).
  pose proof (inv_seed_rep w (beta++betaN) mf Objects) as Seed.
  pose proof (inv_seed_de_bounds w) as DE.
  pose proof (inv_seed_coefficient_link w Bounds) as Link.
  pose proof (inv_seed_state_matches w Bounds) as State.
  pose proof (inv_seed_fg_bounds w Bounds) as FG.
  pose proof (inv_seed_limb_bounds w Bounds) as Limbs.
  pose proof (inv_seed_value_capacity w Bounds) as Capacity.
  destruct (inv_seed_state_range w Bounds) as (Delta & MathEta & FBound & GBound).
  exists betaN,e,le,mi,lef,mf;repeat first [assumption|split].
Qed.
