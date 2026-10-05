(** [secp256k1_fe_set_b32] and [secp256k1_fe_get_b32]: conversion between
    32 big-endian bytes and canonical limbs. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_exec C.jet_sx_pure.
Require Import C.jet_sx_zval C.jet_sx_rep C.jet_sx_zrep.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns C.jet_secp_fe_math C.jet_secp_fe_nv.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 600.

Fixpoint byte_cells (ofs : Z) (n : nat) (v : nat) : list cell :=
  match n with
  | O => []
  | S n => mkcell ofs Mint8unsigned (Some (XL2I (XLv v))) :: byte_cells (ofs + 1) n (S v)
  end.
Definition fe_undef : region :=
  mkreg [mkcell 0 Mint64 None; mkcell 8 Mint64 None; mkcell 16 Mint64 None;
         mkcell 24 Mint64 None; mkcell 32 Mint64 None] true None.

Definition sb_run : option res :=
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 400 f_secp256k1_fe_set_b32
    [XP 0 0; XP 1 0] [fe_undef; mkreg (byte_cells 0 32 0) false None] [] 32.
Definition sb_tree : option res := Eval vm_compute in sb_run.
Definition sb_leaf : sstate :=
  Eval vm_compute in match sb_tree with Some (RDone a _) => a | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition sb_ret : sx :=
  Eval vm_compute in match (stemps sb_leaf)!1%positive with Some x => x | None => XIc Int.zero end.
Lemma sb_run_eq : sb_run = Some (RDone sb_leaf ONormal).
Proof. vm_cast_no_check (eq_refl (Some (RDone sb_leaf ONormal))). Qed.

Ltac pow_facts :=
  pose proof (eq_refl : 2 ^ 4 = 16); pose proof (eq_refl : 2 ^ 8 = 256);
  pose proof (eq_refl : 2 ^ 12 = 4096); pose proof (eq_refl : 2 ^ 16 = 65536);
  pose proof (eq_refl : 2 ^ 20 = 1048576); pose proof (eq_refl : 2 ^ 24 = 16777216);
  pose proof (eq_refl : 2 ^ 28 = 268435456); pose proof (eq_refl : 2 ^ 32 = 4294967296);
  pose proof (eq_refl : 2 ^ 36 = 68719476736); pose proof (eq_refl : 2 ^ 40 = 1099511627776);
  pose proof (eq_refl : 2 ^ 44 = 17592186044416); pose proof (eq_refl : 2 ^ 48 = 281474976710656);
  pose proof (eq_refl : 2 ^ 52 = 4503599627370496);
  pose proof (eq_refl : 2 ^ 104 = 20282409603651670423947251286016);
  pose proof (eq_refl : 2 ^ 156 = 91343852333181432387730302044767688728495783936);
  pose proof (eq_refl : 2 ^ 208 = 411376139330301510538742295639337626245683966408394965837152256).

Ltac lor1 :=
  match goal with
  | |- context[Z.lor ?x (?y * 2 ^ ?k)] =>
      lazymatch x with
      | context[Z.lor _ _] => fail
      | _ => rewrite (lor_shift_add x y k) by lia
      end
  end.

Lemma sb_math bs :
  length bs = 32%nat -> Forall (fun b => 0 <= b <= 255) bs ->
  zcells (fun n => nth n bs 0) (cells0 sb_leaf) = fe_limbs_of (be_val bs) /\
  zval (fun n => nth n bs 0) sb_ret = b2z (Z.ltb (be_val bs) feP).
Proof.
  intros Hlen Hb.
  do 33 (destruct bs as [|? bs]; try discriminate). clear Hlen.
  repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end.
  cbv [zcells cells0 sb_leaf sb_ret sregs hd rcells map cval zval zop zcmp nth Int.unsigned Int64.unsigned Int.intval Int64.intval].
  pow_facts.
  repeat match goal with |- context[?x mod 2 ^ 32] => rewrite (Z.mod_small x (2 ^ 32)) by lia end.
  rewrite !land_15.
  pose proof (Z.div_mod z24 (2 ^ 4) ltac:(lia)). pose proof (Z.mod_pos_bound z24 (2 ^ 4) ltac:(lia)).
  pose proof (Z.div_mod z11 (2 ^ 4) ltac:(lia)). pose proof (Z.mod_pos_bound z11 (2 ^ 4) ltac:(lia)).
  assert (0 <= z24 / 2 ^ 4 < 16) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
  assert (0 <= z11 / 2 ^ 4 < 16) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
  rewrite (Z.mod_small (z24 / 2 ^ 4) (2 ^ 4)) by lia. rewrite (Z.mod_small (z11 / 2 ^ 4) (2 ^ 4)) by lia.
  set (h24 := z24 / 2 ^ 4) in *. set (l24 := z24 mod 2 ^ 4) in *.
  set (h11 := z11 / 2 ^ 4) in *. set (l11 := z11 mod 2 ^ 4) in *.
  repeat lor1.
  match goal with |- [?l0; ?l1; ?l2; ?l3; ?l4] = _ /\ _ =>
    assert (Hok : fe_limbs_ok l0 l1 l2 l3 l4) by (unfold fe_limbs_ok; lia);
    assert (Hv : fe_val l0 l1 l2 l3 l4 = be_val [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14;
        z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29; z30])
      by (unfold fe_val, be_val; cbn [fold_left]; lia)
  end.
  split; [apply fe_limbs_unique; assumption|].
  rewrite (overflow_flag _ _ _ _ _ Hok), Hv. reflexivity.
Qed.

(** ** From limbs to bytes *)
Fixpoint byte_undef (ofs : Z) (n : nat) : list cell :=
  match n with O => [] | S n => mkcell ofs Mint8unsigned None :: byte_undef (ofs + 1) n end.

Definition gb_run : option res :=
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 400 f_secp256k1_fe_get_b32
    [XP 0 0; XP 1 0] [mkreg (byte_undef 0 32) true None; mkreg (u64_cells 0 (vars5 0)) false None] [] 5.
Definition gb_tree : option res := Eval vm_compute in gb_run.
Definition gb_leaf : sstate :=
  Eval vm_compute in match gb_tree with Some (RDone a _) => a | _ => mkst (PTree.empty sx) [] [] 0 end.
Lemma gb_run_eq : gb_run = Some (RDone gb_leaf ONormal).
Proof. vm_cast_no_check (eq_refl (Some (RDone gb_leaf ONormal))). Qed.

Definition be_bytes (W : Z) : list Z :=
  map (fun j => (W / 2 ^ (8 * (31 - Z.of_nat j))) mod 2 ^ 8) (seq 0 32).

Lemma mod_mod_pow x a c : 0 <= c <= a -> (x mod 2 ^ a) mod 2 ^ c = x mod 2 ^ c.
Proof.
  intros H. symmetry. apply Znumtheory.Zmod_div_mod; try (apply Z.pow_pos_nonneg; lia).
  exists (2 ^ (a - c)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma byte_wrap E : 0 <= E < 2 ^ 8 -> ((E mod 2 ^ 32) mod 2 ^ 8) mod 2 ^ 8 = E.
Proof.
  intros H. change (2 ^ 8) with 256 in *. change (2 ^ 32) with 4294967296.
  rewrite (Z.mod_small E 4294967296) by lia. rewrite (Z.mod_small E 256) by lia. apply Z.mod_small. lia.
Qed.

Lemma be_bytes_eq W :
  be_bytes W =
  [(W / 2 ^ 248) mod 2 ^ 8;
   (W / 2 ^ 240) mod 2 ^ 8;
   (W / 2 ^ 232) mod 2 ^ 8;
   (W / 2 ^ 224) mod 2 ^ 8;
   (W / 2 ^ 216) mod 2 ^ 8;
   (W / 2 ^ 208) mod 2 ^ 8;
   (W / 2 ^ 200) mod 2 ^ 8;
   (W / 2 ^ 192) mod 2 ^ 8;
   (W / 2 ^ 184) mod 2 ^ 8;
   (W / 2 ^ 176) mod 2 ^ 8;
   (W / 2 ^ 168) mod 2 ^ 8;
   (W / 2 ^ 160) mod 2 ^ 8;
   (W / 2 ^ 152) mod 2 ^ 8;
   (W / 2 ^ 144) mod 2 ^ 8;
   (W / 2 ^ 136) mod 2 ^ 8;
   (W / 2 ^ 128) mod 2 ^ 8;
   (W / 2 ^ 120) mod 2 ^ 8;
   (W / 2 ^ 112) mod 2 ^ 8;
   (W / 2 ^ 104) mod 2 ^ 8;
   (W / 2 ^ 96) mod 2 ^ 8;
   (W / 2 ^ 88) mod 2 ^ 8;
   (W / 2 ^ 80) mod 2 ^ 8;
   (W / 2 ^ 72) mod 2 ^ 8;
   (W / 2 ^ 64) mod 2 ^ 8;
   (W / 2 ^ 56) mod 2 ^ 8;
   (W / 2 ^ 48) mod 2 ^ 8;
   (W / 2 ^ 40) mod 2 ^ 8;
   (W / 2 ^ 32) mod 2 ^ 8;
   (W / 2 ^ 24) mod 2 ^ 8;
   (W / 2 ^ 16) mod 2 ^ 8;
   (W / 2 ^ 8) mod 2 ^ 8;
   (W / 2 ^ 0) mod 2 ^ 8].
Proof. reflexivity. Qed.

Ltac byte_simple :=
  rewrite land_255; rewrite byte_wrap by (apply Z.mod_pos_bound; lia);
  rewrite ?mod_div_mod by lia; rewrite ?mod_mod_pow by lia; rewrite ?div_div_pow by lia;
  rewrite ?Z.pow_0_r, ?Z.div_1_r; reflexivity.

Ltac byte_cross :=
  rewrite !land_15; rewrite mod_div_mod by lia; rewrite (mod_mod_pow _ 52 4) by lia;
  rewrite ?div_div_pow by lia;
  match goal with |- context[Z.lor (?x mod 2 ^ 4) (?y mod 2 ^ 4 * 2 ^ 4)] =>
    pose proof (Z.mod_pos_bound x (2 ^ 4) ltac:(lia)); pose proof (Z.mod_pos_bound y (2 ^ 4) ltac:(lia));
    rewrite (lor_shift_add (x mod 2 ^ 4) (y mod 2 ^ 4) 4) by lia;
    rewrite byte_wrap by (change (2 ^ 8) with 256; change (2 ^ 4) with 16 in *; lia)
  end;
  match goal with |- _ = ?z mod 2 ^ 8 => rewrite (mod256_split z) end;
  rewrite ?div_div_pow by lia; reflexivity.

Lemma gb_math W :
  0 <= W < 2 ^ 256 ->
  zcells (fun n => nth n (fe_limbs_of W) 0) (cells0 gb_leaf) = be_bytes W.
Proof.
  intros HW. rewrite be_bytes_eq.
  cbv [zcells cells0 gb_leaf sregs hd rcells map cval zval zop zcmp nth fe_limbs_of Int.unsigned Int64.unsigned Int.intval Int64.intval].
  repeat (f_equal; [first [byte_simple|byte_cross]|]).
  f_equal. byte_simple.
Qed.
