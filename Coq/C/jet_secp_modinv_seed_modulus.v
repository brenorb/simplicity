(** Revalue the real initialized/copy-complete inverse state for either
    modulus. The matrix remains undefined, as in the actual allocation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_u64_transport
 C.jet_secp_modinv_loop_modulus C.jet_secp_modinv_entry_modulus C.jet_secp_modinv_copies_modulus
 C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_seed C.jet_secp_modinv_var_de
 C.jet_secp_modinv_var_fg C.jet_secp_modinv_var_post C.jet_secp_fe_nv C.jet_secp_modinfo_fe_copy
 C.jet_secp_multiply_normalize_bridge C.jet_secp_modinv_de_numeric C.jet_secp_modinv_normalize62_words.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition inv_mod_seed_rho (mu w : nat->int64) n := nth n
 (words5 w++words5(inv_init_word false)++words5(inv_init_word true)++words5 mu++words5 w) Int64.zero.
Definition inv_mod_seed_regs mu := upd (inv_mod_loop_regs mu) 6 inv_seed_matrix.
Lemma inv_mod_seed_matrix_source mu : nth 6 (inv_mod_fg_regs mu) (mkreg [] true None)=inv_seed_matrix.
Proof. reflexivity. Qed.
Lemma inv_mod_seed_shapes mu : map rshape(inv_mod_seed_regs mu)=map rshape(inv_mod_fg_regs mu).
Proof. reflexivity. Qed.

Theorem inv_mod_seed_rep mu w beta m : rep w beta (inv_mod_fg_regs mu) m ->
 rep (inv_mod_seed_rho mu w) beta (inv_mod_seed_regs mu) m.
Proof.
 intros Rep;pose proof Rep as(Len & Sep & Regions);split;[exact Len|];split.
 - eapply rsep_shape;[apply inv_mod_seed_shapes|exact Sep].
 - intros r reg At;assert(R:(r<7)%nat) by(change(r<length(inv_mod_seed_regs mu))%nat;apply nth_error_Some;rewrite At;discriminate).
   destruct r as [|[|[|[|[|[|[|r]]]]]]];try lia;
    cbn [inv_mod_seed_regs inv_mod_loop_regs upd nth_error] in At;injection At as <-.
   + eapply region_u64_transport with(rho:=w) (beta:=beta) (r:=0%nat) (xs:=vars5 0) (ys:=vars5 0);
     try reflexivity;exact(Regions 0%nat _ eq_refl).
   + eapply region_u64_transport with(rho:=w) (beta:=beta) (r:=1%nat)
      (xs:=map XLc(inv_mod_words mu)) (ys:=map XLc(inv_mod_words mu));try reflexivity;exact(Regions 1%nat _ eq_refl).
   + eapply region_u64_transport with(rho:=w) (beta:=beta) (r:=2%nat)
      (xs:=map(inv_init_sx false) [0;1;2;3;4]%nat) (ys:=vars5 5);try reflexivity;exact(Regions 2%nat _ eq_refl).
   + eapply region_u64_transport with(rho:=w) (beta:=beta) (r:=3%nat)
      (xs:=map(inv_init_sx true) [0;1;2;3;4]%nat) (ys:=vars5 10);try reflexivity;exact(Regions 3%nat _ eq_refl).
   + eapply region_u64_transport with(rho:=w) (beta:=beta) (r:=4%nat)
      (xs:=inv_mod_copy_exprs mu false) (ys:=vars5 15);try reflexivity;exact(Regions 4%nat _ eq_refl).
   + eapply region_u64_transport with(rho:=w) (beta:=beta) (r:=5%nat)
      (xs:=inv_mod_copy_exprs mu true) (ys:=vars5 20);try reflexivity;exact(Regions 5%nat _ eq_refl).
   + eapply inv_region_undefined;[repeat constructor|].
     rewrite <-(inv_mod_seed_matrix_source mu);exact(Regions 6%nat _ eq_refl).
Qed.

Lemma inv_mod_seed_de_word mu w high i : (i<5)%nat ->
 de62_array(inv_de_rho(inv_mod_seed_rho mu w)) high i=inv_init_word high i.
Proof. destruct high;destruct i as [|[|[|[|[|i]]]]];intro I;try lia;reflexivity. Qed.
Lemma inv_mod_seed_de_value mu w high : de62_input_value(inv_de_rho(inv_mod_seed_rho mu w)) high=if high then 1 else 0.
Proof. destruct high;reflexivity. Qed.
Lemma inv_mod_seed_fg_word mu w (high : bool) i : (i<5)%nat ->
 inv_mod_seed_rho mu w ((if high then 20 else 15)+i)%nat=if high then w i else mu i.
Proof. destruct high;destruct i as [|[|[|[|[|i]]]]];intro I;try lia;reflexivity. Qed.
Lemma inv_mod_seed_fg_value mu w high : inv_fg_active_value 5 (inv_mod_seed_rho mu w) high=
 norm62_value_z 4 (fun i=>Int64.signed(if high then w i else mu i)).
Proof.
 unfold inv_fg_active_value;apply norm62_value_ext;intros i I;rewrite inv_mod_seed_fg_word by lia;reflexivity.
Qed.
Lemma inv_mod_seed_field_rho w n : inv_mod_seed_rho modinfo_fe_limb w n=inv_seed_rho w n.
Proof. reflexivity. Qed.
Lemma inv_mod_seed_field_regs : inv_mod_seed_regs modinfo_fe_limb=inv_seed_regs.
Proof. reflexivity. Qed.
