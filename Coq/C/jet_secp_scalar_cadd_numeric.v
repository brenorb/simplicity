(** Numeric interpretation of the actual scalar_cadd_bit stores. The helper
    adds the round bit modulo 2^256, including carry through all four limbs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_exec C.jet_secp_linkage C.jets_secp
 C.jet_secp_scalar_cadd_control C.jet_secp_scalar_cadd_function
 C.jet_secp_u128_word_oracle C.jet_secp_scalar_overflow_numeric C.jet_secp_scalar_add_initial
 C.jet_secp_scalar_reduce_numeric C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_limb_bridge C.jet_secp_scalar_negate_canonical C.jet_sx_mem
 C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition cadd_pair_add (p:int64*int64) (x:int64) : int64*int64 :=
 let lo:=Int64.add (fst p) x in
 (lo,Int64.add (snd p) (Int64.repr (Int.signed (if Int64.ltu lo x then Int.one else Int.zero)))).
Definition cadd_machine_words (flag:bool) (rho:nat->int64) : list int64 :=
 let p0:=cadd_pair_add (rho 0%nat,Int64.zero) (cadd_selector_value flag 0) in
 let p1:=cadd_pair_add (cadd_pair_add (snd p0,Int64.zero) (rho 1%nat)) Int64.zero in
 let p2:=cadd_pair_add (cadd_pair_add (snd p1,Int64.zero) (rho 2%nat)) Int64.zero in
 let p3:=cadd_pair_add (cadd_pair_add (snd p2,Int64.zero) (rho 3%nat)) Int64.zero in
 [fst p0;fst p1;fst p2;fst p3].

Lemma cadd_actual_words rho flag : cadd_output_words rho flag=cadd_machine_words flag rho.
Proof. destruct flag;reflexivity. Qed.

Lemma cadd_pair_zero p : cadd_pair_add p Int64.zero=p.
Proof.
 destruct p as [lo hi];unfold cadd_pair_add;cbn [fst snd];rewrite Int64.add_zero.
 assert (Test:Int64.ltu lo Int64.zero=false).
 { unfold Int64.ltu;change ((if zlt (Int64.unsigned lo) 0 then true else false)=false).
   destruct (zlt (Int64.unsigned lo) 0);[pose proof (Int64.unsigned_range lo);lia|reflexivity]. }
 rewrite Test;change ((lo,Int64.add hi Int64.zero)=(lo,hi));rewrite Int64.add_zero;reflexivity.
Qed.

Lemma cadd_pair_from_zero lo x :
 let p:=cadd_pair_add (lo,Int64.zero) x in
 0<=Int64.unsigned (snd p)<=1 /\
 Int64.unsigned (snd p)*2^64+Int64.unsigned (fst p)=Int64.unsigned lo+Int64.unsigned x.
Proof.
 cbv zeta;split.
 - unfold cadd_pair_add;cbn [fst snd];destruct (Int64.ltu (Int64.add lo x) x);
   change (0<=0<=1) || change (0<=1<=1);lia.
 - pose proof (add64_carry_value lo Int64.zero x) as Value.
   change (Int64.unsigned (snd (cadd_pair_add (lo,Int64.zero) x))*2^64+
    Int64.unsigned (fst (cadd_pair_add (lo,Int64.zero) x))=
    (Int64.unsigned lo+Int64.unsigned x) mod 2^128) in Value.
   rewrite Z.mod_small in Value;
    [exact Value|pose proof (Int64.unsigned_range lo);pose proof (Int64.unsigned_range x);
     change Int64.modulus with (2^64) in *;lia].
Qed.

Definition cadd_output_value rho flag := scalar_limb_value (fun i=>nth i (cadd_output_words rho flag) Int64.zero).

Theorem cadd_output_numeric rho flag :
 cadd_output_value rho flag=(scalar_limb_value rho+(if flag then 1 else 0)) mod 2^256.
Proof.
 unfold cadd_output_value;rewrite cadd_actual_words.
 unfold cadd_machine_words;rewrite !cadd_pair_zero.
 set (p0:=cadd_pair_add (rho 0%nat,Int64.zero) (cadd_selector_value flag 0)).
 set (p1:=cadd_pair_add (snd p0,Int64.zero) (rho 1%nat)).
 set (p2:=cadd_pair_add (snd p1,Int64.zero) (rho 2%nat)).
 set (p3:=cadd_pair_add (snd p2,Int64.zero) (rho 3%nat)).
 destruct (cadd_pair_from_zero (rho 0%nat) (cadd_selector_value flag 0)) as (Bound0 & Sum0);fold p0 in Bound0,Sum0.
 destruct (cadd_pair_from_zero (snd p0) (rho 1%nat)) as (Bound1 & Sum1);fold p1 in Bound1,Sum1.
 destruct (cadd_pair_from_zero (snd p1) (rho 2%nat)) as (Bound2 & Sum2);fold p2 in Bound2,Sum2.
 destruct (cadd_pair_from_zero (snd p2) (rho 3%nat)) as (Bound3 & Sum3);fold p3 in Bound3,Sum3.
 assert (Round:Int64.unsigned (cadd_selector_value flag 0)=(if flag then 1 else 0))
  by (destruct flag;reflexivity).
 rewrite Round in Sum0.
 pose proof (scalar_limb_value_range (fun i=>nth i [fst p0;fst p1;fst p2;fst p3] Int64.zero)) as Range.
 unfold scalar_limb_value in *;cbn [nth] in *.
 apply Z.mod_unique with (q:=Int64.unsigned (snd p3));[lia|].
 nia.
Qed.

Corollary cadd_output_exact rho (flag:bool) : scalar_limb_value rho+(if flag then 1 else 0)<2^256 ->
 cadd_output_value rho flag=scalar_limb_value rho+(if flag then 1 else 0).
Proof.
 intro Fits;rewrite cadd_output_numeric;apply Z.mod_small.
 pose proof (scalar_limb_value_range rho);destruct flag;lia.
Qed.

Lemma cadd_output_canonical rho flag :
 map Int64.repr (scalar_limbs_of (cadd_output_value rho flag))=cadd_output_words rho flag.
Proof.
 unfold cadd_output_value.
 assert (Length:length (cadd_output_words rho flag)=4%nat)
  by (unfold cadd_output_words;rewrite map_length;apply cadd_output_length).
 generalize dependent (cadd_output_words rho flag);intros xs Length.
 destruct xs as [|w0 [|w1 [|w2 [|w3 xs]]]];try discriminate.
 destruct xs;[|discriminate].
 unfold scalar_limb_value;cbn [nth];rewrite scalar_limbs_of_four_words.
 cbn [map];rewrite !Int64.repr_unsigned;reflexivity.
Qed.

Theorem eval_scalar_cadd_numeric rho (flag:bool) m b :
 scalar_at m b 0 (scalar_add_values rho 0) -> Mem.range_perm m b 0 32 Cur Freeable ->
 exists mf, Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_cadd_bit)
  [Vptr b Ptrofs.zero;Vint Int.zero;Vint (if flag then Int.one else Int.zero)] E0 mf Vundef /\
 scalar_at mf b 0 (map Int64.repr (scalar_limbs_of ((scalar_limb_value rho+(if flag then 1 else 0)) mod 2^256))) /\
 Mem.range_perm mf b 0 32 Cur Freeable /\ keeps_permissions m mf /\
 readonly_preserved m mf /\ lframe (fun b' _=>b'<>b) m mf.
Proof.
 intros Stored Free;destruct (eval_scalar_cadd_owned flag rho m b Stored Free)
  as (mf & Run & Output & Rest).
 exists mf;split;[exact Run|];split;[|exact Rest].
 rewrite <-cadd_output_numeric,cadd_output_canonical;exact Output.
Qed.

Theorem eval_scalar_cadd_value value (flag:bool) m b : 0<=value<2^256 ->
 scalar_at m b 0 (map Int64.repr (scalar_limbs_of value)) -> Mem.range_perm m b 0 32 Cur Freeable ->
 exists mf, Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_cadd_bit)
  [Vptr b Ptrofs.zero;Vint Int.zero;Vint (if flag then Int.one else Int.zero)] E0 mf Vundef /\
 scalar_at mf b 0 (map Int64.repr (scalar_limbs_of ((value+(if flag then 1 else 0)) mod 2^256))) /\
 Mem.range_perm mf b 0 32 Cur Freeable /\ keeps_permissions m mf /\
 readonly_preserved m mf /\ lframe (fun b' _=>b'<>b) m mf.
Proof.
 intros Range Stored Free.
 assert (Input:scalar_at m b 0 (scalar_add_values (scalar_limb_rho value) 0)) by exact Stored.
 destruct (eval_scalar_cadd_numeric (scalar_limb_rho value) flag m b Input Free)
  as (mf & Run & Output & Rest).
 rewrite scalar_limb_rho_value in Output by exact Range.
 exists mf;split;[exact Run|];split;assumption.
Qed.
