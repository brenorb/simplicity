(** Actual loop-body storage connected to its radix-2^62 recurrence. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clightdefs Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jet_secp_modinv_fg_prefix.
Require Import C.jet_secp_modinv_fg_iteration C.jet_secp_modinv_fg_iteration_prefix.
Require Import C.jet_secp_modinv_fg_index.
Require Import C.jet_secp_i128_shift62_rep C.jet_secp_u128_shift64_rep.
Require Import C.jet_secp_modinv_fg_iteration_arith.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fg_iter_pair_sx (high : bool) k := if high then fg_iter_cg k else fg_iter_cf k.
Definition fg_iter_mask := XLsh Hshru (XLc (Int64.repr (-1))) 2.

Lemma fg_final_low k (high : bool) : (0<k<5)%nat ->
 xload (sregs (fg_iter_final_state k)) (if high then 4 else 3) 0 tulong=
 Some (i128_shift62_lo_sx (fst (fg_iter_pair_sx high k)) (snd (fg_iter_pair_sx high k))).
Proof. destruct high;destruct k as [|[|[|[|[|k]]]]];intro K;try lia;vm_compute;reflexivity. Qed.
Lemma fg_final_high k (high : bool) : (0<k<5)%nat ->
 xload (sregs (fg_iter_final_state k)) (if high then 4 else 3) 8 tulong=
 Some (i128_shift62_hi_sx (snd (fg_iter_pair_sx high k))).
Proof. destruct high;destruct k as [|[|[|[|[|k]]]]];intro K;try lia;vm_compute;reflexivity. Qed.
Lemma fg_final_limb k (high : bool) : (0<k<5)%nat ->
 xload (sregs (fg_iter_final_state k)) (if high then 1 else 0) (8*(Z.of_nat k-1)) tulong=
 Some (XLb Band (fst (fg_iter_pair_sx high k)) fg_iter_mask).
Proof. destruct high;destruct k as [|[|[|[|[|k]]]]];intro K;try lia;vm_compute;reflexivity. Qed.

Definition fg_iter_input (rho : nat->int64) (high : bool) :=
 (rho (if high then 17%nat else 15%nat),rho (if high then 18%nat else 16%nat)).
Definition fg_iter_u (rho : nat->int64) (high : bool) := rho (if high then 12%nat else 10%nat).
Definition fg_iter_v (rho : nat->int64) (high : bool) := rho (if high then 13%nat else 11%nat).
Definition fg_iter_words rho high k :=
 fg_row_words (fg_iter_input rho high) (fg_iter_u rho high) (fg_iter_v rho high) (rho k) (rho (5+k)%nat).
Definition fg_iter_sum rho high k :=
 fg_row_sum (fg_iter_input rho high) (fg_iter_u rho high) (fg_iter_v rho high) (rho k) (rho (5+k)%nat).
Definition fg_iter_bound rho high k :=
 fg_row_bound (fg_iter_input rho high) (fg_iter_u rho high) (fg_iter_v rho high) (rho k) (rho (5+k)%nat).
Definition fg_iter_carry rho high k :=
 fg_row_carry (fg_iter_input rho high) (fg_iter_u rho high) (fg_iter_v rho high) (rho k) (rho (5+k)%nat).
Definition fg_iter_limb rho high k :=
 fg_row_limb (fg_iter_input rho high) (fg_iter_u rho high) (fg_iter_v rho high) (rho k) (rho (5+k)%nat).

Lemma fg_iter_words_den rho beta (high : bool) k :
 den rho beta (fst (fg_iter_pair_sx high k))=Vlong (fst (fg_iter_words rho high k)) /\
 den rho beta (snd (fg_iter_pair_sx high k))=Vlong (snd (fg_iter_words rho high k)).
Proof. destruct high;split;reflexivity. Qed.
Lemma fg_iter_mask_den rho beta : den rho beta fg_iter_mask=Vlong (Int64.repr (2^62-1)).
Proof. reflexivity. Qed.

Lemma fg_iter_carry_low_den rho beta (high : bool) k :
 den rho beta (i128_shift62_lo_sx (fst (fg_iter_pair_sx high k)) (snd (fg_iter_pair_sx high k)))=
 Vlong (fst (fg_iter_carry rho high k)).
Proof.
 rewrite i128_shift62_lo_den,(proj1 (fg_iter_words_den rho beta high k)),
  (proj2 (fg_iter_words_den rho beta high k));reflexivity.
Qed.
Lemma fg_iter_carry_high_den rho beta (high : bool) k :
 den rho beta (i128_shift62_hi_sx (snd (fg_iter_pair_sx high k)))=
 Vlong (snd (fg_iter_carry rho high k)).
Proof. rewrite i128_shift62_hi_den,(proj2 (fg_iter_words_den rho beta high k));reflexivity. Qed.
Lemma fg_iter_limb_den rho beta (high : bool) k :
 den rho beta (XLb Band (fst (fg_iter_pair_sx high k)) fg_iter_mask)=Vlong (fg_iter_limb rho high k).
Proof.
 change (Vlong (Int64.and (il (den rho beta (fst (fg_iter_pair_sx high k))))
  (il (den rho beta fg_iter_mask)))=Vlong (fg_iter_limb rho high k)).
 rewrite (proj1 (fg_iter_words_den rho beta high k)),fg_iter_mask_den;reflexivity.
Qed.

Definition fg_iter_at rho beta m (high : bool) k : Prop :=
 let r:=if high then 4%nat else 3%nat in
 let arr:=if high then 1%nat else 0%nat in
 Mem.load Mint64 m (blk beta r) (bas beta r)=Some (Vlong (fst (fg_iter_carry rho high k))) /\
 Mem.load Mint64 m (blk beta r) (bas beta r+8)=Some (Vlong (snd (fg_iter_carry rho high k))) /\
 Mem.load Mint64 m (blk beta arr) (bas beta arr+8*(Z.of_nat k-1))=Some (Vlong (fg_iter_limb rho high k)) /\
 fg_pair_value (fg_iter_carry rho high k)=fg_iter_sum rho high k/2^62 /\
 Int64.unsigned (fg_iter_limb rho high k)=fg_iter_sum rho high k mod 2^62 /\
 0<=Int64.signed (fg_iter_limb rho high k)<2^62 /\
 Z.abs (fg_pair_value (fg_iter_carry rho high k))<=2^63 /\
 fg_iter_sum rho high k=fg_pair_value (fg_iter_carry rho high k)*2^62+Int64.unsigned (fg_iter_limb rho high k).

Lemma fg_iter_storage rho beta m high k : (0<k<5)%nat ->
 rep rho beta (sregs (fg_iter_final_state k)) m -> fg_iter_bound rho high k ->
 fg_iter_at rho beta m high k.
Proof.
 intros K Rep Bound.
 pose proof (xload_u64_defined_sound rho beta _ m _ _ _ Rep (fg_final_low k high K)) as Low.
 pose proof (xload_u64_defined_sound rho beta _ m _ _ _ Rep (fg_final_high k high K)) as High.
 pose proof (xload_u64_defined_sound rho beta _ m _ _ _ Rep (fg_final_limb k high K)) as Limb.
 rewrite Z.add_0_r,fg_iter_carry_low_den in Low;rewrite fg_iter_carry_high_den in High.
 rewrite fg_iter_limb_den in Limb.
 unfold fg_iter_at;split;[exact Low|];split;[exact High|];split;[exact Limb|].
 exact (fg_row_step_numeric _ _ _ _ _ Bound).
Qed.

Theorem exec_fg_iteration_numeric k rho beta e le m : (0<k<5)%nat ->
 rep rho beta fg_iter_regs m -> tmatch rho beta (fg_iter_temps k) le ->
 ematch beta (snd fg_alloc) e ->
 fg_iter_bound rho false k -> fg_iter_bound rho true k -> exists lef mf,
 Clight2.exec_stmt secp_ge e le m fg_work E0 lef mf Out_normal /\
 fg_iter_at rho beta mf false k /\ fg_iter_at rho beta mf true k /\
 rep rho beta (sregs (fg_iter_final_state k)) mf /\
 tmatch rho beta (stemps (fg_iter_final_state k)) lef /\
 lframe (fun b ofs=>~foot beta (map rshape fg_iter_regs) b ofs) m mf.
Proof.
 intros K Rep Temps Env F G.
 destruct (exec_fg_iteration k rho beta e le m K Rep Temps Env)
  as (lef & mf & Exec & Out & Match & Frame).
 exists lef,mf;split;[exact Exec|];split;[eapply fg_iter_storage;eassumption|];
 split;[eapply fg_iter_storage;eassumption|];split;[exact Out|];split;assumption.
Qed.
