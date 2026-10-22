(** Actual scalar_split_128 into two fresh scalar objects. This shared
    generation dependency is not a public jet registration. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec
 C.jet_sx_rep C.jet_sx_mem C.jet_sx_pure C.jet_secp_linkage C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition scalar_split128_empty :=
 mkreg (map (fun ofs=>mkcell ofs Mint64 None) [0;8;16;24]) true (Some 32).
Definition scalar_split128_input_region (owned : bool) :=
 mkreg (u64_cells 0 [XLv 0;XLv 1;XLv 2;XLv 3]) owned (if owned then Some 32 else None).
Definition scalar_split128_regs owned :=
 [scalar_split128_empty;scalar_split128_empty;
  scalar_split128_input_region owned].
Definition scalar_split128_run owned :=
 xfun (genv_cenv secp_ge) [] [] 100 f_secp256k1_scalar_split_128
 [XP 0 0;XP 1 0;XP 2 0] (scalar_split128_regs owned) [] 4.
Definition scalar_split128_state owned :=
 match scalar_split128_run owned with Some (RDone st _) => st
 | _ =>mkst (PTree.empty sx) [] [] 0 end.
Definition scalar_split128_zero := XI2L Signed (XIc Int.zero).
Definition scalar_split128_output_regs owned :=
 [mkreg (u64_cells 0 [XLv 0;XLv 1;scalar_split128_zero;scalar_split128_zero]) true (Some 32);
  mkreg (u64_cells 0 [XLv 2;XLv 3;scalar_split128_zero;scalar_split128_zero]) true (Some 32);
  scalar_split128_input_region owned].

Lemma scalar_split128_run_eq owned :
 scalar_split128_run owned=Some (RDone (scalar_split128_state owned) ONormal).
Proof. destruct owned;timeout 10 (vm_compute;reflexivity). Qed.
Lemma scalar_split128_return owned : (stemps (scalar_split128_state owned))!1%positive=None.
Proof. destruct owned;reflexivity. Qed.
Lemma scalar_split128_log owned : slog (scalar_split128_state owned)=[].
Proof. destruct owned;reflexivity. Qed.
Lemma scalar_split128_output owned : sregs (scalar_split128_state owned)=scalar_split128_output_regs owned.
Proof. destruct owned;reflexivity. Qed.
Lemma scalar_split128_zero_den rho layout : den rho layout scalar_split128_zero=Vlong Int64.zero.
Proof. reflexivity. Qed.

Lemma scalar_split128_low_loads owned rho beta m :
 rep rho beta (scalar_split128_output_regs owned) m ->
 forall i w,nth_error [rho 0%nat;rho 1%nat;Int64.zero;Int64.zero] i=Some w ->
 Mem.load Mint64 m (blk beta 0) (bas beta 0+8*Z.of_nat i)=Some (Vlong w).
Proof.
 intro Rep.
 pose proof (rep_region rho beta (scalar_split128_output_regs owned) m 0 _ Rep eq_refl) as Region.
 intros i w Nth;destruct i as [|[|[|[|i]]]];cbn [nth_error] in Nth;
   try (destruct i;discriminate Nth);injection Nth as <-.
 all: first [apply (region_load rho beta m 0 _ _ _ (XLv 0) Region) |
   apply (region_load rho beta m 0 _ _ _ (XLv 1) Region) |
   apply (region_load rho beta m 0 _ _ _ scalar_split128_zero Region)].
 all: cbn [scalar_split128_output_regs rcells u64_cells In];auto.
Qed.

Lemma scalar_split128_high_loads owned rho beta m :
 rep rho beta (scalar_split128_output_regs owned) m ->
 forall i w,nth_error [rho 2%nat;rho 3%nat;Int64.zero;Int64.zero] i=Some w ->
 Mem.load Mint64 m (blk beta 1) (bas beta 1+8*Z.of_nat i)=Some (Vlong w).
Proof.
 intro Rep.
 pose proof (rep_region rho beta (scalar_split128_output_regs owned) m 1 _ Rep eq_refl) as Region.
 intros i w Nth;destruct i as [|[|[|[|i]]]];cbn [nth_error] in Nth;
   try (destruct i;discriminate Nth);injection Nth as <-.
 all: first [apply (region_load rho beta m 1 _ _ _ (XLv 2) Region) |
   apply (region_load rho beta m 1 _ _ _ (XLv 3) Region) |
   apply (region_load rho beta m 1 _ _ _ scalar_split128_zero Region)].
 all: cbn [scalar_split128_output_regs rcells u64_cells In];auto.
Qed.

Local Opaque scalar_split128_state.
Theorem eval_scalar_split128_fresh owned rho beta m : rep rho beta (scalar_split128_regs owned) m ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_split_128)
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
   Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef /\
 rep rho beta (scalar_split128_output_regs owned) mf /\
 lframe (fun b pos=>~foot beta (map rshape (scalar_split128_regs owned)) b pos) m mf.
Proof.
 intro Rep.
 destruct (xfun_pure secp_ge [] ltac:(intros;contradiction) 100
  f_secp256k1_scalar_split_128 [XP 0 0;XP 1 0;XP 2 0] (scalar_split128_regs owned) 4
  (RDone (scalar_split128_state owned) ONormal) (scalar_split128_run_eq owned)
  ltac:(cbn [leaves_log_nil];rewrite scalar_split128_log;reflexivity) rho beta m Rep)
  as (mf & result & Call & Final & Return & Shape & Frame).
 cbn [rsel fst] in Return,Final;rewrite scalar_split128_return in Return;subst result.
 change (map (den rho (lay beta)) [XP 0 0;XP 1 0;XP 2 0]) with
 [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));
  Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0));
  Vptr (blk beta 2) (Ptrofs.repr (bas beta 2+0))] in Call.
 rewrite !Z.add_0_r in Call;rewrite scalar_split128_output in Final.
 exists mf;split;[exact Call|];split;assumption.
Qed.

Definition scalar_split128_low rho := Int64.unsigned (rho 0%nat)+2^64*Int64.unsigned (rho 1%nat).
Definition scalar_split128_high rho := Int64.unsigned (rho 2%nat)+2^64*Int64.unsigned (rho 3%nat).
Definition scalar_split128_input_value rho := Int64.unsigned (rho 0%nat)+
 2^64*Int64.unsigned (rho 1%nat)+2^128*Int64.unsigned (rho 2%nat)+
 2^192*Int64.unsigned (rho 3%nat).

Lemma scalar_split128_values rho :
 0<=scalar_split128_low rho<2^128 /\ 0<=scalar_split128_high rho<2^128 /\
 scalar_split128_input_value rho mod 2^128=scalar_split128_low rho /\
 scalar_split128_input_value rho / 2^128=scalar_split128_high rho.
Proof.
 pose proof (Int64.unsigned_range (rho 0%nat)) as B0.
 pose proof (Int64.unsigned_range (rho 1%nat)) as B1.
 pose proof (Int64.unsigned_range (rho 2%nat)) as B2.
 pose proof (Int64.unsigned_range (rho 3%nat)) as B3.
 change Int64.modulus with (2^64) in *.
 assert (Low : 0<=scalar_split128_low rho<2^128) by (unfold scalar_split128_low;lia).
 assert (High : 0<=scalar_split128_high rho<2^128) by (unfold scalar_split128_high;lia).
 assert (Value : scalar_split128_input_value rho=
  scalar_split128_low rho+scalar_split128_high rho*2^128).
 { unfold scalar_split128_input_value,scalar_split128_low,scalar_split128_high;ring. }
 split;[exact Low|];split;[exact High|];rewrite Value;split.
 - rewrite Z.mod_add by lia;apply Z.mod_small;exact Low.
 - rewrite Z.div_add by lia;rewrite Z.div_small by exact Low;lia.
Qed.

Theorem eval_scalar_split128_owned owned rho beta m : rep rho beta (scalar_split128_regs owned) m ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_split_128)
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
   Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef /\
 rep rho beta (scalar_split128_output_regs owned) mf /\
 (forall i w,nth_error [rho 0%nat;rho 1%nat;Int64.zero;Int64.zero] i=Some w ->
  Mem.load Mint64 mf (blk beta 0) (bas beta 0+8*Z.of_nat i)=Some (Vlong w)) /\
 (forall i w,nth_error [rho 2%nat;rho 3%nat;Int64.zero;Int64.zero] i=Some w ->
  Mem.load Mint64 mf (blk beta 1) (bas beta 1+8*Z.of_nat i)=Some (Vlong w)) /\
 Mem.range_perm mf (blk beta 0) 0 32 Cur Freeable /\
 Mem.range_perm mf (blk beta 1) 0 32 Cur Freeable /\
 (owned=true -> Mem.range_perm mf (blk beta 2) 0 32 Cur Freeable) /\
 0<=scalar_split128_low rho<2^128 /\ 0<=scalar_split128_high rho<2^128 /\
 scalar_split128_input_value rho mod 2^128=scalar_split128_low rho /\
 scalar_split128_input_value rho / 2^128=scalar_split128_high rho /\
 lframe (fun b pos=>~foot beta (map rshape (scalar_split128_regs owned)) b pos) m mf.
Proof.
 intro Rep;destruct (eval_scalar_split128_fresh owned rho beta m Rep) as (mf & Call & Final & Frame).
 assert (F0 : Mem.range_perm mf (blk beta 0) 0 32 Cur Freeable).
 { destruct (rep_region rho beta (scalar_split128_output_regs owned) mf 0 _ Final eq_refl)
    as (_ & _ & _ & _ & (_ & _ & Free & _));exact Free. }
 assert (F1 : Mem.range_perm mf (blk beta 1) 0 32 Cur Freeable).
 { destruct (rep_region rho beta (scalar_split128_output_regs owned) mf 1 _ Final eq_refl)
    as (_ & _ & _ & _ & (_ & _ & Free & _));exact Free. }
 assert (F2 : owned=true -> Mem.range_perm mf (blk beta 2) 0 32 Cur Freeable).
 { intro Eq;subst owned.
   destruct (rep_region rho beta (scalar_split128_output_regs true) mf 2 _ Final eq_refl)
    as (_ & _ & _ & _ & (_ & _ & Free & _));exact Free. }
 destruct (scalar_split128_values rho) as (Low & High & Mod & Div).
 exists mf;split;[exact Call|];split;[exact Final|];split;
 [apply scalar_split128_low_loads with owned;exact Final|];split;
 [apply scalar_split128_high_loads with owned;exact Final|];split;[exact F0|];split;[exact F1|];
 split;[exact F2|];
 split;[exact Low|];split;[exact High|];split;[exact Mod|];split;assumption.
Qed.

