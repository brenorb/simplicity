(** Original unsigned scalar initializer, used by the TapTweak point update. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep C.jet_sx_pure
 C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv C.jet_secp_local_regions
 C.jet_secp_b32_exec C.jet_secp_scalar_get_b32_storage C.jet_clight_internal_preserve C.jet_secp_closed_helpers.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition scalar_set_int_holes:=map (fun i=>mkcell (8*i) Mint64 None) [0;1;2;3].
Definition scalar_set_int_regs:=[mkreg scalar_set_int_holes true (Some 32)].
Definition scalar_set_int_run v:=xfun (genv_cenv secp_ge) [] (int_table secp_pure) 100
 f_secp256k1_scalar_set_int [XP 0 0;XI v] scalar_set_int_regs [] 0.
Definition scalar_set_int_tree:=Eval vm_compute in fun v=>scalar_set_int_run v.
Definition scalar_set_int_state v:=match scalar_set_int_tree v with
 | Some (RDone st _)=>st|_=>mkst (PTree.empty sx) [] [] 0 end.
Definition scalar_set_int_out v:=[XI2L Unsigned (XI v);XI2L Signed (XIc Int.zero);XI2L Signed (XIc Int.zero);XI2L Signed (XIc Int.zero)].
Lemma scalar_set_int_run_eq v:scalar_set_int_run v=Some (RDone (scalar_set_int_state v) ONormal).
Proof. reflexivity. Qed.
Lemma scalar_set_int_output v:sregs (scalar_set_int_state v)=[mkreg (u64_cells 0 (scalar_set_int_out v)) true (Some 32)].
Proof. reflexivity. Qed.
Lemma scalar_set_int_log v:slog (scalar_set_int_state v)=[].
Proof. reflexivity. Qed.
Lemma scalar_set_int_return v:(stemps (scalar_set_int_state v))!1%positive=None.
Proof. reflexivity. Qed.
Lemma scalar_set_int_initial rho m b:Mem.range_perm m b 0 32 Cur Freeable ->rep rho [(b,0)] scalar_set_int_regs m.
Proof.
 intro Owned;apply (rep_add _ [] [] m b 0);[apply rep_nil|cbn;tauto|].
 unfold scalar_set_int_regs;cbn [hd];unfold region_ok;cbn [rcells rw rfree bas blk lay nth fst snd length app].
 split;[lia|];split;[eapply Mem.perm_valid_block;apply (Owned 0);lia|];split;[reflexivity|];split.
 - apply Forall_forall;intros c Member;cbn [scalar_set_int_holes map In] in Member;
   repeat destruct Member as [Member|Member];try contradiction;subst c;apply writable_undefined_cell;
   cbn [bas blk lay nth fst snd size_chunk align_chunk];
   try (change Ptrofs.max_unsigned with 18446744073709551615;lia).
   all:try (apply freeable_range_writable;intros pos Range;apply Owned;lia).
   all:match goal with |- (8|?n)=>exists (n/8);reflexivity end.
 - split;[reflexivity|];split;[reflexivity|];split;[exact Owned|];repeat constructor;cbn;lia.
Qed.
Theorem eval_scalar_set_int_owned v m b:Mem.range_perm m b 0 32 Cur Freeable ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_set_int) [Vptr b Ptrofs.zero;Vint v] E0 mf Vundef /\
 scalar_at mf b 0 [Int64.repr (Int.unsigned v);Int64.zero;Int64.zero;Int64.zero] /\
 Mem.range_perm mf b 0 32 Cur Freeable /\lframe (fun bx _=>bx<>b) m mf /\readonly_preserved m mf.
Proof.
 intro Owned;pose (rho:=fun _:nat=>Int64.zero).
 assert (Log:leaves_log_nil (RDone (scalar_set_int_state v) ONormal)=true)
 by (cbn [leaves_log_nil];rewrite scalar_set_int_log;reflexivity).
 destruct (xfun_pure secp_ge secp_pure secp_pure_ok 100 f_secp256k1_scalar_set_int
  [XP 0 0;XI v] scalar_set_int_regs 0 _ (scalar_set_int_run_eq v) Log rho [(b,0)] m
  (scalar_set_int_initial rho m b Owned)) as (mf & result & Call & Output & Return & Storage & Frame).
 cbn [rsel fst] in Output,Return;rewrite scalar_set_int_return in Return;subst result.
 rewrite scalar_set_int_output in Output.
 pose proof (rep_region _ _ _ mf 0 _ Output eq_refl) as Region.
 pose proof Region as (_ & _ & _ & _ & _ & _ & Free & _).
 assert (Words:forall i limb,nth_error [Int64.repr (Int.unsigned v);Int64.zero;Int64.zero;Int64.zero] i=Some limb ->
  Mem.load Mint64 mf b (0+8*Z.of_nat i)=Some (Vlong limb)).
 { intros i limb Nth;destruct i as [|[|[|[|i]]]];cbn [nth_error] in Nth;
   try (destruct i;discriminate Nth);injection Nth as Same;subst limb.
   all:first [eapply (region_load rho [(b,0)] mf 0 _ _ Mint64 (XI2L Unsigned (XI v)) Region)|
              eapply (region_load rho [(b,0)] mf 0 _ _ Mint64 (XI2L Signed (XIc Int.zero)) Region)];
    cbn [rcells u64_cells scalar_set_int_out In];tauto. }
 exists mf;split;[exact Call|];split.
 - split;[reflexivity|];split;[lia|];split;[exists 0;reflexivity|];split;
   [change (32<=18446744073709551615);lia|];split;[|exact Words].
   intros pos Range;eapply Mem.perm_implies;[apply Free;exact Range|constructor].
 - split;[exact Free|];split.
   + eapply lframe_implies;[exact Frame|];intros bx pos Other Valid (r & shape & d & ch & Entry & Member & Block & Range).
     destruct r as [|r];[|destruct r;discriminate].
     apply Other;exact Block.
   + eapply secp_closed_function_preserved with (fd:=f_secp256k1_scalar_set_int);[reflexivity|reflexivity|exact Call].
Qed.
