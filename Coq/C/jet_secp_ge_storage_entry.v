(** Actual two field allocations in the original affine storage saver. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_curve_statements C.jet_clight_internal_frame C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition ge_storage_env bx b_y:=PTree.set _y (b_y,curve_fe_type)
 (PTree.set _x (bx,curve_fe_type) empty_env).
Definition ge_storage_temps out point:=PTree.set _a point (PTree.set _r out
 (create_undef_temps (fn_temps f_secp256k1_ge_to_storage))).
Lemma ge_storage_ok:fn_okb f_secp256k1_ge_to_storage=true.
Proof. reflexivity. Qed.
Lemma ge_storage_blocks bx b_y:blocks_of_env secp_ge (ge_storage_env bx b_y)=[(b_y,0,40);(bx,0,40)].
Proof. reflexivity. Qed.
Lemma ge_storage_plain bx b_y:plain_env (ge_storage_env bx b_y).
Proof.
 intros id b ty Lookup;unfold ge_storage_env in Lookup.
 repeat rewrite PTree.gsspec in Lookup.
 repeat match type of Lookup with context[if ?D then _ else _]=>destruct D end;
 try discriminate;injection Lookup as <- <-;reflexivity.
Qed.
Theorem ge_storage_entry_owned m out point:
 exists mi bx b_y,
 function_entry2 secp_ge f_secp256k1_ge_to_storage [out;point] m
 (ge_storage_env bx b_y) (ge_storage_temps out point) mi /\
 NoDup [bx;b_y] /\(forall b,Mem.valid_block m b ->~In b [bx;b_y]) /\
 (forall b,In b [bx;b_y] ->Mem.range_perm mi b 0 40 Cur Freeable) /\
 lframe (fun _ _=>True) m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 40) as (mx,bx) eqn:AX.
 destruct (Mem.alloc mx 0 40) as (mi,b_y) eqn:AY.
 assert (VX:Mem.valid_block mx bx) by (eapply Mem.valid_new_block;exact AX).
 assert (XY:bx<>b_y).
 { intro Same;subst b_y;exact (Mem.fresh_block_alloc _ _ _ _ _ AY VX). }
 assert (Separate:NoDup [bx;b_y]) by (repeat constructor;cbn [In];intuition congruence).
 assert (Old:forall b,Mem.valid_block m b ->~In b [bx;b_y]).
 { intros b Valid [Same|[Same|[]]];subst b.
   - exact (Mem.fresh_block_alloc _ _ _ _ _ AX Valid).
   - apply (Mem.fresh_block_alloc _ _ _ _ _ AY);eapply Mem.valid_block_alloc;[exact AX|exact Valid]. }
 assert (Owned:forall b,In b [bx;b_y] ->Mem.range_perm mi b 0 40 Cur Freeable).
 { intros b [Same|[Same|[]]];subst b;intros pos Range.
   - eapply Mem.perm_alloc_1;[exact AY|];eapply Mem.perm_alloc_2;[exact AX|exact Range].
   - eapply Mem.perm_alloc_2;[exact AY|exact Range]. }
 assert (Entry:function_entry2 secp_ge f_secp256k1_ge_to_storage [out;point] m
 (ge_storage_env bx b_y) (ge_storage_temps out point) mi).
 { destruct (fn_okb_true _ ge_storage_ok) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons with (m1:=mx) (b1:=bx);[exact AX|].
   eapply alloc_variables_cons with (m1:=mi) (b1:=b_y);[exact AY|constructor]. }
 exists mi,bx,b_y;split;[exact Entry|];split;[exact Separate|];split;[exact Old|];split;[exact Owned|];split.
 - eapply lframe_trans;[apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact AX|].
   apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact AY.
 - split;[eapply entry_keeps_permissions;exact Entry|eapply entry_preserved;exact Entry].
Qed.
