(** Actual three local allocations of the original opaque public-key loader. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_pubkey_copy
 C.jet_secp_curve_statements C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition pubkey_load_env bs bx b_y:=PTree.set _y (b_y,curve_fe_type)
 (PTree.set _x (bx,curve_fe_type) (PTree.set _s (bs,pubkey_storage_type) empty_env)).
Definition pubkey_load_temps out key:=PTree.set _pubkey key
 (PTree.set _ge out (create_undef_temps (fn_temps f_secp256k1_pubkey_load))).
Lemma pubkey_load_ok:fn_okb f_secp256k1_pubkey_load=true.
Proof. reflexivity. Qed.
Lemma pubkey_load_blocks bs bx b_y:
 blocks_of_env secp_ge (pubkey_load_env bs bx b_y)=[(bs,0,64);(b_y,0,40);(bx,0,40)].
Proof. reflexivity. Qed.
Theorem pubkey_load_entry_owned m out key:
 exists mi bs bx b_y,
 function_entry2 secp_ge f_secp256k1_pubkey_load [out;key] m
  (pubkey_load_env bs bx b_y) (pubkey_load_temps out key) mi /\
 NoDup [bs;bx;b_y] /\
 (forall b,Mem.valid_block m b ->~In b [bs;bx;b_y]) /\
 (forall b hi,In (b,hi) [(bs,64);(bx,40);(b_y,40)] ->Mem.range_perm mi b 0 hi Cur Freeable) /\
 lframe (fun _ _=>True) m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 64) as (m1,bs) eqn:AS.
 destruct (Mem.alloc m1 0 40) as (m2,bx) eqn:AX.
 destruct (Mem.alloc m2 0 40) as (mi,b_y) eqn:AY.
 assert (VS:Mem.valid_block m1 bs) by (eapply Mem.valid_new_block;exact AS).
 assert (VX:Mem.valid_block m2 bx) by (eapply Mem.valid_new_block;exact AX).
 assert (SX:bs<>bx).
 { intro Same;subst bx;exact (Mem.fresh_block_alloc _ _ _ _ _ AX VS). }
 assert (SY:bs<>b_y).
 { intro Same;subst b_y;apply (Mem.fresh_block_alloc _ _ _ _ _ AY).
   eapply Mem.valid_block_alloc;[exact AX|exact VS]. }
 assert (XY:bx<>b_y).
 { intro Same;subst b_y;exact (Mem.fresh_block_alloc _ _ _ _ _ AY VX). }
 assert (Separate:NoDup [bs;bx;b_y]) by (repeat constructor;cbn [In];intuition congruence).
 assert (Old:forall b,Mem.valid_block m b ->~In b [bs;bx;b_y]).
 { intros b Valid [Same|[Same|[Same|[]]]];subst b.
   - exact (Mem.fresh_block_alloc _ _ _ _ _ AS Valid).
   - apply (Mem.fresh_block_alloc _ _ _ _ _ AX);eapply Mem.valid_block_alloc;[exact AS|exact Valid].
   - apply (Mem.fresh_block_alloc _ _ _ _ _ AY);eapply Mem.valid_block_alloc;[exact AX|].
     eapply Mem.valid_block_alloc;[exact AS|exact Valid]. }
 assert (Owned:forall b hi,In (b,hi) [(bs,64);(bx,40);(b_y,40)] ->Mem.range_perm mi b 0 hi Cur Freeable).
 { intros b hi [Same|[Same|[Same|[]]]];inversion Same;subst b hi;intros pos Range.
   - eapply Mem.perm_alloc_1;[exact AY|];eapply Mem.perm_alloc_1;[exact AX|];
     eapply Mem.perm_alloc_2;[exact AS|exact Range].
   - eapply Mem.perm_alloc_1;[exact AY|];eapply Mem.perm_alloc_2;[exact AX|exact Range].
   - eapply Mem.perm_alloc_2;[exact AY|exact Range]. }
 assert (Entry:function_entry2 secp_ge f_secp256k1_pubkey_load [out;key] m
  (pubkey_load_env bs bx b_y) (pubkey_load_temps out key) mi).
 { destruct (fn_okb_true _ pubkey_load_ok) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons with (m1:=m1) (b1:=bs);[exact AS|].
   eapply alloc_variables_cons with (m1:=m2) (b1:=bx);[exact AX|].
   eapply alloc_variables_cons with (m1:=mi) (b1:=b_y);[exact AY|constructor]. }
 exists mi,bs,bx,b_y;split;[exact Entry|];split;[exact Separate|];split;[exact Old|];split;[exact Owned|];split.
 - eapply lframe_trans;[apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact AS|].
   eapply lframe_trans;[apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact AX|].
   apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact AY.
 - split;[eapply entry_keeps_permissions;exact Entry|eapply entry_preserved;exact Entry].
Qed.
