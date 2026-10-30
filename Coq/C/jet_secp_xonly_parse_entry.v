(** Actual point and field allocations of the original x-only key parser. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements
 C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition xonly_parse_env bp bx:=PTree.set _x (bx,curve_fe_type) (PTree.set _pk (bp,curve_ge_type) empty_env).
Definition xonly_parse_temps key input:=PTree.set _input32 input (PTree.set _pubkey key
 (create_undef_temps (fn_temps f_secp256k1_xonly_pubkey_parse))).
Lemma xonly_parse_ok:fn_okb f_secp256k1_xonly_pubkey_parse=true.
Proof. reflexivity. Qed.
Lemma xonly_parse_blocks bp bx:blocks_of_env secp_ge (xonly_parse_env bp bx)=[(bx,0,40);(bp,0,88)].
Proof. reflexivity. Qed.
Theorem xonly_parse_entry_owned m key input:exists mi bp bx,
 function_entry2 secp_ge f_secp256k1_xonly_pubkey_parse [key;input] m
 (xonly_parse_env bp bx) (xonly_parse_temps key input) mi /\NoDup [bp;bx] /\
 (forall b,Mem.valid_block m b ->~In b [bp;bx]) /\
 Mem.range_perm mi bp 0 88 Cur Freeable /\Mem.range_perm mi bx 0 40 Cur Freeable /\
 lframe (fun _ _=>True) m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 88) as (mp,bp) eqn:AP.
 destruct (Mem.alloc mp 0 40) as (mi,bx) eqn:AX.
 assert (VP:Mem.valid_block mp bp) by (eapply Mem.valid_new_block;exact AP).
 assert (PX:bp<>bx).
 { intro Same;subst bx;exact (Mem.fresh_block_alloc _ _ _ _ _ AX VP). }
 assert (Separate:NoDup [bp;bx]) by (repeat constructor;cbn [In];intuition congruence).
 assert (Old:forall b,Mem.valid_block m b ->~In b [bp;bx]).
 { intros b Valid [Same|[Same|[]]];subst b.
   - exact (Mem.fresh_block_alloc _ _ _ _ _ AP Valid).
   - apply (Mem.fresh_block_alloc _ _ _ _ _ AX);eapply Mem.valid_block_alloc;[exact AP|exact Valid]. }
 assert (Entry:function_entry2 secp_ge f_secp256k1_xonly_pubkey_parse [key;input] m
 (xonly_parse_env bp bx) (xonly_parse_temps key input) mi).
 { destruct (fn_okb_true _ xonly_parse_ok) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons with (m1:=mp) (b1:=bp);[exact AP|].
   eapply alloc_variables_cons with (m1:=mi) (b1:=bx);[exact AX|constructor]. }
 exists mi,bp,bx;split;[exact Entry|];split;[exact Separate|];split;[exact Old|];split.
 - intros pos Range;eapply Mem.perm_alloc_1;[exact AX|];eapply Mem.perm_alloc_2;[exact AP|exact Range].
 - split.
   + intros pos Range;eapply Mem.perm_alloc_2;[exact AX|exact Range].
   + split.
     * eapply lframe_trans;apply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption.
     * split;[eapply entry_keeps_permissions;exact Entry|eapply entry_preserved;exact Entry].
Qed.
