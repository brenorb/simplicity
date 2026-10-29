(** Exact entry and cleanup order of the original Schnorr challenge helper.
    The normalized Clight constructor-return slot is a fourth distinct local. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_exec C.jet_clight_internal_frame C.jet_sx_exec C.jet_secp_linkage C.jet_transport.
Require Import C.jets_secp.
Import ListNotations Ctypes Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition schnorr_challenge_context_type:=Tstruct _sha256_context noattr.
Definition schnorr_challenge_state_type:=Tstruct _sha256_midstate noattr.
Definition schnorr_challenge_env bb bs bc br:=
 PTree.set __res (br,schnorr_challenge_context_type)
  (PTree.set _sha (bc,schnorr_challenge_context_type)
   (PTree.set _sha_buf (bs,schnorr_challenge_state_type)
    (PTree.set _buf (bb,tarray tuchar 32) empty_env))).
Definition schnorr_challenge_temps be ba oa bm om bp op:=
 PTree.set _pubkey32 (Vptr bp op)
  (PTree.set _msglen (Vlong (Int64.repr 32))
   (PTree.set _msg (Vptr bm om)
    (PTree.set _r32 (Vptr ba oa)
     (PTree.set _e (Vptr be Ptrofs.zero)
      (create_undef_temps (fn_temps f_secp256k1_schnorrsig_challenge)))))).
Lemma schnorr_challenge_entry m m1 m2 m3 m4 bb bs bc br be ba oa bm om bp op :
 Mem.alloc m 0 32=(m1,bb) ->Mem.alloc m1 0 32=(m2,bs) ->
 Mem.alloc m2 0 88=(m3,bc) ->Mem.alloc m3 0 88=(m4,br) ->
 function_entry2 secp_ge f_secp256k1_schnorrsig_challenge
  [Vptr be Ptrofs.zero;Vptr ba oa;Vptr bm om;Vlong (Int64.repr 32);Vptr bp op]
  m (schnorr_challenge_env bb bs bc br) (schnorr_challenge_temps be ba oa bm om bp op) m4.
Proof.
 intros AB AS AC AR.
 assert (Ok:fn_okb f_secp256k1_schnorrsig_challenge=true) by reflexivity.
 destruct (fn_okb_true _ Ok) as (Vars & Params & Disjoint);constructor;
 [exact Vars|exact Params|exact Disjoint| |reflexivity].
 eapply alloc_variables_cons with (m1:=m1) (b1:=bb);[exact AB|].
 eapply alloc_variables_cons with (m1:=m2) (b1:=bs);[exact AS|].
 eapply alloc_variables_cons with (m1:=m3) (b1:=bc);[exact AC|].
 eapply alloc_variables_cons with (m1:=m4) (b1:=br);[exact AR|constructor].
Qed.

Lemma schnorr_challenge_blocks bb bs bc br : blocks_of_env secp_ge (schnorr_challenge_env bb bs bc br)=
 [(bs,0,32);(bc,0,88);(br,0,88);(bb,0,32)].
Proof. vm_compute;reflexivity. Qed.
Lemma schnorr_challenge_plain bb bs bc br : plain_env (schnorr_challenge_env bb bs bc br).
Proof. unfold schnorr_challenge_env;repeat (apply plain_set;[|reflexivity]);apply plain_empty. Qed.
