(** Original Schnorr verifier: all nine local allocations and their fresh ownership. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition schnorr_verify_env bp bk ba bng br bx bpk bbuf bf:=PTree.set _overflow (bf,tint) (PTree.set _buf (bbuf,tarray tuchar 32) (PTree.set _r (br,Tstruct __6121 noattr) (PTree.set _rx (bx,Tstruct __5467 noattr) (PTree.set _pkj (ba,Tstruct __6123 noattr) (PTree.set _pk (bpk,Tstruct __6121 noattr) (PTree.set _rj (bp,Tstruct __6123 noattr) (PTree.set _e (bk,Tstruct __5826 noattr) (PTree.set _s (bng,Tstruct __5826 noattr) (empty_env))))))))).
Definition schnorr_verify_temps sig msg key:=
 PTree.set _pubkey key (PTree.set _msglen (Vlong (Int64.repr 32))
 (PTree.set _msg msg (PTree.set _sig64 sig (create_undef_temps (fn_temps f_secp256k1_schnorrsig_verify))))).
Definition schnorr_verify_locals (bp bk ba bng br bx bpk bbuf bf:block):=[bp;bk;ba;bng;br;bx;bpk;bbuf;bf].
Definition schnorr_verify_storage (bp bk ba bng br bx bpk bbuf bf:block):=[(bp,128);(bk,32);(ba,128);(bng,32);(br,88);(bx,40);(bpk,88);(bbuf,32);(bf,4)].
Lemma schnorr_verify_entry_ok:fn_okb f_secp256k1_schnorrsig_verify=true.
Proof. reflexivity. Qed.
Local Ltac allocated_valid := first [assumption |
 match goal with A:Mem.alloc _ _ _=(?mm,?bb) |- Mem.valid_block ?mm ?bb =>
  eapply Mem.valid_new_block;exact A end |
 match goal with A:Mem.alloc _ _ _=(?mm,_) |- Mem.valid_block ?mm _ =>
  eapply Mem.valid_block_alloc;[exact A|allocated_valid] end].
Local Ltac allocated_distinct := first [assumption |
 match goal with A:Mem.alloc _ _ _=(_,?bb) |- ?ba<>?bb =>
  let Eq:=fresh "Eq" in intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ A);
   rewrite <-Eq;allocated_valid end |
 match goal with A:Mem.alloc _ _ _=(_,?ba) |- ?ba<>?bb =>
  let Eq:=fresh "Eq" in intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ A);
   rewrite Eq;allocated_valid end].
Local Ltac allocated_perm Range := first [
 match goal with A:Mem.alloc _ _ _=(?mm,?bb) |- Mem.perm ?mm ?bb _ _ _ =>
  eapply Mem.perm_alloc_2;[exact A|exact Range] end |
 match goal with A:Mem.alloc _ _ _=(?mm,_) |- Mem.perm ?mm _ _ _ _ =>
  eapply Mem.perm_alloc_1;[exact A|allocated_perm Range] end].
Local Ltac allocated_frame := lazymatch goal with |- lframe _ ?ma ?mb =>
 tryif constr_eq ma mb then apply lframe_refl else
 match goal with A:Mem.alloc ma _ _=(?mi,_) |- _ =>
  eapply lframe_trans with (m2:=mi);
   [apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact A|allocated_frame] end end.

Theorem schnorr_verify_entry m sig msg key:exists mi bp bk ba bng br bx bpk bbuf bf,
 function_entry2 secp_ge f_secp256k1_schnorrsig_verify [sig;msg;Vlong (Int64.repr 32);key] m
 (schnorr_verify_env bp bk ba bng br bx bpk bbuf bf) (schnorr_verify_temps sig msg key) mi /\
 NoDup (schnorr_verify_locals bp bk ba bng br bx bpk bbuf bf) /\
 (forall b,Mem.valid_block m b ->~In b (schnorr_verify_locals bp bk ba bng br bx bpk bbuf bf)) /\
 (forall b hi,In (b,hi) (schnorr_verify_storage bp bk ba bng br bx bpk bbuf bf) ->Mem.range_perm mi b 0 hi Cur Freeable) /\
 lframe (fun _ _=>True) m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 32) as (m1,bng) eqn:A0.
 destruct (Mem.alloc m1 0 32) as (m2,bk) eqn:A1.
 destruct (Mem.alloc m2 0 128) as (m3,bp) eqn:A2.
 destruct (Mem.alloc m3 0 88) as (m4,bpk) eqn:A3.
 destruct (Mem.alloc m4 0 128) as (m5,ba) eqn:A4.
 destruct (Mem.alloc m5 0 40) as (m6,bx) eqn:A5.
 destruct (Mem.alloc m6 0 88) as (m7,br) eqn:A6.
 destruct (Mem.alloc m7 0 32) as (m8,bbuf) eqn:A7.
 destruct (Mem.alloc m8 0 4) as (mi,bf) eqn:A8.
 assert (Entry:function_entry2 secp_ge f_secp256k1_schnorrsig_verify [sig;msg;Vlong (Int64.repr 32);key] m
 (schnorr_verify_env bp bk ba bng br bx bpk bbuf bf) (schnorr_verify_temps sig msg key) mi).
 { destruct (fn_okb_true _ schnorr_verify_entry_ok) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons with (m1:=m1) (b1:=bng);[exact A0|].
   eapply alloc_variables_cons with (m1:=m2) (b1:=bk);[exact A1|].
   eapply alloc_variables_cons with (m1:=m3) (b1:=bp);[exact A2|].
   eapply alloc_variables_cons with (m1:=m4) (b1:=bpk);[exact A3|].
   eapply alloc_variables_cons with (m1:=m5) (b1:=ba);[exact A4|].
   eapply alloc_variables_cons with (m1:=m6) (b1:=bx);[exact A5|].
   eapply alloc_variables_cons with (m1:=m7) (b1:=br);[exact A6|].
   eapply alloc_variables_cons with (m1:=m8) (b1:=bbuf);[exact A7|].
   eapply alloc_variables_cons with (m1:=mi) (b1:=bf);[exact A8|constructor]. }
 assert (Distinct:NoDup (schnorr_verify_locals bp bk ba bng br bx bpk bbuf bf)).
 { unfold schnorr_verify_locals;repeat rewrite NoDup_cons_iff;repeat rewrite not_in_cons;
    repeat split;try apply NoDup_nil;try apply in_nil;allocated_distinct. }
 assert (Old:forall b,Mem.valid_block m b ->~In b (schnorr_verify_locals bp bk ba bng br bx bpk bbuf bf)).
 { intros b Valid;unfold schnorr_verify_locals;repeat rewrite not_in_cons;repeat split;try apply in_nil;allocated_distinct. }
 exists mi,bp,bk,ba,bng,br,bx,bpk,bbuf,bf;split;[exact Entry|];split;[exact Distinct|];split;[exact Old|];split.
 - intros b hi Slot;cbn [schnorr_verify_storage In] in Slot;
   repeat match goal with S:_ \/ _ |- _=>destruct S as [S|S] end;try contradiction;
   match goal with S:(_,_) = (_,_) |- _=>inversion S;subst b hi end;
   intros pos Range;allocated_perm Range.
 - split;[allocated_frame|];split;[eapply entry_keeps_permissions;exact Entry|eapply entry_preserved;exact Entry].
Qed.
Lemma schnorr_verify_blocks bp bk ba bng br bx bpk bbuf bf:
 blocks_of_env secp_ge (schnorr_verify_env bp bk ba bng br bx bpk bbuf bf)=
 [(bf,0,4);(bng,0,32);(bk,0,32);(bpk,0,88);(ba,0,128);(bbuf,0,32);(br,0,88);(bx,0,40);(bp,0,128)].
Proof. reflexivity. Qed.
