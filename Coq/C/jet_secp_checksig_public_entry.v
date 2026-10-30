(** Actual public CheckSig entry: eight fresh locals and exact source environment. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition checksig_public_env bl bb bkey bmsg bsig bout bctx bres:=
 PTree.set __res (bres,Tstruct _sha256_context noattr)
 (PTree.set _ctx (bctx,Tstruct _sha256_context noattr)
 (PTree.set _output (bout,Tstruct _sha256_midstate noattr)
 (PTree.set _sig (bsig,tarray tuchar 64) (PTree.set _msg (bmsg,tarray tuchar 64)
 (PTree.set _pubkey (bkey,Tstruct __6478 noattr) (PTree.set _buf (bb,tarray tuchar 32)
 (PTree.set _src (bl,Tstruct _frameItem noattr) empty_env))))))).
Definition checksig_public_temps v_env bd base bs sbase:=
 PTree.set _env v_env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
 (PTree.set _dst (Vptr bd (Ptrofs.repr base)) (create_undef_temps (fn_temps f_simplicity_check_sig_verify)))).
Definition checksig_public_locals (bl bb bkey bmsg bsig bout bctx bres:block):=[bl;bb;bkey;bmsg;bsig;bout;bctx;bres].
Definition checksig_public_storage (bl bb bkey bmsg bsig bout bctx bres:block):=[(bl,16);(bb,32);(bkey,64);(bmsg,64);(bsig,64);(bout,32);(bctx,88);(bres,88)].
Lemma checksig_public_entry_ok:fn_okb f_simplicity_check_sig_verify=true.
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

Theorem checksig_public_entry v_env m bd base bs sbase:exists mi bl bb bkey bmsg bsig bout bctx bres,
 function_entry2 secp_ge f_simplicity_check_sig_verify
 [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m
 (checksig_public_env bl bb bkey bmsg bsig bout bctx bres) (checksig_public_temps v_env bd base bs sbase) mi /\
 NoDup (checksig_public_locals bl bb bkey bmsg bsig bout bctx bres) /\
 (forall b,Mem.valid_block m b ->~In b (checksig_public_locals bl bb bkey bmsg bsig bout bctx bres)) /\
 (forall b hi,In (b,hi) (checksig_public_storage bl bb bkey bmsg bsig bout bctx bres) ->Mem.range_perm mi b 0 hi Cur Freeable) /\
 lframe (fun _ _=>True) m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 16) as (m1,bl) eqn:A0.
 destruct (Mem.alloc m1 0 32) as (m2,bb) eqn:A1.
 destruct (Mem.alloc m2 0 64) as (m3,bkey) eqn:A2.
 destruct (Mem.alloc m3 0 64) as (m4,bmsg) eqn:A3.
 destruct (Mem.alloc m4 0 64) as (m5,bsig) eqn:A4.
 destruct (Mem.alloc m5 0 32) as (m6,bout) eqn:A5.
 destruct (Mem.alloc m6 0 88) as (m7,bctx) eqn:A6.
 destruct (Mem.alloc m7 0 88) as (mi,bres) eqn:A7.
 assert (Entry:function_entry2 secp_ge f_simplicity_check_sig_verify
 [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m
 (checksig_public_env bl bb bkey bmsg bsig bout bctx bres) (checksig_public_temps v_env bd base bs sbase) mi).
 { destruct (fn_okb_true _ checksig_public_entry_ok) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons with (m1:=m1) (b1:=bl);[exact A0|].
   eapply alloc_variables_cons with (m1:=m2) (b1:=bb);[exact A1|].
   eapply alloc_variables_cons with (m1:=m3) (b1:=bkey);[exact A2|].
   eapply alloc_variables_cons with (m1:=m4) (b1:=bmsg);[exact A3|].
   eapply alloc_variables_cons with (m1:=m5) (b1:=bsig);[exact A4|].
   eapply alloc_variables_cons with (m1:=m6) (b1:=bout);[exact A5|].
   eapply alloc_variables_cons with (m1:=m7) (b1:=bctx);[exact A6|].
   eapply alloc_variables_cons with (m1:=mi) (b1:=bres);[exact A7|constructor]. }
 assert (Distinct:NoDup (checksig_public_locals bl bb bkey bmsg bsig bout bctx bres)).
 { unfold checksig_public_locals;repeat rewrite NoDup_cons_iff;repeat rewrite not_in_cons;
    repeat split;try apply NoDup_nil;try apply in_nil;allocated_distinct. }
 assert (Old:forall b,Mem.valid_block m b ->~In b (checksig_public_locals bl bb bkey bmsg bsig bout bctx bres)).
 { intros b Valid;unfold checksig_public_locals;repeat rewrite not_in_cons;repeat split;try apply in_nil;allocated_distinct. }
 exists mi,bl,bb,bkey,bmsg,bsig,bout,bctx,bres;split;[exact Entry|];split;[exact Distinct|];split;[exact Old|];split.
 - intros b hi Slot;cbn [checksig_public_storage In] in Slot;
   repeat match goal with S:_ \/ _ |- _=>destruct S as [S|S] end;try contradiction;
   match goal with S:(_,_) = (_,_) |- _=>inversion S;subst b hi end;
   intros pos Range;allocated_perm Range.
 - split;[allocated_frame|];split;[eapply entry_keeps_permissions;exact Entry|eapply entry_preserved;exact Entry].
Qed.

Lemma checksig_public_blocks bl bb bkey bmsg bsig bout bctx bres:
 blocks_of_env secp_ge (checksig_public_env bl bb bkey bmsg bsig bout bctx bres)=
 [(bout,0,32);(bctx,0,88);(bsig,0,64);(bl,0,16);(bmsg,0,64);(bres,0,88);(bkey,0,64);(bb,0,32)].
Proof. reflexivity. Qed.
Theorem checksig_public_free m bl bb bkey bmsg bsig bout bctx bres:
 NoDup (checksig_public_locals bl bb bkey bmsg bsig bout bctx bres) ->
 (forall b hi,In (b,hi) (checksig_public_storage bl bb bkey bmsg bsig bout bctx bres) ->Mem.range_perm m b 0 hi Cur Freeable) ->
 exists mf,Mem.free_list m (blocks_of_env secp_ge (checksig_public_env bl bb bkey bmsg bsig bout bctx bres))=Some mf /\
 lframe (fun b _=>~In b (checksig_public_locals bl bb bkey bmsg bsig bout bctx bres)) m mf /\readonly_preserved m mf.
Proof.
 intros Separate Owned.
 destruct (free_list_exists [(bout,0,32);(bctx,0,88);(bsig,0,64);(bl,0,16);(bmsg,0,64);(bres,0,88);(bkey,0,64);(bb,0,32)] m) as (mf & Frees & Unchanged).
 - clear -Separate;unfold checksig_public_locals in Separate;repeat rewrite NoDup_cons_iff in *;cbn [fst In] in *;
   repeat constructor;cbn [fst In];intuition congruence.
 - intros b lo hi Slot;cbn [In] in Slot;repeat destruct Slot as [Slot|Slot];try contradiction;
   inversion Slot;subst b lo hi;apply Owned;clear;cbn [checksig_public_storage In];tauto.
 - exists mf;split;[rewrite checksig_public_blocks;exact Frees|];split.
   + eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
     intros b pos Outside _;clear -Outside;cbn [checksig_public_locals map fst In] in *;tauto.
   + eapply freelist_preserved;exact Frees.
Qed.
