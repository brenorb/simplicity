(** Original generic TapTweak entry, including all eleven real local allocations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition taptweak_env bb bi bo bp bt bh bs bc bc1 br br1:=PTree.set __res__1 (br1,Tstruct _sha256_context noattr) (PTree.set __res (br,Tstruct _sha256_context noattr) (PTree.set _ctx__1 (bc1,Tstruct _sha256_context noattr) (PTree.set _ctx (bc,Tstruct _sha256_context noattr) (PTree.set _output_hash (bs,Tstruct _sha256_midstate noattr) (PTree.set _input_hash (bh,Tstruct _sha256_midstate noattr) (PTree.set _taptweakTag (bt,Tstruct _sha256_midstate noattr) (PTree.set _pubkey (bp,Tstruct __2078 noattr) (PTree.set _output_pubkey (bo,Tstruct __6478 noattr) (PTree.set _input_pubkey (bi,Tstruct __6478 noattr) (PTree.set _buf (bb,tarray tuchar 32) (empty_env))))))))))).
Definition taptweak_temps vd vs vt vn:=PTree.set _tagLen vn (PTree.set _tagName__3 vt
 (PTree.set _src vs (PTree.set _dst vd (create_undef_temps (fn_temps f_simplicity_generic_taptweak))))).
Definition taptweak_locals (bb bi bo bp bt bh bs bc bc1 br br1:block):=[bb;bi;bo;bp;bt;bh;bs;bc;bc1;br;br1].
Definition taptweak_storage (bb bi bo bp bt bh bs bc bc1 br br1:block):=[(bb,32);(bi,64);(bo,64);(bp,64);(bt,32);(bh,32);(bs,32);(bc,88);(bc1,88);(br,88);(br1,88)].
Lemma taptweak_entry_ok:fn_okb f_simplicity_generic_taptweak=true.
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

Theorem taptweak_entry m vd vs vt vn:exists mi bb bi bo bp bt bh bs bc bc1 br br1,
 function_entry2 secp_ge f_simplicity_generic_taptweak [vd;vs;vt;vn] m
 (taptweak_env bb bi bo bp bt bh bs bc bc1 br br1) (taptweak_temps vd vs vt vn) mi /\
 NoDup (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1) /\
 (forall b,Mem.valid_block m b ->~In b (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1)) /\
 (forall b hi,In (b,hi) (taptweak_storage bb bi bo bp bt bh bs bc bc1 br br1) ->Mem.range_perm mi b 0 hi Cur Freeable) /\
 lframe (fun _ _=>True) m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 32) as (m1,bb) eqn:A0.
 destruct (Mem.alloc m1 0 64) as (m2,bi) eqn:A1.
 destruct (Mem.alloc m2 0 64) as (m3,bo) eqn:A2.
 destruct (Mem.alloc m3 0 64) as (m4,bp) eqn:A3.
 destruct (Mem.alloc m4 0 32) as (m5,bt) eqn:A4.
 destruct (Mem.alloc m5 0 32) as (m6,bh) eqn:A5.
 destruct (Mem.alloc m6 0 32) as (m7,bs) eqn:A6.
 destruct (Mem.alloc m7 0 88) as (m8,bc) eqn:A7.
 destruct (Mem.alloc m8 0 88) as (m9,bc1) eqn:A8.
 destruct (Mem.alloc m9 0 88) as (m10,br) eqn:A9.
 destruct (Mem.alloc m10 0 88) as (mi,br1) eqn:A10.
 assert (Entry:function_entry2 secp_ge f_simplicity_generic_taptweak [vd;vs;vt;vn] m
 (taptweak_env bb bi bo bp bt bh bs bc bc1 br br1) (taptweak_temps vd vs vt vn) mi).
 { destruct (fn_okb_true _ taptweak_entry_ok) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons with (m1:=m1) (b1:=bb);[exact A0|].
   eapply alloc_variables_cons with (m1:=m2) (b1:=bi);[exact A1|].
   eapply alloc_variables_cons with (m1:=m3) (b1:=bo);[exact A2|].
   eapply alloc_variables_cons with (m1:=m4) (b1:=bp);[exact A3|].
   eapply alloc_variables_cons with (m1:=m5) (b1:=bt);[exact A4|].
   eapply alloc_variables_cons with (m1:=m6) (b1:=bh);[exact A5|].
   eapply alloc_variables_cons with (m1:=m7) (b1:=bs);[exact A6|].
   eapply alloc_variables_cons with (m1:=m8) (b1:=bc);[exact A7|].
   eapply alloc_variables_cons with (m1:=m9) (b1:=bc1);[exact A8|].
   eapply alloc_variables_cons with (m1:=m10) (b1:=br);[exact A9|].
   eapply alloc_variables_cons with (m1:=mi) (b1:=br1);[exact A10|constructor]. }
 assert (Distinct:NoDup (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1)).
 { unfold taptweak_locals;repeat rewrite NoDup_cons_iff;repeat rewrite not_in_cons;
    repeat split;try apply NoDup_nil;try apply in_nil;allocated_distinct. }
 assert (Old:forall b,Mem.valid_block m b ->~In b (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1)).
 { intros b Valid;unfold taptweak_locals;repeat rewrite not_in_cons;repeat split;try apply in_nil;allocated_distinct. }
 exists mi,bb,bi,bo,bp,bt,bh,bs,bc,bc1,br,br1;split;[exact Entry|];split;[exact Distinct|];split;[exact Old|];split.
 - intros b hi Slot;cbn [taptweak_storage In] in Slot;
   repeat match goal with S:_ \/ _ |- _=>destruct S as [S|S] end;try contradiction;
   match goal with S:(_,_) = (_,_) |- _=>inversion S;subst b hi end;
   intros pos Range;allocated_perm Range.
 - split;[allocated_frame|];split;[eapply entry_keeps_permissions;exact Entry|eapply entry_preserved;exact Entry].
Qed.
Lemma taptweak_blocks bb bi bo bp bt bh bs bc bc1 br br1:
 blocks_of_env secp_ge (taptweak_env bb bi bo bp bt bh bs bc bc1 br br1)=
 [(bs,0,32);(bo,0,64);(bc1,0,88);(bc,0,88);(bh,0,32);(bi,0,64);
 (br1,0,88);(br,0,88);(bp,0,64);(bt,0,32);(bb,0,32)].
Proof. reflexivity. Qed.
Theorem taptweak_free m bb bi bo bp bt bh bs bc bc1 br br1:
 NoDup (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1) ->
 (forall b hi,In (b,hi) (taptweak_storage bb bi bo bp bt bh bs bc bc1 br br1) ->Mem.range_perm m b 0 hi Cur Freeable) ->
 exists mf,Mem.free_list m (blocks_of_env secp_ge (taptweak_env bb bi bo bp bt bh bs bc bc1 br br1))=Some mf /\
 lframe (fun b _=>~In b (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1)) m mf /\readonly_preserved m mf.
Proof.
 intros Separate Owned.
 destruct (free_list_exists [(bs,0,32);(bo,0,64);(bc1,0,88);(bc,0,88);(bh,0,32);(bi,0,64);
 (br1,0,88);(br,0,88);(bp,0,64);(bt,0,32);(bb,0,32)] m) as (mf & Frees & Unchanged).
 - clear -Separate;unfold taptweak_locals in Separate;repeat rewrite NoDup_cons_iff in *;cbn [fst In] in *;
   repeat constructor;cbn [fst In];intuition congruence.
 - intros b lo hi Slot;cbn [In] in Slot;repeat destruct Slot as [Slot|Slot];try contradiction;
   inversion Slot;subst b lo hi;apply Owned;clear;cbn [taptweak_storage In];tauto.
 - exists mf;split;[rewrite taptweak_blocks;exact Frees|];split.
   + eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
     intros b pos Outside _;clear -Outside;cbn [taptweak_locals map fst In] in *;tauto.
   + eapply freelist_preserved;exact Frees.
Qed.
