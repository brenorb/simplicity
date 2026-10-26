(** Actual public hash_to_curve entry. All four local objects are fresh;
    no initial key, generator, or affine-coordinate contents are required. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition hash_public_env bl bk bg bp :=
 PTree.set _ge (bp,Tstruct __6121 noattr)
 (PTree.set _gen (bg,Tstruct __6563 noattr)
 (PTree.set _key (bk,tarray tuchar 32)
 (PTree.set _src (bl,Tstruct _frameItem noattr) empty_env))).
Definition hash_public_temps v_env bd base bs sbase :=
 PTree.set _env v_env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
 (PTree.set _dst (Vptr bd (Ptrofs.repr base))
 (create_undef_temps (fn_temps f_simplicity_hash_to_curve)))).
Definition hash_public_storage (bl bk bg bp:block) := [(bl,16);(bk,32);(bg,64);(bp,88)].
Definition hash_public_locals (bl bk bg bp:block) := [bl;bk;bg;bp].
Lemma hash_public_entry_ok : fn_okb f_simplicity_hash_to_curve=true.
Proof. reflexivity. Qed.
Lemma hash_public_blocks bl bk bg bp :
 blocks_of_env secp_ge (hash_public_env bl bk bg bp)=
 [(bp,0,88);(bg,0,64);(bk,0,32);(bl,0,16)].
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

Theorem hash_public_entry v_env m bd base bs sbase : exists mi bl bk bg bp,
 function_entry2 secp_ge f_simplicity_hash_to_curve
   [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m
   (hash_public_env bl bk bg bp) (hash_public_temps v_env bd base bs sbase) mi /\
 NoDup (hash_public_locals bl bk bg bp) /\
 (forall b,Mem.valid_block m b ->~In b (hash_public_locals bl bk bg bp)) /\
 (forall b hi,In (b,hi) (hash_public_storage bl bk bg bp) ->
   Mem.range_perm mi b 0 hi Cur Freeable) /\
 lframe (fun _ _=>True) m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 16) as (m1,bl) eqn:AL.
 destruct (Mem.alloc m1 0 32) as (m2,bk) eqn:AK.
 destruct (Mem.alloc m2 0 64) as (m3,bg) eqn:AG.
 destruct (Mem.alloc m3 0 88) as (mi,bp) eqn:AP.
 assert (Entry:function_entry2 secp_ge f_simplicity_hash_to_curve
   [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m
   (hash_public_env bl bk bg bp) (hash_public_temps v_env bd base bs sbase) mi).
 { destruct (fn_okb_true _ hash_public_entry_ok) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons with (m1:=m1) (b1:=bl);[exact AL|].
   eapply alloc_variables_cons with (m1:=m2) (b1:=bk);[exact AK|].
   eapply alloc_variables_cons with (m1:=m3) (b1:=bg);[exact AG|].
   eapply alloc_variables_cons with (m1:=mi) (b1:=bp);[exact AP|constructor]. }
 assert (Distinct:NoDup (hash_public_locals bl bk bg bp)).
 { unfold hash_public_locals;repeat rewrite NoDup_cons_iff;repeat rewrite not_in_cons;
   repeat split;try apply NoDup_nil;try apply in_nil;allocated_distinct. }
 assert (Old:forall b,Mem.valid_block m b ->~In b (hash_public_locals bl bk bg bp)).
 { intros b Valid;unfold hash_public_locals;repeat rewrite not_in_cons;
   repeat split;try apply in_nil;allocated_distinct. }
 exists mi,bl,bk,bg,bp;split;[exact Entry|];split;[exact Distinct|];split;[exact Old|];split.
 - intros b hi Slot;cbn [hash_public_storage In] in Slot;
   repeat match goal with S:_ \/ _ |- _=>destruct S as [S|S] end;try contradiction;
   match goal with S:(_,_) = (_,_) |- _=>inversion S;subst b hi end;
   intros pos Range;allocated_perm Range.
 - split;[allocated_frame|eapply entry_preserved;exact Entry].
Qed.

Lemma hash_public_free m bl bk bg bp : NoDup (hash_public_locals bl bk bg bp) ->
 (forall b hi,In (b,hi) (hash_public_storage bl bk bg bp) ->
   Mem.range_perm m b 0 hi Cur Freeable) -> exists mf,
 Mem.free_list m (blocks_of_env secp_ge (hash_public_env bl bk bg bp))=Some mf /\
 lframe (fun b _=>~In b (hash_public_locals bl bk bg bp)) m mf /\ readonly_preserved m mf.
Proof.
 intros Distinct Free.
 destruct (free_list_exists [(bp,0,88);(bg,0,64);(bk,0,32);(bl,0,16)] m)
   as (mf & Freed & Frame).
 - cbn;unfold hash_public_locals in Distinct;repeat rewrite NoDup_cons_iff in Distinct;
   cbn in Distinct;repeat constructor;cbn;intuition congruence.
 - intros b lo hi Slot;cbn [In] in Slot;
   repeat match goal with S:_ \/ _ |- _=>destruct S as [S|S] end;try contradiction;
   match goal with S:(_,_,_) = (_,_,_) |- _=>inversion S;subst b lo hi end;
   apply Free;clear;cbn [hash_public_storage In];tauto.
 - exists mf;split;[rewrite hash_public_blocks;exact Freed|];split.
   + eapply lframe_implies;[apply lframe_unchanged;exact Frame|].
     intros b ofs Outside Valid;unfold hash_public_locals in Outside;cbn in *;intuition congruence.
   + eapply freelist_preserved;exact Freed.
Qed.
