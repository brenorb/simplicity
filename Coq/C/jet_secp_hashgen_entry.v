(** Original generator_generate_internal entry: allocate all eleven locals.
    Expose the actual environment, ownership, freshness and old-memory frame. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition hashgen_env bt bp bx bo bs bb bl bc0 bc1 br1 br0 :=
 PTree.set __res__1 (br0,Tstruct _sha256_context noattr)
 (PTree.set __res (br1,Tstruct _sha256_context noattr)
 (PTree.set _sha256_ctx__1 (bc1,Tstruct _sha256_context noattr)
 (PTree.set _sha256_ctx (bc0,Tstruct _sha256_context noattr)
 (PTree.set _blind (bl,Tstruct __5826 noattr)
 (PTree.set _b32 (bb,tarray tuchar 32)
 (PTree.set _sha256_buf (bs,Tstruct _sha256_midstate noattr)
 (PTree.set _overflow (bo,tint)
 (PTree.set _accum (bx,Tstruct __6123 noattr)
 (PTree.set _add (bp,Tstruct __6121 noattr)
 (PTree.set _t (bt,Tstruct __5467 noattr) empty_env)))))))))).
Definition hashgen_entry_temps bg ba oa :=
 PTree.set _blind32 (Vlong Int64.zero) (PTree.set _key32 (Vptr ba oa)
 (PTree.set _gen (Vptr bg Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_generator_generate_internal)))).
Definition hashgen_storage (bt bp bx bo bs bb bl bc0 bc1 br1 br0:block) :=
 [(bt,40);(bp,88);(bx,128);(bo,4);(bs,32);(bb,32);(bl,32);(bc0,88);(bc1,88);(br1,88);(br0,88)].
Definition hashgen_locals (bt bp bx bo bs bb bl bc0 bc1 br1 br0:block) :=
 [bt;bp;bx;bo;bs;bb;bl;bc0;bc1;br1;br0].
Lemma hashgen_entry_ok : fn_okb f_secp256k1_generator_generate_internal=true.
Proof. reflexivity. Qed.
Lemma hashgen_entry_sizes : map (fun p=>sizeof (genv_cenv secp_ge) (snd p))
 (fn_vars f_secp256k1_generator_generate_internal)=[40;88;128;4;32;32;32;88;88;88;88].
Proof. reflexivity. Qed.
Lemma hashgen_blocks bt bp bx bo bs bb bl bc0 bc1 br1 br0 :
 blocks_of_env secp_ge (hashgen_env bt bp bx bo bs bb bl bc0 bc1 br1 br0)=
 [(bo,0,4);(bc1,0,88);(bc0,0,88);(bs,0,32);(bx,0,128);(bp,0,88);
  (br0,0,88);(br1,0,88);(bt,0,40);(bl,0,32);(bb,0,32)].
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

Theorem hashgen_entry m bg ba oa : exists mi bt bp bx bo bs bb bl bc0 bc1 br1 br0,
 function_entry2 secp_ge f_secp256k1_generator_generate_internal
   [Vptr bg Ptrofs.zero;Vptr ba oa;Vlong Int64.zero] m
   (hashgen_env bt bp bx bo bs bb bl bc0 bc1 br1 br0) (hashgen_entry_temps bg ba oa) mi /\
 NoDup (hashgen_locals bt bp bx bo bs bb bl bc0 bc1 br1 br0) /\
 (forall b,Mem.valid_block m b ->~In b (hashgen_locals bt bp bx bo bs bb bl bc0 bc1 br1 br0)) /\
 (forall b hi,In (b,hi) (hashgen_storage bt bp bx bo bs bb bl bc0 bc1 br1 br0) ->
   Mem.range_perm mi b 0 hi Cur Freeable) /\
 lframe (fun _ _=>True) m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 40) as (m1,bt) eqn:AT.
 destruct (Mem.alloc m1 0 88) as (m2,bp) eqn:AP.
 destruct (Mem.alloc m2 0 128) as (m3,bx) eqn:AX.
 destruct (Mem.alloc m3 0 4) as (m4,bo) eqn:AO.
 destruct (Mem.alloc m4 0 32) as (m5,bs) eqn:AS.
 destruct (Mem.alloc m5 0 32) as (m6,bb) eqn:AB.
 destruct (Mem.alloc m6 0 32) as (m7,bl) eqn:AL.
 destruct (Mem.alloc m7 0 88) as (m8,bc0) eqn:AC0.
 destruct (Mem.alloc m8 0 88) as (m9,bc1) eqn:AC1.
 destruct (Mem.alloc m9 0 88) as (m10,br1) eqn:AR1.
 destruct (Mem.alloc m10 0 88) as (mi,br0) eqn:AR0.
 assert (Entry:function_entry2 secp_ge f_secp256k1_generator_generate_internal
   [Vptr bg Ptrofs.zero;Vptr ba oa;Vlong Int64.zero] m
   (hashgen_env bt bp bx bo bs bb bl bc0 bc1 br1 br0) (hashgen_entry_temps bg ba oa) mi).
 { destruct (fn_okb_true _ hashgen_entry_ok) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons with (m1:=m1) (b1:=bt);[exact AT|].
   eapply alloc_variables_cons with (m1:=m2) (b1:=bp);[exact AP|].
   eapply alloc_variables_cons with (m1:=m3) (b1:=bx);[exact AX|].
   eapply alloc_variables_cons with (m1:=m4) (b1:=bo);[exact AO|].
   eapply alloc_variables_cons with (m1:=m5) (b1:=bs);[exact AS|].
   eapply alloc_variables_cons with (m1:=m6) (b1:=bb);[exact AB|].
   eapply alloc_variables_cons with (m1:=m7) (b1:=bl);[exact AL|].
   eapply alloc_variables_cons with (m1:=m8) (b1:=bc0);[exact AC0|].
   eapply alloc_variables_cons with (m1:=m9) (b1:=bc1);[exact AC1|].
   eapply alloc_variables_cons with (m1:=m10) (b1:=br1);[exact AR1|].
   eapply alloc_variables_cons with (m1:=mi) (b1:=br0);[exact AR0|constructor]. }
 assert (Distinct:NoDup (hashgen_locals bt bp bx bo bs bb bl bc0 bc1 br1 br0)).
 { unfold hashgen_locals;repeat rewrite NoDup_cons_iff;repeat rewrite not_in_cons;
     repeat split;try apply NoDup_nil;try apply in_nil;allocated_distinct. }
 assert (Old:forall b,Mem.valid_block m b ->~In b (hashgen_locals bt bp bx bo bs bb bl bc0 bc1 br1 br0)).
 { intros b Valid;unfold hashgen_locals;repeat rewrite not_in_cons;repeat split;try apply in_nil;allocated_distinct. }
 exists mi,bt,bp,bx,bo,bs,bb,bl,bc0,bc1,br1,br0;split;[exact Entry|];split;[exact Distinct|];split;[exact Old|];split.
 - intros b hi Slot;cbn [hashgen_storage In] in Slot;
   repeat match goal with S:_ \/ _ |- _=>destruct S as [S|S] end;try contradiction;
   match goal with S:(_,_) = (_,_) |- _=>inversion S;subst b hi end;
   intros pos Range;allocated_perm Range.
 - split;[allocated_frame|eapply entry_preserved;exact Entry].
Qed.
