(** Actual Strauss entry for arbitrary scalar pointers and the original
    preparation prefix for generate.
    The state fields are supplied by ecmult's checked setup, not assumed
    intermediate executions. All nine Strauss locals are allocated here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight Clightdefs ClightBigstep Integers Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_generator_initialize C.jet_secp_generator_zero_global.
Require Import C.jet_secp_generator_globalz_call C.jet_secp_fe_nv.
Require Import C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_add_reader_support.
Require Import C.jet_secp_point_set_bit.
Require Import C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl :=
 PTree.set _na_lam (bl,Tstruct __5826 noattr)
 (PTree.set _na_1 (bn,Tstruct __5826 noattr)
 (PTree.set _tmp (bj,Tstruct __6123 noattr)
 (PTree.set _wnaf_ng_128 (bw128,tarray tint 129)
 (PTree.set _wnaf_ng_1 (bw0,tarray tint 129)
 (PTree.set _ng_128 (b128,Tstruct __5826 noattr)
 (PTree.set _ng_1 (b0,Tstruct __5826 noattr)
 (PTree.set _Z (bz,Tstruct __5467 noattr)
 (PTree.set _tmpa (bt,Tstruct __6121 noattr) empty_env)))))))).
Definition generator_entry_temps bs r a ng :=
 PTree.set _ng ng (PTree.set _na (Vptr generator_zero_block Ptrofs.zero)
 (PTree.set _a a (PTree.set _num (Vlong Int64.one) (PTree.set _r r
 (PTree.set _state (Vptr bs Ptrofs.zero)
 (create_undef_temps (fn_temps f_secp256k1_ecmult_strauss_wnaf))))))).
Definition strauss_entry_temps bs r a na ng :=
 PTree.set _ng ng (PTree.set _na na
 (PTree.set _a a (PTree.set _num (Vlong Int64.one) (PTree.set _r r
 (PTree.set _state (Vptr bs Ptrofs.zero)
 (create_undef_temps (fn_temps f_secp256k1_ecmult_strauss_wnaf))))))).
Definition generator_local_storage (bt bz b0 b128 bw0 bw128 bj bn bl : block) :=
 [(bt,88);(bz,40);(b0,32);(b128,32);(bw0,516);(bw128,516);(bj,128);(bn,32);(bl,32)].

Lemma generator_entry_ok : fn_okb f_secp256k1_ecmult_strauss_wnaf=true.
Proof. reflexivity. Qed.
Lemma generator_local_sizes : map (fun p=>sizeof (genv_cenv secp_ge) (snd p))
 (fn_vars f_secp256k1_ecmult_strauss_wnaf)=[88;40;32;32;516;516;128;32;32].
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

Theorem strauss_entry_owned m bs r a na ng :
 exists mi bt bz b0 b128 bw0 bw128 bj bn bl,
 function_entry2 secp_ge f_secp256k1_ecmult_strauss_wnaf
  [Vptr bs Ptrofs.zero;r;Vlong Int64.one;a;na;ng]
  m (generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl) (strauss_entry_temps bs r a na ng) mi /\
 NoDup [bt;bz;b0;b128;bw0;bw128;bj;bn;bl] /\
 (forall b,Mem.valid_block m b -> ~ In b [bt;bz;b0;b128;bw0;bw128;bj;bn;bl]) /\
 (forall b hi,In (b,hi) (generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm mi b 0 hi Cur Freeable) /\
 lframe (fun _ _=>True) m mi /\ keeps_permissions m mi /\ readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 88) as [m1 bt] eqn:AT.
 destruct (Mem.alloc m1 0 40) as [m2 bz] eqn:AZ.
 destruct (Mem.alloc m2 0 32) as [m3 b0] eqn:A0.
 destruct (Mem.alloc m3 0 32) as [m4 b128] eqn:A128.
 destruct (Mem.alloc m4 0 516) as [m5 bw0] eqn:AW0.
 destruct (Mem.alloc m5 0 516) as [m6 bw128] eqn:AW128.
 destruct (Mem.alloc m6 0 128) as [m7 bj] eqn:AJ.
 destruct (Mem.alloc m7 0 32) as [m8 bn] eqn:AN.
 destruct (Mem.alloc m8 0 32) as [mi bl] eqn:AL.
 assert (Separate:NoDup [bt;bz;b0;b128;bw0;bw128;bj;bn;bl]).
 { repeat rewrite NoDup_cons_iff;repeat rewrite not_in_cons;
    repeat split;try apply NoDup_nil;try apply in_nil;allocated_distinct. }
 assert (Old:forall b,Mem.valid_block m b -> ~ In b [bt;bz;b0;b128;bw0;bw128;bj;bn;bl]).
 { intros b Valid;repeat rewrite not_in_cons;repeat split;try apply in_nil;allocated_distinct. }
 assert (FrameA:lframe (fun _ _=>True) m mi) by allocated_frame.
 assert (Free:forall b hi,In (b,hi) (generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm mi b 0 hi Cur Freeable).
 { intros b hi Slot;cbn [generator_local_storage In] in Slot;
    repeat match goal with H:_ \/ _ |- _ => destruct H as [H|H] end;try contradiction;
    match goal with H:(_,_) = (_,_) |- _ => inversion H;subst b hi end;
    intros pos Range;allocated_perm Range. }
 assert (Entry:function_entry2 secp_ge f_secp256k1_ecmult_strauss_wnaf
  [Vptr bs Ptrofs.zero;r;Vlong Int64.one;a;na;ng]
  m (generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl) (strauss_entry_temps bs r a na ng) mi).
 { destruct (fn_okb_true _ generator_entry_ok) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons with (m1:=m1) (b1:=bt);[exact AT|].
   eapply alloc_variables_cons with (m1:=m2) (b1:=bz);[exact AZ|].
   eapply alloc_variables_cons with (m1:=m3) (b1:=b0);[exact A0|].
   eapply alloc_variables_cons with (m1:=m4) (b1:=b128);[exact A128|].
   eapply alloc_variables_cons with (m1:=m5) (b1:=bw0);[exact AW0|].
   eapply alloc_variables_cons with (m1:=m6) (b1:=bw128);[exact AW128|].
   eapply alloc_variables_cons with (m1:=m7) (b1:=bj);[exact AJ|].
   eapply alloc_variables_cons with (m1:=m8) (b1:=bn);[exact AN|].
   eapply alloc_variables_cons with (m1:=mi) (b1:=bl);[exact AL|constructor]. }
 exists mi,bt,bz,b0,b128,bw0,bw128,bj,bn,bl.
 split;[exact Entry|];split;[exact Separate|];split;[exact Old|];split;[exact Free|];
 split;[exact FrameA|];split.
 - eapply entry_keeps_permissions;exact Entry.
 - eapply entry_preserved;exact Entry.
Qed.

(** Only the local Z object is changed by the original initialization call.
    All other locals retain their initial ownership. *)
Lemma generator_local_storage_keep_z mi mf bt bz b0 b128 bw0 bw128 bj bn bl :
 NoDup [bt;bz;b0;b128;bw0;bw128;bj;bn;bl] ->
 (forall b hi,In (b,hi) (generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm mi b 0 hi Cur Freeable) ->
 Mem.range_perm mf bz 0 40 Cur Freeable -> lframe (fun b _=>b<>bz) mi mf ->
 forall b hi,In (b,hi) (generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm mf b 0 hi Cur Freeable.
Proof.
 intros Separate Free ZFree FrameB b hi Slot.
 assert (Bound:0<hi).
 { cbn [generator_local_storage In] in Slot;
   repeat match goal with H:_ \/ _ |- _ => destruct H as [H|H] end;try contradiction;
   match goal with H:(_,_) = (_,_) |- _ => inversion H;lia end. }
 destruct (peq b bz) as [Eq|Other].
 - subst b.
   assert (Size:hi=40).
   { cbn [generator_local_storage In] in Slot;
     pose proof Separate as Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
     repeat match goal with H:_ \/ _ |- _ => destruct H as [H|H] end;try contradiction;
     match goal with H:(_,_) = (_,_) |- _ => inversion H;subst;intuition congruence end. }
   subst hi;exact ZFree.
 - assert (Valid:Mem.valid_block mi b).
   { eapply Mem.perm_valid_block;apply (Free b hi Slot 0);lia. }
   intros pos Range;apply (proj1 (proj2 FrameB));
    [exact Valid|exact Other|apply (Free b hi Slot);exact Range].
Qed.

Theorem strauss_entry_and_initialize m bs r a na ng :
 exists mi mf bt bz b0 b128 bw0 bw128 bj bn bl,
 function_entry2 secp_ge f_secp256k1_ecmult_strauss_wnaf
  [Vptr bs Ptrofs.zero;r;Vlong Int64.one;a;na;ng]
  m (generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl) (strauss_entry_temps bs r a na ng) mi /\
 Clight2.exec_stmt secp_ge (generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl)
  (strauss_entry_temps bs r a na ng) mi generator_initialize E0
  (generator_initial_temps (strauss_entry_temps bs r a na ng)) mf Out_normal /\
 fe_at mf bz 0 (words5 (point_set_bit_words true)) /\
 NoDup [bt;bz;b0;b128;bw0;bw128;bj;bn;bl] /\
 (forall b,Mem.valid_block m b -> ~ In b [bt;bz;b0;b128;bw0;bw128;bj;bn;bl]) /\
 (forall b hi,In (b,hi) (generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun _ _=>True) m mf /\ keeps_permissions m mf /\ readonly_preserved m mf.
Proof.
 destruct (strauss_entry_owned m bs r a na ng)
  as (mi & bt & bz & b0 & b128 & bw0 & bw128 & bj & bn & bl &
   Entry & Separate & Old & Free & FrameA & KeepA & ReadonlyA).
 destruct (exec_generator_initialize (generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl)
  (strauss_entry_temps bs r a na ng) mi bz eq_refl eq_refl
  (Free bz 40 ltac:(clear;cbn [generator_local_storage In];tauto)))
  as (mf & Init & Field & ZFree & FrameB & ReadonlyB).
 assert (Frame:lframe (fun _ _=>True) m mf).
 { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b).
   - eapply lframe_trans.
     + eapply lframe_implies;[exact FrameA|intros;exact I].
     + eapply lframe_implies;[exact FrameB|].
       intros b pos Valid _ Same;subst b;apply (Old bz Valid);clear;cbn [In];tauto.
   - intros b pos _ Valid;exact Valid. }
 exists mi,mf,bt,bz,b0,b128,bw0,bw128,bj,bn,bl.
 split;[exact Entry|];split;[exact Init|];split;[exact Field|];split;[exact Separate|];
 split;[exact Old|];split.
 - exact (generator_local_storage_keep_z mi mf bt bz b0 b128 bw0 bw128 bj bn bl Separate Free ZFree FrameB).
 - split;[exact Frame|];split.
   + intros b pos k p Perm;apply (proj1 (proj2 Frame));
      [eapply Mem.perm_valid_block;exact Perm|exact I|exact Perm].
   + eapply preserved_trans;[exact ReadonlyA|exact ReadonlyB].
Qed.

Theorem generator_entry_and_prepare m bs bx ba r a ng :
 generator_zero_global_state m ->
 Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr ba Ptrofs.zero) ->
 exists mi mf bt bz b0 b128 bw0 bw128 bj bn bl,
 function_entry2 secp_ge f_secp256k1_ecmult_strauss_wnaf
  [Vptr bs Ptrofs.zero;r;Vlong Int64.one;a;Vptr generator_zero_block Ptrofs.zero;ng]
  m (generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl) (generator_entry_temps bs r a ng) mi /\
 Clight2.exec_stmt secp_ge (generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl)
  (generator_entry_temps bs r a ng) mi generator_prepare_non_generator E0
  (generator_ready_temps (generator_entry_temps bs r a ng)
   (Vptr ba Ptrofs.zero) (Vptr bx Ptrofs.zero)) mf Out_normal /\
 fe_at mf bz 0 (words5 (point_set_bit_words true)) /\
 NoDup [bt;bz;b0;b128;bw0;bw128;bj;bn;bl] /\
 (forall b,Mem.valid_block m b -> ~ In b [bt;bz;b0;b128;bw0;bw128;bj;bn;bl]) /\
 (forall b hi,In (b,hi) (generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>b<>bz) m mf /\ readonly_preserved mi mf.
Proof.
 intros Zero X A.
 pose proof (generator_zero_global_valid m Zero) as ZeroValid.
 assert (StateValid:Mem.valid_block m bs).
 { eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
    [eapply Mem.load_valid_access;exact X|apply perm_any_N]. }
 destruct (strauss_entry_owned m bs r a (Vptr generator_zero_block Ptrofs.zero) ng)
  as (mi & bt & bz & b0 & b128 & bw0 & bw128 & bj & bn & bl &
   Entry & Separate & Old & Free & FrameA & KeepA & ReadonlyA).
 assert (ZI:scalar_at mi generator_zero_block 0 [Int64.zero;Int64.zero;Int64.zero;Int64.zero]).
 { eapply scalar_at_lframe;[exact (proj1 Zero)|exact FrameA|intros;exact I]. }
 assert (XI:Mem.load Mptr mi bs (0+0)=Some (Vptr bx Ptrofs.zero)).
 { change (Mem.load Mptr mi bs 0=Some (Vptr bx Ptrofs.zero)).
   rewrite (proj1 FrameA Mptr bs 0 StateValid ltac:(intros;exact I));exact X. }
 assert (AI:Mem.load Mptr mi bs (0+8)=Some (Vptr ba Ptrofs.zero)).
 { change (Mem.load Mptr mi bs 8=Some (Vptr ba Ptrofs.zero)).
   rewrite (proj1 FrameA Mptr bs 8 StateValid ltac:(intros;exact I));exact A. }
 assert (NZ:generator_zero_block<>bz).
 { intro Same;apply (Old generator_zero_block ZeroValid);rewrite Same;clear;cbn [In];tauto. }
 assert (SZ:bs<>bz).
 { intro Same;apply (Old bs StateValid);rewrite Same;clear;cbn [In];tauto. }
 destruct (exec_generator_prepare_non_generator
  (generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl) (generator_entry_temps bs r a ng)
  mi bz generator_zero_block 0 bs 0 ba Ptrofs.zero bx Ptrofs.zero
  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
  (Free bz 40 ltac:(cbn [generator_local_storage In];tauto)) NZ SZ ZI ltac:(lia)
  ltac:(change (0+24<=18446744073709551615);lia) AI XI)
  as (mf & Body & Field & ZFree & FrameB & PreservedB).
 exists mi,mf,bt,bz,b0,b128,bw0,bw128,bj,bn,bl;split.
 - exact Entry.
 - split;[exact Body|];split;[exact Field|];split;[exact Separate|];split;[exact Old|];split.
   + exact (generator_local_storage_keep_z mi mf bt bz b0 b128 bw0 bw128 bj bn bl Separate Free ZFree FrameB).
   + split.
     * eapply lframe_trans;[|exact FrameB];eapply lframe_implies;[exact FrameA|];intros;exact I.
     * exact PreservedB.
Qed.
