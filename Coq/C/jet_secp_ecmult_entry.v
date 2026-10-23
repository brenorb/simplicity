(** Original ecmult function entry and state setup, on fresh private objects. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Integers Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.jet_secp_ecmult_state.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition ecmult_env bx ba bp bs :=
 PTree.set _state (bs,Tstruct _secp256k1_strauss_state noattr)
 (PTree.set _ps (bp,tarray (Tstruct _secp256k1_strauss_point_state noattr) 1)
 (PTree.set _pre_a (ba,tarray (Tstruct __6121 noattr) 8)
 (PTree.set _aux (bx,tarray (Tstruct __5467 noattr) 8) empty_env))).
Definition ecmult_temps r a na ng :=
 PTree.set _ng ng (PTree.set _na na (PTree.set _a a (PTree.set _r r
  (create_undef_temps (fn_temps f_secp256k1_ecmult))))).

Lemma ecmult_entry_ok : fn_okb f_secp256k1_ecmult=true.
Proof. reflexivity. Qed.
Lemma ecmult_local_sizes : map (fun p=>sizeof (genv_cenv secp_ge) (snd p))
 (fn_vars f_secp256k1_ecmult)=[320;704;1040;24].
Proof. reflexivity. Qed.

Lemma ecmult_entry m m1 m2 m3 mi bx ba bp bs r a na ng :
 Mem.alloc m 0 320=(m1,bx) -> Mem.alloc m1 0 704=(m2,ba) ->
 Mem.alloc m2 0 1040=(m3,bp) -> Mem.alloc m3 0 24=(mi,bs) ->
 function_entry2 secp_ge f_secp256k1_ecmult [r;a;na;ng] m
  (ecmult_env bx ba bp bs) (ecmult_temps r a na ng) mi.
Proof.
 intros AX AA AP AS;destruct (fn_okb_true _ ecmult_entry_ok) as (Vars & Params & Disjoint).
 constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
 eapply alloc_variables_cons with (m1:=m1) (b1:=bx);[exact AX|].
 eapply alloc_variables_cons with (m1:=m2) (b1:=ba);[exact AA|].
 eapply alloc_variables_cons with (m1:=m3) (b1:=bp);[exact AP|].
 eapply alloc_variables_cons with (m1:=mi) (b1:=bs);[exact AS|constructor].
Qed.

Theorem ecmult_entry_and_state m r a na ng :
 exists mi mf bx ba bp bs,
 function_entry2 secp_ge f_secp256k1_ecmult [r;a;na;ng] m
  (ecmult_env bx ba bp bs) (ecmult_temps r a na ng) mi /\
 Clight2.exec_stmt secp_ge (ecmult_env bx ba bp bs) (ecmult_temps r a na ng)
  mi ecmult_state_initialize E0 (ecmult_temps r a na ng) mf Out_normal /\
 Mem.load Mptr mf bs 0=Some (Vptr bx Ptrofs.zero) /\
 Mem.load Mptr mf bs 8=Some (Vptr ba Ptrofs.zero) /\
 Mem.load Mptr mf bs 16=Some (Vptr bp Ptrofs.zero) /\
 NoDup [bx;ba;bp;bs] /\
 (forall b,Mem.valid_block m b -> ~ In b [bx;ba;bp;bs]) /\
 (forall b hi,In (b,hi) [(bx,320);(ba,704);(bp,1040);(bs,24)] ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 Mem.unchanged_on (fun _ _=>True) m mf.
Proof.
 destruct (Mem.alloc m 0 320) as [m1 bx] eqn:AX.
 destruct (Mem.alloc m1 0 704) as [m2 ba] eqn:AA.
 destruct (Mem.alloc m2 0 1040) as [m3 bp] eqn:AP.
 destruct (Mem.alloc m3 0 24) as [mi bs] eqn:AS.
 assert (Owned:Mem.range_perm mi bs 0 24 Cur Freeable) by
  (intros pos Range;eapply Mem.perm_alloc_2;[exact AS|exact Range]).
 destruct (exec_ecmult_state_initialize (ecmult_env bx ba bp bs) (ecmult_temps r a na ng)
  mi bs bx ba bp ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) Owned)
  as (mf & Init & X & A & P & Free & Frame).
 assert (OldState:forall b,Mem.valid_block m3 b -> b<>bs).
 { intros b Valid ->;exact (Mem.fresh_block_alloc _ _ _ _ _ AS Valid). }
 assert (VX:Mem.valid_block m3 bx).
 { eapply Mem.valid_block_alloc;[exact AP|];eapply Mem.valid_block_alloc;[exact AA|];
    eapply Mem.valid_new_block;exact AX. }
 assert (VA:Mem.valid_block m3 ba).
 { eapply Mem.valid_block_alloc;[exact AP|];eapply Mem.valid_new_block;exact AA. }
 assert (VP:Mem.valid_block m3 bp) by (eapply Mem.valid_new_block;exact AP).
 assert (XA:bx<>ba).
 { intro Eq;subst ba;apply (Mem.fresh_block_alloc _ _ _ _ _ AA).
   eapply Mem.valid_new_block;exact AX. }
 assert (XP:bx<>bp).
 { intro Eq;subst bp;apply (Mem.fresh_block_alloc _ _ _ _ _ AP).
   eapply Mem.valid_block_alloc;[exact AA|];eapply Mem.valid_new_block;exact AX. }
 assert (APart:ba<>bp).
 { intro Eq;subst bp;apply (Mem.fresh_block_alloc _ _ _ _ _ AP).
   eapply Mem.valid_new_block;exact AA. }
 assert (Separate:NoDup [bx;ba;bp;bs]).
 { pose proof (OldState bx VX);pose proof (OldState ba VA);pose proof (OldState bp VP).
   repeat constructor;cbn [In];intuition congruence. }
 assert (Old:forall b,Mem.valid_block m b -> ~ In b [bx;ba;bp;bs]).
 { intros b Valid [Eq | [Eq | [Eq | [Eq | Eq]]]];try contradiction;subst b.
   - exact (Mem.fresh_block_alloc _ _ _ _ _ AX Valid).
   - apply (Mem.fresh_block_alloc _ _ _ _ _ AA);eapply Mem.valid_block_alloc;[exact AX|exact Valid].
   - apply (Mem.fresh_block_alloc _ _ _ _ _ AP);eapply Mem.valid_block_alloc;[exact AA|];
      eapply Mem.valid_block_alloc;[exact AX|exact Valid].
   - apply (Mem.fresh_block_alloc _ _ _ _ _ AS);eapply Mem.valid_block_alloc;[exact AP|];
      eapply Mem.valid_block_alloc;[exact AA|];eapply Mem.valid_block_alloc;[exact AX|exact Valid]. }
 assert (Keep:forall b hi, b<>bs -> Mem.range_perm mi b 0 hi Cur Freeable ->
  Mem.range_perm mf b 0 hi Cur Freeable).
 { intros b hi Other Perm pos Range;eapply Mem.perm_unchanged_on;
    [exact Frame|exact Other|apply Perm;exact Range]. }
 exists mi,mf,bx,ba,bp,bs;split.
 - exact (ecmult_entry m m1 m2 m3 mi bx ba bp bs r a na ng AX AA AP AS).
 - split;[exact Init|];split;[exact X|];split;[exact A|];split;[exact P|];
    split;[exact Separate|];split;[exact Old|];split.
   + intros b hi [Eq | [Eq | [Eq | [Eq | Eq]]]];try contradiction;inversion Eq;subst b hi.
     * apply Keep;[apply OldState;exact VX|].
       intros pos Range;eapply Mem.perm_alloc_1;[exact AS|];eapply Mem.perm_alloc_1;[exact AP|];
        eapply Mem.perm_alloc_1;[exact AA|];eapply Mem.perm_alloc_2;[exact AX|exact Range].
     * apply Keep;[apply OldState;exact VA|].
       intros pos Range;eapply Mem.perm_alloc_1;[exact AS|];eapply Mem.perm_alloc_1;[exact AP|];
        eapply Mem.perm_alloc_2;[exact AA|exact Range].
     * apply Keep;[apply OldState;exact VP|].
       intros pos Range;eapply Mem.perm_alloc_1;[exact AS|];eapply Mem.perm_alloc_2;[exact AP|exact Range].
     * exact Free.
   + assert (AllocFrame:Mem.unchanged_on (fun _ _=>True) m mi).
     { eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact AX|].
       eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact AA|].
       eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact AP|].
       eapply Mem.alloc_unchanged_on;exact AS. }
     eapply Mem.unchanged_on_implies with (P:=fun b _=>Mem.valid_block m b).
     * eapply Mem.unchanged_on_trans.
       -- eapply Mem.unchanged_on_implies;[exact AllocFrame|];intros;exact I.
       -- eapply Mem.unchanged_on_implies;[exact Frame|].
          intros b pos Valid _;apply OldState.
          eapply Mem.valid_block_alloc;[exact AP|];eapply Mem.valid_block_alloc;[exact AA|];
           eapply Mem.valid_block_alloc;[exact AX|exact Valid].
     * intros b pos _ Valid;exact Valid.
Qed.
