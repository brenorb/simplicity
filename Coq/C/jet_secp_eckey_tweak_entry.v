(** Original native public-key tweak helper: entry, statements and local cleanup. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_curve_statements C.jet_secp_statement_prefix
 C.jet_sx_exec C.jet_sx_mem C.jet_secp_local_regions C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition eckey_tweak_env bp bo:=PTree.set _one (bo,Tstruct __5826 noattr)
 (PTree.set _pt (bp,Tstruct __6123 noattr) empty_env).
Definition eckey_tweak_temps bk bt:=PTree.set _tweak (Vptr bt Ptrofs.zero)
 (PTree.set _key (Vptr bk Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_eckey_pubkey_tweak_add))).
Definition eckey_tweak_set_ge:=curve_call _secp256k1_gej_set_ge f_secp256k1_gej_set_ge None
 [Eaddrof (Evar _pt (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));Etempvar _key (tptr curve_ge_type)].
Definition eckey_tweak_set_one:=curve_call _secp256k1_scalar_set_int f_secp256k1_scalar_set_int None
 [Eaddrof (Evar _one (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));Econst_int Int.one tint].
Definition eckey_tweak_mult:=curve_call _secp256k1_ecmult f_secp256k1_ecmult None
 [Eaddrof (Evar _pt (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
  Eaddrof (Evar _pt (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
  Eaddrof (Evar _one (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));Etempvar _tweak (tptr (Tstruct __5826 noattr))].
Definition eckey_tweak_guard:=Ssequence
 (curve_call _secp256k1_gej_is_infinity f_secp256k1_gej_is_infinity (Some _t'1)
 [Eaddrof (Evar _pt (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr))])
 (Sifthenelse (Etempvar _t'1 tint) (Sreturn (Some (Econst_int Int.zero tint))) Sskip).
Definition eckey_tweak_affine:=curve_call _secp256k1_ge_set_gej_var f_secp256k1_ge_set_gej_var None
 [Etempvar _key (tptr curve_ge_type);Eaddrof (Evar _pt (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr))].
Definition eckey_tweak_finish:=Ssequence eckey_tweak_guard (Ssequence eckey_tweak_affine (Sreturn (Some (Econst_int Int.one tint)))).
Lemma eckey_tweak_body_source:fn_body f_secp256k1_eckey_pubkey_tweak_add=
 Ssequence eckey_tweak_set_ge (Ssequence eckey_tweak_set_one (Ssequence eckey_tweak_mult eckey_tweak_finish)).
Proof. reflexivity. Qed.
Lemma eckey_tweak_entry_ok:fn_okb f_secp256k1_eckey_pubkey_tweak_add=true.
Proof. reflexivity. Qed.
Local Opaque secp_ge.
Theorem eckey_tweak_entry m bk bt:exists mi bp bo,
 function_entry2 secp_ge f_secp256k1_eckey_pubkey_tweak_add [Vptr bk Ptrofs.zero;Vptr bt Ptrofs.zero]
 m (eckey_tweak_env bp bo) (eckey_tweak_temps bk bt) mi /\bp<>bo /\
 (forall b,Mem.valid_block m b ->b<>bp /\b<>bo) /\
 Mem.range_perm mi bp 0 128 Cur Freeable /\Mem.range_perm mi bo 0 32 Cur Freeable /\
 lframe (fun _ _=>True) m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 128) as (m1,bp) eqn:A1.
 destruct (Mem.alloc m1 0 32) as (mi,bo) eqn:A2.
 assert (Entry:function_entry2 secp_ge f_secp256k1_eckey_pubkey_tweak_add [Vptr bk Ptrofs.zero;Vptr bt Ptrofs.zero]
 m (eckey_tweak_env bp bo) (eckey_tweak_temps bk bt) mi).
 { destruct (fn_okb_true _ eckey_tweak_entry_ok) as [Vars [Params Disjoint]];constructor;
   [exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons with (m1:=m1) (b1:=bp);[exact A1|].
   eapply alloc_variables_cons with (m1:=mi) (b1:=bo);[exact A2|constructor]. }
 exists mi,bp,bo;split;[exact Entry|];split.
 - intro Same;apply (Mem.fresh_block_alloc _ _ _ _ _ A2);rewrite <-Same;eapply Mem.valid_new_block;exact A1.
 - split.
   + intros b Old;split;intro Same;subst b.
     * exact (Mem.fresh_block_alloc _ _ _ _ _ A1 Old).
     * apply (Mem.fresh_block_alloc _ _ _ _ _ A2);eapply Mem.valid_block_alloc;[exact A1|exact Old].
   + split.
     * intros pos Range;eapply Mem.perm_alloc_1;[exact A2|eapply Mem.perm_alloc_2;[exact A1|exact Range]].
     * split;[intros pos Range;eapply Mem.perm_alloc_2;[exact A2|exact Range]|];split.
       -- eapply lframe_trans;apply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption.
       -- split;[eapply entry_keeps_permissions;exact Entry|eapply entry_preserved;exact Entry].
Qed.
Lemma eckey_tweak_blocks bp bo:blocks_of_env secp_ge (eckey_tweak_env bp bo)=[(bo,0,32);(bp,0,128)].
Proof. reflexivity. Qed.
Theorem eckey_tweak_free m bp bo:bp<>bo ->Mem.range_perm m bp 0 128 Cur Freeable ->Mem.range_perm m bo 0 32 Cur Freeable ->
 exists mf,Mem.free_list m (blocks_of_env secp_ge (eckey_tweak_env bp bo))=Some mf /\
 lframe (fun b _=>b<>bp /\b<>bo) m mf /\readonly_preserved m mf.
Proof.
 intros Separate FP FO.
 destruct (free_list_exists [(bo,0,32);(bp,0,128)] m) as (mf & Free & Unchanged).
 - cbn;repeat constructor;cbn;intuition congruence.
 - intros b lo hi [Slot|[Slot|Empty]];try contradiction;inversion Slot;subst;assumption.
 - exists mf;split;[rewrite eckey_tweak_blocks;exact Free|];split.
   + eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
     intros b pos [NP NO] Old;cbn [map fst In];intuition congruence.
   + eapply freelist_preserved;exact Free.
Qed.
