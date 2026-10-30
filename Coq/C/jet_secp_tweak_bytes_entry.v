(** Original byte-scalar public-key tweak helper: entry, statements and local cleanup. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_curve_statements C.jet_secp_statement_prefix
 C.jet_sx_exec C.jet_sx_mem C.jet_secp_local_regions C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition tweak_bytes_env bt bf:=PTree.set _overflow (bf,tint)
 (PTree.set _term (bt,Tstruct __5826 noattr) empty_env).
Definition tweak_bytes_temps bk bb:=PTree.set _tweak32 (Vptr bb Ptrofs.zero)
 (PTree.set _p (Vptr bk Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_ec_pubkey_tweak_add_helper))).
Definition tweak_bytes_init:=Sassign (Evar _overflow tint) (Econst_int Int.zero tint).
Definition tweak_bytes_parse:=curve_call _secp256k1_scalar_set_b32 f_secp256k1_scalar_set_b32 None
 [Eaddrof (Evar _term (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
 Etempvar _tweak32 (tptr tuchar);Eaddrof (Evar _overflow tint) (tptr tint)].
Definition tweak_bytes_native:=curve_call _secp256k1_eckey_pubkey_tweak_add f_secp256k1_eckey_pubkey_tweak_add (Some _t'2)
 [Etempvar _p (tptr curve_ge_type);Eaddrof (Evar _term (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr))].
Definition tweak_bytes_guard:=Ssequence (Sset _t'3 (Evar _overflow tint))
 (Sifthenelse (Eunop Onotbool (Etempvar _t'3 tint) tint)
 (Ssequence tweak_bytes_native (Sset _t'1 (Ecast (Etempvar _t'2 tint) tbool)))
 (Sset _t'1 (Econst_int Int.zero tint))).
Definition tweak_bytes_return:=Sreturn (Some (Etempvar _t'1 tint)).
Lemma tweak_bytes_body_source:fn_body f_secp256k1_ec_pubkey_tweak_add_helper=
 Ssequence tweak_bytes_init (Ssequence tweak_bytes_parse (Ssequence tweak_bytes_guard tweak_bytes_return)).
Proof. reflexivity. Qed.
Lemma tweak_bytes_entry_ok:fn_okb f_secp256k1_ec_pubkey_tweak_add_helper=true.
Proof. reflexivity. Qed.
Local Opaque secp_ge.
Theorem tweak_bytes_entry m bk bb:exists mi bt bf,
 function_entry2 secp_ge f_secp256k1_ec_pubkey_tweak_add_helper [Vptr bk Ptrofs.zero;Vptr bb Ptrofs.zero]
 m (tweak_bytes_env bt bf) (tweak_bytes_temps bk bb) mi /\bt<>bf /\
 (forall b,Mem.valid_block m b ->b<>bt /\b<>bf) /\
 Mem.range_perm mi bt 0 32 Cur Freeable /\Mem.range_perm mi bf 0 4 Cur Freeable /\
 lframe (fun _ _=>True) m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 32) as (m1,bt) eqn:A1.
 destruct (Mem.alloc m1 0 4) as (mi,bf) eqn:A2.
 assert (Entry:function_entry2 secp_ge f_secp256k1_ec_pubkey_tweak_add_helper [Vptr bk Ptrofs.zero;Vptr bb Ptrofs.zero]
 m (tweak_bytes_env bt bf) (tweak_bytes_temps bk bb) mi).
 { destruct (fn_okb_true _ tweak_bytes_entry_ok) as [Vars [Params Disjoint]];constructor;
   [exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons with (m1:=m1) (b1:=bt);[exact A1|].
   eapply alloc_variables_cons with (m1:=mi) (b1:=bf);[exact A2|constructor]. }
 exists mi,bt,bf;split;[exact Entry|];split.
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
Lemma tweak_bytes_blocks bt bf:blocks_of_env secp_ge (tweak_bytes_env bt bf)=[(bf,0,4);(bt,0,32)].
Proof. reflexivity. Qed.
Theorem tweak_bytes_free m bt bf:bt<>bf ->Mem.range_perm m bt 0 32 Cur Freeable ->Mem.range_perm m bf 0 4 Cur Freeable ->
 exists mf,Mem.free_list m (blocks_of_env secp_ge (tweak_bytes_env bt bf))=Some mf /\
 lframe (fun b _=>b<>bt /\b<>bf) m mf /\readonly_preserved m mf.
Proof.
 intros Separate FP FO.
 destruct (free_list_exists [(bf,0,4);(bt,0,32)] m) as (mf & Free & Unchanged).
 - cbn;repeat constructor;cbn;intuition congruence.
 - intros b lo hi [Slot|[Slot|Empty]];try contradiction;inversion Slot;subst;assumption.
 - exists mf;split;[rewrite tweak_bytes_blocks;exact Free|];split.
   + eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
     intros b pos [NP NO] Old;cbn [map fst In];intuition congruence.
   + eapply freelist_preserved;exact Free.
Qed.
