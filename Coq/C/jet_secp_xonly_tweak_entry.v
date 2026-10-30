(** Original x-only tweak wrapper: exact entry, statement spine and cleanup. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_curve_statements C.jet_secp_statement_prefix
 C.jet_sx_exec C.jet_sx_mem C.jet_clight_nonnull_guard C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition xonly_tweak_env bk:=PTree.set _pk (bk,curve_ge_type) empty_env.
Definition xonly_tweak_temps output input bytes:=PTree.set _tweak32 bytes
 (PTree.set _internal_pubkey input (PTree.set _output_pubkey output
 (create_undef_temps (fn_temps f_secp256k1_xonly_pubkey_tweak_add)))).
Definition xonly_tweak_clear:=Scall None
 (Evar _memset (Tfunction (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil))) (tptr tvoid) cc_default))
 [Etempvar _output_pubkey (tptr (Tstruct __2078 noattr));Econst_int Int.zero tint;Esizeof (Tstruct __2078 noattr) tulong].
Definition xonly_tweak_start_statements:=
 [nonnull_return_zero _output_pubkey (Tstruct __2078 noattr);xonly_tweak_clear;
 nonnull_return_zero _internal_pubkey (Tstruct __6478 noattr);nonnull_return_zero _tweak32 tuchar].
Definition xonly_tweak_pk:=Eaddrof (Evar _pk curve_ge_type) (tptr curve_ge_type).
Definition xonly_tweak_load:=curve_call _secp256k1_xonly_pubkey_load f_secp256k1_xonly_pubkey_load (Some _t'1)
 [xonly_tweak_pk;Etempvar _internal_pubkey (tptr (Tstruct __6478 noattr))].
Definition xonly_tweak_scalar:=curve_call _secp256k1_ec_pubkey_tweak_add_helper f_secp256k1_ec_pubkey_tweak_add_helper (Some _t'3)
 [xonly_tweak_pk;Etempvar _tweak32 (tptr tuchar)].
Definition xonly_tweak_test:=Ssequence
 (Ssequence xonly_tweak_load
 (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
 (Sset _t'2 (Econst_int Int.one tint))
 (Ssequence xonly_tweak_scalar (Sset _t'2 (Ecast (Eunop Onotbool (Etempvar _t'3 tint) tint) tbool)))))
 (Sifthenelse (Etempvar _t'2 tint) (Sreturn (Some (Econst_int Int.zero tint))) Sskip).
Definition xonly_tweak_save:=curve_call _secp256k1_pubkey_save f_secp256k1_pubkey_save None
 [Etempvar _output_pubkey (tptr (Tstruct __2078 noattr));xonly_tweak_pk].
Definition xonly_tweak_finish:=Ssequence xonly_tweak_save (Sreturn (Some (Econst_int Int.one tint))).
Lemma xonly_tweak_body_source:fn_body f_secp256k1_xonly_pubkey_tweak_add=
 statement_sequence xonly_tweak_start_statements (Ssequence xonly_tweak_test xonly_tweak_finish).
Proof. reflexivity. Qed.
Lemma xonly_tweak_blocks bk:blocks_of_env secp_ge (xonly_tweak_env bk)=[(bk,0,88)].
Proof. reflexivity. Qed.
Local Opaque secp_ge.
Theorem xonly_tweak_entry m output input bytes:exists mi bk,
 function_entry2 secp_ge f_secp256k1_xonly_pubkey_tweak_add [output;input;bytes] m
 (xonly_tweak_env bk) (xonly_tweak_temps output input bytes) mi /\
 (forall b,Mem.valid_block m b ->b<>bk) /\Mem.range_perm mi bk 0 88 Cur Freeable /\
 lframe (fun _ _=>True) m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 88) as (mi,bk) eqn:Alloc.
 assert (Entry:function_entry2 secp_ge f_secp256k1_xonly_pubkey_tweak_add [output;input;bytes] m
 (xonly_tweak_env bk) (xonly_tweak_temps output input bytes) mi).
 { assert (OK:fn_okb f_secp256k1_xonly_pubkey_tweak_add=true) by reflexivity.
   destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons;[exact Alloc|constructor]. }
 exists mi,bk;split;[exact Entry|];split.
 - intros b Valid Same;subst b;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Valid).
 - split;[intros pos Range;eapply Mem.perm_alloc_2;[exact Alloc|exact Range]|];split.
   + apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc.
   + split;[eapply entry_keeps_permissions;exact Entry|eapply entry_preserved;exact Entry].
Qed.
Theorem xonly_tweak_free m bk:Mem.range_perm m bk 0 88 Cur Freeable ->exists mf,
 Mem.free_list m (blocks_of_env secp_ge (xonly_tweak_env bk))=Some mf /\
 lframe (fun b _=>b<>bk) m mf /\readonly_preserved m mf.
Proof.
 intro Free;destruct (Mem.range_perm_free m bk 0 88 Free) as (mf & Frees).
 exists mf;split.
 - rewrite xonly_tweak_blocks;cbn [Mem.free_list];rewrite Frees;reflexivity.
 - split;[apply lframe_unchanged;eapply Mem.free_unchanged_on;[exact Frees|intros;congruence]|eapply free_preserved;exact Frees].
Qed.
