(** Actual 64-byte copy from native local storage into an opaque public key. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_mem C.jet_memcpy_model C.jet_struct_copy_loads
 C.jet_secp_linkage C.jets_secp C.jet_secp_affine_storage C.jet_clight_internal_preserve
 C.jet_secp_sha_absorb_short C.jet_secp_pubkey_copy.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition pubkey_save_copy_stmt:=Scall None
 (Evar _memcpy (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) (tptr tvoid) cc_default))
 [Ebinop Oadd pubkey_opaque_data (Econst_int Int.zero tint) (tptr tuchar);
  Eaddrof (Evar _s pubkey_storage_type) (tptr pubkey_storage_type);
  Esizeof pubkey_storage_type tulong].
Lemma pubkey_save_copy_source:
 match fn_body f_secp256k1_pubkey_save with
 |Sifthenelse _ (Ssequence _ copy) _=>copy|_=>Sskip end=pubkey_save_copy_stmt.
Proof. reflexivity. Qed.
Theorem exec_pubkey_save_copy (Model:memcpy_model) w e le m bs bd:
 e!_s=Some (bs,pubkey_storage_type) ->e!_memcpy=None ->
 le!_pubkey=Some (Vptr bd Ptrofs.zero) ->bd<>bs ->
 Mem.range_perm m bd 0 64 Cur Freeable ->affine_storage_readable m bs 0 w ->
 exists mf,
 Clight2.exec_stmt secp_ge e le m pubkey_save_copy_stmt E0 le mf Out_normal /\
 affine_storage_readable mf bd 0 w /\Mem.range_perm mf bd 0 64 Cur Freeable /\
 lframe (fun b _=>b<>bd) m mf /\readonly_preserved m mf.
Proof.
 intros LocalS Symbol Key Separate Free Source.
 destruct Source as (Base & Align & Max & Read & Loads).
 destruct (Mem.range_perm_loadbytes m bs 0 64 Read) as (bytes & Load).
 assert (Length:Z.of_nat (length bytes)=64).
 { rewrite (Mem.loadbytes_length _ _ _ _ _ Load);reflexivity. }
 assert (Dest:Mem.range_perm m bd 0 64 Cur Writable).
 { intros pos Range;eapply Mem.perm_implies;[apply Free;exact Range|constructor]. }
 assert (VS:Mem.valid_block m bs) by (eapply Mem.perm_valid_block;apply (Read 0);lia).
 assert (VD:Mem.valid_block m bd) by (eapply Mem.perm_valid_block;apply (Free 0);lia).
 assert (Pointer:Ptrofs.unsigned (Ptrofs.repr 0)=0) by (apply Ptrofs.unsigned_repr;lia).
 destruct (Model (genv_genv secp_ge) m bd Ptrofs.zero bs (Ptrofs.repr 0) 64 bytes
  VS VD ltac:(rewrite Pointer;exact Load) ltac:(rewrite Ptrofs.unsigned_zero;exact Dest)
  ltac:(left;congruence)
  ltac:(clear;change Int64.max_unsigned with 18446744073709551615;lia)
  ltac:(rewrite Pointer;lia) ltac:(rewrite Ptrofs.unsigned_zero;clear;change Ptrofs.max_unsigned with 18446744073709551615;lia))
 as (mf & Store & ExternalCall).
 rewrite Ptrofs.unsigned_zero in Store.
 assert (FinalBytes:Mem.loadbytes mf bd 0 64=Some bytes).
 { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ Store) as H;rewrite Length in H;exact H. }
 exists mf;split.
 - unfold pubkey_save_copy_stmt;eapply exec_Scall with
   (vf:=Vptr (secp_symbol_block _memcpy) Ptrofs.zero)
   (vargs:=[Vptr bd Ptrofs.zero;Vptr bs (Ptrofs.repr 0);Vlong (Int64.repr 64)])
   (f:=External (EF_external "memcpy" memcpy_sig)
    (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) (tptr tvoid) cc_default)
   (vres:=Vptr bd Ptrofs.zero).
   + reflexivity.
   + eapply eval_Elvalue;[eapply eval_Evar_global;[exact Symbol|exact secp_sha_memcpy_symbol]|apply deref_loc_reference;reflexivity].
   + eapply eval_Econs with (v1:=Vptr bd Ptrofs.zero).
     { eapply eval_Ebinop;[apply eval_pubkey_data;exact Key|constructor|reflexivity]. }
     { reflexivity. }
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact LocalS|reflexivity|].
     eapply eval_Econs with (v1:=Vlong (Int64.repr 64));[|reflexivity|constructor].
     rewrite <-pubkey_storage_size;apply eval_Esizeof.
   + exact secp_sha_memcpy_funct.
   + reflexivity.
   + apply eval_funcall_external;exact ExternalCall.
 - split.
   + split;[lia|];split;[exists 0;reflexivity|];split.
     { change (64<=18446744073709551615);lia. }
     split.
     { intros pos Range;eapply Mem.perm_implies;[eapply Mem.perm_storebytes_1;[exact Store|apply Free;exact Range]|constructor]. }
     intros i Index;eapply equal_loadbytes_field with (m1:=m) (b1:=bs) (base1:=0)
      (base2:=0) (n:=64) (delta:=8*Z.of_nat i) (bytes:=bytes).
     { lia. }
     { change (8*Z.of_nat i+8<=64);lia. }
     { exact Load. }
     { exact FinalBytes. }
     { change (8|0+8*Z.of_nat i);exists (Z.of_nat i);lia. }
     { exact (Loads i Index). }
   + split.
     { intros pos Range;eapply Mem.perm_storebytes_1;[exact Store|apply Free;exact Range]. }
     split.
     { apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|intros;congruence]. }
     eapply storebytes_preserved;exact Store.
Qed.
