(** Actual 32-byte memcpy at the head of the original tagged SHA initializer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_mem C.jet_memcpy_model C.jet_struct_copy_loads C.jet_uint32_array_init
 C.jet_secp_linkage C.jets_secp C.jet_secp_sha_absorb_short C.jet_secp_generator_sha_start
 C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition tagged_sha_copy:=Scall None
 (Evar _memcpy (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) (tptr tvoid) cc_default))
 [Etempvar _output (tptr tuint);
  Efield (Ederef (Etempvar _iv (tptr (Tstruct _sha256_midstate noattr))) (Tstruct _sha256_midstate noattr)) _s (tarray tuint 8);
  Esizeof (tarray tuint 8) tulong].
Lemma tagged_sha_copy_source:
 match fn_body f_sha256_tagged_init with Ssequence first _=>first|_=>Sskip end=tagged_sha_copy.
Proof. reflexivity. Qed.
Lemma eval_tagged_iv_address e le m biv:
 le!_iv=Some (Vptr biv Ptrofs.zero) ->
 eval_expr secp_ge e le m
 (Efield (Ederef (Etempvar _iv (tptr (Tstruct _sha256_midstate noattr))) (Tstruct _sha256_midstate noattr)) _s (tarray tuint 8))
 (Vptr biv Ptrofs.zero).
Proof.
 intro IV;destruct generator_sha_state_layout as (co & Cenv & Offset).
 eapply eval_Elvalue with (loc:=biv) (ofs:=Ptrofs.zero) (bf:=Full).
 - rewrite <-(Ptrofs.add_zero_l Ptrofs.zero);eapply eval_Efield_struct with (co:=co) (delta:=0).
   + eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact IV|apply deref_loc_copy;reflexivity].
   + reflexivity.
   + exact Cenv.
   + exact Offset.
 - apply deref_loc_reference;reflexivity.
Qed.
Theorem exec_tagged_sha_copy (Model:memcpy_model) regs e le m bs biv:
 length regs=8%nat ->e!_memcpy=None ->le!_output=Some (Vptr bs Ptrofs.zero) ->le!_iv=Some (Vptr biv Ptrofs.zero) ->
 bs<>biv ->Mem.range_perm m bs 0 32 Cur Freeable ->Mem.range_perm m biv 0 32 Cur Readable ->
 uint32_array_at m biv 0 regs ->exists mf bytes,
 Clight2.exec_stmt secp_ge e le m tagged_sha_copy E0 le mf Out_normal /\
 Mem.loadbytes m biv 0 32=Some bytes /\Mem.storebytes m bs 0 bytes=Some mf /\
 uint32_array_at mf bs 0 regs /\keeps_permissions m mf /\
 lframe (fun b _=>b<>bs) m mf /\readonly_preserved m mf.
Proof.
 intros Len Symbol Out IV Separate Free Source Words.
 destruct (Mem.range_perm_loadbytes m biv 0 32 Source) as (bytes & Load).
 assert (Length:Z.of_nat (length bytes)=32) by (rewrite (Mem.loadbytes_length _ _ _ _ _ Load);reflexivity).
 assert (Dest:Mem.range_perm m bs 0 32 Cur Writable).
 { intros pos Range;eapply Mem.perm_implies;[apply Free;exact Range|constructor]. }
 assert (VS:Mem.valid_block m biv) by (eapply Mem.perm_valid_block;apply (Source 0);clear;lia).
 assert (VD:Mem.valid_block m bs) by (eapply Mem.perm_valid_block;apply (Free 0);clear;lia).
 destruct (Model (genv_genv secp_ge) m bs Ptrofs.zero biv Ptrofs.zero 32 bytes VS VD
  ltac:(rewrite Ptrofs.unsigned_zero;exact Load) ltac:(rewrite Ptrofs.unsigned_zero;exact Dest)
  ltac:(left;congruence) ltac:(clear;change Int64.max_unsigned with 18446744073709551615;lia)
  ltac:(rewrite Ptrofs.unsigned_zero;clear;change Ptrofs.max_unsigned with 18446744073709551615;lia)
  ltac:(rewrite Ptrofs.unsigned_zero;clear;change Ptrofs.max_unsigned with 18446744073709551615;lia))
 as (mf & Store & ExternalCall).
 rewrite Ptrofs.unsigned_zero in Store.
 assert (FinalBytes:Mem.loadbytes mf bs 0 32=Some bytes).
 { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ Store) as H;rewrite Length in H;exact H. }
 exists mf,bytes;split.
 - unfold tagged_sha_copy;eapply exec_Scall with (vf:=Vptr (secp_symbol_block _memcpy) Ptrofs.zero)
  (vargs:=[Vptr bs Ptrofs.zero;Vptr biv Ptrofs.zero;Vlong (Int64.repr 32)])
  (f:=External (EF_external "memcpy" memcpy_sig)
   (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) (tptr tvoid) cc_default) (vres:=Vptr bs Ptrofs.zero).
   + reflexivity.
   + eapply eval_Elvalue;[eapply eval_Evar_global;[exact Symbol|exact secp_sha_memcpy_symbol]|apply deref_loc_reference;reflexivity].
   + eapply eval_Econs;[apply eval_Etempvar;exact Out|reflexivity|].
     eapply eval_Econs;[apply eval_tagged_iv_address;exact IV|reflexivity|].
     eapply eval_Econs with (v1:=Vlong (Int64.repr 32));[constructor|reflexivity|constructor].
   + exact secp_sha_memcpy_funct.
   + reflexivity.
   + apply eval_funcall_external;exact ExternalCall.
 - split;[exact Load|];split;[exact Store|];split.
   + intros i x Nth;assert (Index:(i<8)%nat) by (rewrite <-Len;apply nth_error_Some;rewrite Nth;discriminate).
     eapply equal_loadbytes_field with (m1:=m) (b1:=biv) (base1:=0) (base2:=0)
      (n:=32) (delta:=4*Z.of_nat i) (bytes:=bytes).
     * lia.
     * change (4*Z.of_nat i+4<=32);lia.
     * exact Load.
     * exact FinalBytes.
     * change (4|0+4*Z.of_nat i);exists (Z.of_nat i);lia.
     * exact (Words i x Nth).
   + split;[intros b pos k p Perm;eapply Mem.perm_storebytes_1;[exact Store|exact Perm]|];split.
     * apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|intros;congruence].
     * eapply storebytes_preserved;exact Store.
Qed.
