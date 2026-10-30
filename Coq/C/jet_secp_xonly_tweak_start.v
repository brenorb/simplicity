(** Original x-only tweak wrapper's pointer checks and output clear. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_mem C.jet_memset_model C.jet_secp_linkage C.jets_secp
 C.jet_secp_root_chain_owned C.jet_secp_wnaf_memset C.jet_secp_statement_prefix
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Require Import C.jet_clight_nonnull_guard C.jet_secp_xonly_parse_start C.jet_secp_xonly_tweak_entry.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Theorem exec_xonly_tweak_clear (Model:memset_model) e le m bout:
 e!_memset=None ->le!_output_pubkey=Some (Vptr bout Ptrofs.zero) ->
 Mem.range_perm m bout 0 64 Cur Freeable ->exists mz,
 Clight2.exec_stmt secp_ge e le m xonly_tweak_clear E0 le mz Out_normal /\
 Mem.range_perm mz bout 0 64 Cur Freeable /\keeps_permissions m mz /\
 lframe (fun b _=>b<>bout) m mz /\readonly_preserved m mz.
Proof.
 intros Symbol Key Free.
 assert (Valid:Mem.valid_block m bout) by (eapply Mem.perm_valid_block;apply (Free 0);lia).
 assert (Writable:Mem.range_perm m bout 0 64 Cur Writable).
 { intros pos Range;eapply Mem.perm_implies;[apply Free;exact Range|constructor]. }
 destruct (Model secp_ge m bout Ptrofs.zero Int.zero 64 Valid Writable ltac:(lia)) as (mz & Store & Ext).
 rewrite Ptrofs.unsigned_zero in Store.
 destruct memset_linked as (bf & Sym & Funct).
 exists mz;split.
 - unfold xonly_tweak_clear;eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
   (vargs:=[Vptr bout Ptrofs.zero;Vint Int.zero;Vlong (Int64.repr 64)])
   (f:=External (EF_external "memset" memset_sig)
    (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil))) (tptr tvoid) cc_default)
   (vres:=Vptr bout Ptrofs.zero).
   + reflexivity.
   + eapply eval_Elvalue;[eapply eval_Evar_global;[exact Symbol|exact Sym]|apply deref_loc_reference;reflexivity].
   + eapply eval_Econs;[apply eval_Etempvar;exact Key|reflexivity|].
     eapply eval_Econs;[constructor|reflexivity|].
     eapply eval_Econs with (v1:=Vlong (Int64.repr 64));[apply eval_Esizeof|reflexivity|constructor].
   + exact Funct.
   + reflexivity.
   + apply eval_funcall_external;exact Ext.
 - split.
   + intros pos Range;eapply Mem.perm_storebytes_1;[exact Store|apply Free;exact Range].
   + split.
     * intros b pos kind perm P;eapply Mem.perm_storebytes_1;[exact Store|exact P].
     * split.
       -- apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|intros;congruence].
       -- eapply storebytes_preserved;exact Store.
Qed.
Theorem exec_xonly_tweak_start (Model:memset_model) e le m bout bin bb:
 e!_memset=None ->le!_output_pubkey=Some (Vptr bout Ptrofs.zero) ->
 le!_internal_pubkey=Some (Vptr bin Ptrofs.zero) ->le!_tweak32=Some (Vptr bb Ptrofs.zero) ->
 Mem.range_perm m bout 0 64 Cur Freeable ->
 Mem.weak_valid_pointer m bin 0=true ->Mem.weak_valid_pointer m bb 0=true ->exists mz,
 Clight2.exec_stmt secp_ge e le m (statement_sequence xonly_tweak_start_statements Sskip) E0 le mz Out_normal /\
 Mem.range_perm mz bout 0 64 Cur Freeable /\keeps_permissions m mz /\
 lframe (fun b _=>b<>bout) m mz /\readonly_preserved m mz.
Proof.
 intros Symbol Output Input Bytes Free VI VB.
 assert (VO:Mem.weak_valid_pointer m bout (Ptrofs.unsigned Ptrofs.zero)=true).
 { apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm.
   eapply Mem.perm_implies;[apply Free;change (0<=0<64);lia|apply perm_any_N]. }
 destruct (exec_xonly_tweak_clear Model e le m bout Symbol Output Free)
 as (mz & Clear & FreeZ & Keep & Frame & Read).
 exists mz;split.
 - cbn [statement_sequence xonly_tweak_start_statements].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le).
   + exact (exec_nonnull_return_zero secp_ge e le m _ _ _ _ Output VO).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz) (le1:=le);[exact Clear|].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz) (le1:=le).
     * apply exec_nonnull_return_zero with (b:=bin) (ofs:=Ptrofs.zero);[exact Input|].
       apply xonly_keeps_weak_pointer with (m:=m);[exact Keep|exact VI].
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz) (le1:=le);[|constructor].
       apply exec_nonnull_return_zero with (b:=bb) (ofs:=Ptrofs.zero);[exact Bytes|].
       apply xonly_keeps_weak_pointer with (m:=m);[exact Keep|exact VB].
 - split;[exact FreeZ|];split;[exact Keep|];split;assumption.
Qed.
