(** The original challenge caller's constructor-return-slot assignment. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_exec C.jet_sx_mem C.jet_struct_copy_loads C.jet_secp_linkage
 C.jet_secp_schnorr_challenge_entry C.jet_clight_internal_preserve.
Require Import C.jets_secp.
Import ListNotations Ctypes Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition schnorr_challenge_copy := Sassign
 (Evar _sha schnorr_challenge_context_type) (Evar __res schnorr_challenge_context_type).
Local Opaque secp_ge.
Theorem exec_schnorr_challenge_copy e le m bc br out count overflow :
 e!_sha=Some (bc,schnorr_challenge_context_type) ->
 e!__res=Some (br,schnorr_challenge_context_type) ->bc<>br ->
 Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m br 0 88 Cur Freeable ->
 Mem.load Mptr m br 0=Some out ->Mem.load Mint64 m br 8=Some (Vlong count) ->
 Mem.load Mint8unsigned m br 80=Some (Vint overflow) ->exists mf,
 Clight2.exec_stmt secp_ge e le m schnorr_challenge_copy E0 le mf Out_normal /\
 Mem.load Mptr mf bc 0=Some out /\Mem.load Mint64 mf bc 8=Some (Vlong count) /\
 Mem.load Mint8unsigned mf bc 80=Some (Vint overflow) /\
 Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe (fun b _=>b<>bc) m mf /\readonly_preserved m mf.
Proof.
 intros Context Result Separate FC FR Pointer Counter Overflow.
 assert (Read:Mem.range_perm m br 0 88 Cur Readable).
 { intros pos Range;eapply Mem.perm_implies;[apply FR;exact Range|constructor]. }
 destruct (Mem.range_perm_loadbytes m br 0 88 Read) as (bytes & Load).
 pose proof (Mem.loadbytes_length _ _ _ _ _ Load) as Length.
 assert (Write:Mem.range_perm m bc 0 (0+Z.of_nat (length bytes)) Cur Writable).
 { rewrite Length;intros pos Range;eapply Mem.perm_implies;[apply FC;exact Range|constructor]. }
 destruct (Mem.range_perm_storebytes m bc 0 bytes Write) as (mf & Store).
 assert (Bytes:Mem.loadbytes mf bc 0 88=Some bytes).
 { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ Store) as H;rewrite Length in H;exact H. }
 exists mf;split.
 - unfold schnorr_challenge_copy;eapply exec_Sassign_copy with (b:=bc) (b':=br)
    (ofs:=Ptrofs.zero) (ofs':=Ptrofs.zero) (v:=Vptr br Ptrofs.zero).
   + apply eval_Evar_local;exact Context.
   + eapply eval_Elvalue;[apply eval_Evar_local;exact Result|apply deref_loc_copy;reflexivity].
   + reflexivity.
   + eapply assign_loc_copy with (b':=br) (ofs':=Ptrofs.zero) (bytes:=bytes).
     * reflexivity.
     * intros _;exists 0;reflexivity.
     * intros _;exists 0;reflexivity.
     * left;congruence.
     * exact Load.
     * exact Store.
 - split.
   + eapply equal_loadbytes_field with (m1:=m) (b1:=br) (base1:=0) (base2:=0)
      (n:=88) (delta:=0) (bytes:=bytes);[lia|change (8<=88);lia|exact Load|exact Bytes|
       exists 0;reflexivity|exact Pointer].
   + split.
     * eapply equal_loadbytes_field with (m1:=m) (b1:=br) (base1:=0) (base2:=0)
        (n:=88) (delta:=8) (bytes:=bytes);[lia|change (16<=88);lia|exact Load|exact Bytes|
         exists 1;reflexivity|exact Counter].
     * split.
       -- eapply equal_loadbytes_field with (m1:=m) (b1:=br) (base1:=0) (base2:=0)
          (n:=88) (delta:=80) (bytes:=bytes);[lia|change (81<=88);lia|exact Load|exact Bytes|
           exists 80;reflexivity|exact Overflow].
       -- split;[intros pos Range;eapply Mem.perm_storebytes_1;[exact Store|apply FC;exact Range]|];split;
          [intros pos Range;eapply Mem.perm_storebytes_1;[exact Store|apply FR;exact Range]|];split.
          ++ apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|intros;congruence].
          ++ eapply storebytes_preserved;exact Store.
Qed.
