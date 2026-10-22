(** Actual Clight projective-struct copy, including all coordinates and flag.
    Read/write permissions and the by-copy execution are derived, not assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_exec C.jet_sx_mem C.jet_struct_copy_loads C.jet_secp_linkage C.jets_secp
 C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_multiply_normalize_bridge.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma gej_copy_field m mf bs bd bytes ofs w :
 0<=ofs -> ofs+40<=128 ->
 Mem.loadbytes m bs 0 128=Some bytes -> Mem.loadbytes mf bd 0 128=Some bytes ->
 Mem.range_perm mf bd 0 128 Cur Freeable ->
 fe_at m bs ofs (words5 w) -> fe_at mf bd ofs (words5 w).
Proof.
 intros Low Fit Load Dest Free (SB & SA & SM & SP & SL).
 split;[exact SB|];split;[exact SA|];split;[exact SM|];split.
 - intros pos Pos;eapply Mem.perm_implies;[apply Free;change (ofs<=pos<ofs+40) in Pos;lia|constructor].
 - intros i v HI.
   assert (Idx : (i<5)%nat).
   { change (i<length (words5 w))%nat;apply nth_error_Some;rewrite HI;discriminate. }
   assert (IZ : 0<=Z.of_nat i<5) by (pose proof (Nat2Z.is_nonneg i);lia).
   replace (ofs+8*Z.of_nat i) with (0+(ofs+8*Z.of_nat i)) by lia.
   eapply equal_loadbytes_field with (m1:=m) (b1:=bs) (base1:=0) (n:=128) (bytes:=bytes).
   + lia.
   + change (ofs+8*Z.of_nat i+8<=128);lia.
   + exact Load.
   + exact Dest.
   + change (8|0+(ofs+8*Z.of_nat i));destruct SA as [k HK];exists (k+Z.of_nat i);lia.
   + change (Mem.load Mint64 m bs (ofs+8*Z.of_nat i)=Some (Vlong v));exact (SL i v HI).
Qed.

Theorem exec_gej_copy_owned e le m src dst bs bd x y z flag :
 typeof src=Tstruct __6123 noattr -> typeof dst=Tstruct __6123 noattr ->
 eval_expr secp_ge e le m src (Vptr bs Ptrofs.zero) ->
 eval_lvalue secp_ge e le m dst bd Ptrofs.zero Full -> bs<>bd ->
 Mem.range_perm m bs 0 128 Cur Freeable -> Mem.range_perm m bd 0 128 Cur Freeable ->
 fe_at m bs 0 (words5 x) -> fe_at m bs 40 (words5 y) -> fe_at m bs 80 (words5 z) ->
 Mem.load Mint32 m bs 120=Some (Vint flag) -> exists mf,
 Clight2.exec_stmt secp_ge e le m (Sassign dst src) E0 le mf Out_normal /\
 fe_at mf bd 0 (words5 x) /\ fe_at mf bd 40 (words5 y) /\ fe_at mf bd 80 (words5 z) /\
 Mem.load Mint32 mf bd 120=Some (Vint flag) /\
 Mem.range_perm mf bs 0 128 Cur Freeable /\ Mem.range_perm mf bd 0 128 Cur Freeable /\
 lframe (fun b _=>b<>bd) m mf.
Proof.
 intros TS TD ES ED Sep FS FD X Y Z Flag.
 assert (Readable : Mem.range_perm m bs 0 (0+128) Cur Readable).
 { intros pos Pos;eapply Mem.perm_implies;[apply FS;lia|constructor]. }
 destruct (Mem.range_perm_loadbytes m bs 0 128 Readable) as (bytes & Load).
 pose proof (Mem.loadbytes_length _ _ _ _ _ Load) as Len.
 assert (WritePerm : Mem.range_perm m bd 0 (0+Z.of_nat (length bytes)) Cur Writable).
 { rewrite Len;apply freeable_range_writable;exact FD. }
 destruct (Mem.range_perm_storebytes m bd 0 bytes WritePerm) as (mf & Store).
 assert (Dest : Mem.loadbytes mf bd 0 128=Some bytes).
 { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ Store) as D;rewrite Len in D;exact D. }
 assert (FDF : Mem.range_perm mf bd 0 128 Cur Freeable).
 { intros pos Pos;eapply Mem.perm_storebytes_1;[exact Store|apply FD;exact Pos]. }
 assert (FSF : Mem.range_perm mf bs 0 128 Cur Freeable).
 { intros pos Pos;eapply Mem.perm_storebytes_1;[exact Store|apply FS;exact Pos]. }
 exists mf;split.
 - eapply exec_Sassign_copy with (b:=bd) (b':=bs) (ofs:=Ptrofs.zero) (ofs':=Ptrofs.zero)
    (v:=Vptr bs Ptrofs.zero).
   + exact ED.
   + exact ES.
   + rewrite TS,TD;reflexivity.
   + rewrite TD;eapply assign_loc_copy with (b':=bs) (ofs':=Ptrofs.zero) (bytes:=bytes).
     * reflexivity.
     * intros _;change (8|0);exists 0;reflexivity.
     * intros _;change (8|0);exists 0;reflexivity.
     * left;congruence.
     * exact Load.
     * exact Store.
 - split;[exact (gej_copy_field m mf bs bd bytes 0 x ltac:(lia) ltac:(lia) Load Dest FDF X)|].
   split;[exact (gej_copy_field m mf bs bd bytes 40 y ltac:(lia) ltac:(lia) Load Dest FDF Y)|].
   split;[exact (gej_copy_field m mf bs bd bytes 80 z ltac:(lia) ltac:(lia) Load Dest FDF Z)|].
   split.
   + change (Mem.load Mint32 mf bd (0+120)=Some (Vint flag)).
     eapply equal_loadbytes_field with (m1:=m) (b1:=bs) (base1:=0) (n:=128) (bytes:=bytes).
     * lia.
     * change (120+4<=128);lia.
     * exact Load.
     * exact Dest.
     * change (4|120);exists 30;reflexivity.
     * exact Flag.
   + split;[exact FSF|];split;[exact FDF|].
     apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|].
     intros pos Pos Outside;contradiction.
Qed.
