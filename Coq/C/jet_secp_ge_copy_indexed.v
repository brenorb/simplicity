(** The original affine struct assignment from an indexed table entry.
    The entire 88-byte copy, including padding, follows Clight's by-copy
    rule; only the represented coordinate and flag loads are interpreted. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_exec C.jet_sx_mem C.jet_struct_copy_loads C.jet_secp_linkage C.jets_secp
 C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_multiply_normalize_bridge
 C.jet_clight_internal_preserve.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma ge_copy_indexed_field m mf bs base bd bytes ofs w :
 0<=ofs -> ofs+40<=88 -> (8|ofs) ->
 Mem.loadbytes m bs base 88=Some bytes -> Mem.loadbytes mf bd 0 88=Some bytes ->
 Mem.range_perm mf bd 0 88 Cur Freeable ->
 fe_at m bs (base+ofs) (words5 w) -> fe_at mf bd ofs (words5 w).
Proof.
 intros Low Fit Align Load Dest Free (SB & SA & SM & SP & SL).
 split;[exact Low|];split;[exact Align|];split.
 - change Ptrofs.max_unsigned with 18446744073709551615;lia.
 - split.
   + intros pos Pos;eapply Mem.perm_implies;[apply Free;change (ofs<=pos<ofs+40) in Pos;lia|constructor].
   + intros i v HI.
     assert (Idx:(i<5)%nat).
     { change (i<length (words5 w))%nat;apply nth_error_Some;rewrite HI;discriminate. }
     assert (IZ:0<=Z.of_nat i<5) by (pose proof (Nat2Z.is_nonneg i);lia).
     replace (ofs+8*Z.of_nat i) with (0+(ofs+8*Z.of_nat i)) by lia.
     eapply equal_loadbytes_field with (m1:=m) (b1:=bs) (base1:=base) (n:=88) (bytes:=bytes).
     * lia.
     * change (ofs+8*Z.of_nat i+8<=88);lia.
     * exact Load.
     * exact Dest.
     * change (8|0+(ofs+8*Z.of_nat i));destruct Align as [k HK];exists (k+Z.of_nat i);lia.
     * replace (base+(ofs+8*Z.of_nat i)) with ((base+ofs)+8*Z.of_nat i) by lia.
       exact (SL i v HI).
Qed.

Theorem exec_ge_copy_owned_indexed e le m src dst bs base bd x y flag :
 typeof src=Tstruct __6121 noattr -> typeof dst=Tstruct __6121 noattr ->
 eval_expr secp_ge e le m src (Vptr bs (Ptrofs.repr base)) ->
 eval_lvalue secp_ge e le m dst bd Ptrofs.zero Full -> bs<>bd ->
 0<=base -> base+88<=Ptrofs.max_unsigned -> (8|base) ->
 Mem.range_perm m bs base (base+88) Cur Freeable -> Mem.range_perm m bd 0 88 Cur Freeable ->
 fe_at m bs base (words5 x) -> fe_at m bs (base+40) (words5 y) ->
 Mem.load Mint32 m bs (base+80)=Some (Vint flag) -> exists mf,
 Clight2.exec_stmt secp_ge e le m (Sassign dst src) E0 le mf Out_normal /\
 fe_at mf bd 0 (words5 x) /\ fe_at mf bd 40 (words5 y) /\
 Mem.load Mint32 mf bd 80=Some (Vint flag) /\
 Mem.range_perm mf bd 0 88 Cur Freeable /\
 (forall b pos k p,Mem.perm mf b pos k p <-> Mem.perm m b pos k p) /\
 lframe (fun b _=>b<>bd) m mf /\ readonly_preserved m mf.
Proof.
 intros TS TD ES ED Sep Base Max Align FS FD X Y Flag.
 assert (Offset:Ptrofs.unsigned (Ptrofs.repr base)=base) by (apply Ptrofs.unsigned_repr;lia).
 assert (Readable:Mem.range_perm m bs base (base+88) Cur Readable).
 { intros pos Pos;eapply Mem.perm_implies;[apply FS;exact Pos|constructor]. }
 destruct (Mem.range_perm_loadbytes m bs base 88 Readable) as (bytes & Load).
 pose proof (Mem.loadbytes_length _ _ _ _ _ Load) as Len.
 assert (WritePerm:Mem.range_perm m bd 0 (0+Z.of_nat (length bytes)) Cur Writable).
 { rewrite Len;apply freeable_range_writable;exact FD. }
 destruct (Mem.range_perm_storebytes m bd 0 bytes WritePerm) as (mf & Store).
 assert (Dest:Mem.loadbytes mf bd 0 88=Some bytes).
 { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ Store) as D;rewrite Len in D;exact D. }
 assert (FDF:Mem.range_perm mf bd 0 88 Cur Freeable).
 { intros pos Pos;eapply Mem.perm_storebytes_1;[exact Store|apply FD;exact Pos]. }
 exists mf;split.
 - eapply exec_Sassign_copy with (b:=bd) (b':=bs) (ofs:=Ptrofs.zero) (ofs':=Ptrofs.repr base)
    (v:=Vptr bs (Ptrofs.repr base)).
   + exact ED.
   + exact ES.
   + rewrite TS,TD;reflexivity.
   + rewrite TD;eapply assign_loc_copy with (b':=bs) (ofs':=Ptrofs.repr base) (bytes:=bytes).
     * reflexivity.
     * intros _;change (8|Ptrofs.unsigned (Ptrofs.repr base));rewrite Offset;exact Align.
     * intros _;change (8|0);exists 0;reflexivity.
     * left;congruence.
     * change (Mem.loadbytes m bs (Ptrofs.unsigned (Ptrofs.repr base)) 88=Some bytes);rewrite Offset;exact Load.
     * exact Store.
 - split.
   + apply (ge_copy_indexed_field m mf bs base bd bytes 0 x ltac:(lia) ltac:(lia) (Z.divide_0_r 8) Load Dest FDF).
     rewrite Z.add_0_r;exact X.
   + split;[exact (ge_copy_indexed_field m mf bs base bd bytes 40 y ltac:(lia) ltac:(lia)
      ltac:(exists 5;reflexivity) Load Dest FDF Y)|];split.
     * change (Mem.load Mint32 mf bd (0+80)=Some (Vint flag)).
       eapply equal_loadbytes_field with (m1:=m) (b1:=bs) (base1:=base) (n:=88) (bytes:=bytes).
       -- lia.
       -- change (80+4<=88);lia.
       -- exact Load.
       -- exact Dest.
       -- change (4|80);exists 20;reflexivity.
       -- exact Flag.
     * split;[exact FDF|];split.
       -- intros b pos k p;split;intro P;[eapply Mem.perm_storebytes_2|eapply Mem.perm_storebytes_1];eassumption.
       -- split.
          ++ apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|].
             intros pos Pos Outside;contradiction.
          ++ eapply storebytes_preserved;exact Store.
Qed.
