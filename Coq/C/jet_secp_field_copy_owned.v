(** Reusable actual Clight field-struct copy from an owned slice into a distinct
    owned slice.  Destination contents may be uninitialized; no libc is used. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_exec C.jet_sx_mem C.jet_struct_copy_loads C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_multiply_normalize_bridge.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem exec_field_copy_owned e le m src dst bs sbase bd dbase w :
  typeof src=Tstruct __5467 noattr -> typeof dst=Tstruct __5467 noattr ->
  eval_expr secp_ge e le m src (Vptr bs (Ptrofs.repr sbase)) ->
  eval_lvalue secp_ge e le m dst bd (Ptrofs.repr dbase) Full ->
  bs<>bd -> fe_at m bs sbase (words5 w) ->
  0<=dbase -> (8|dbase) -> dbase+40<=Ptrofs.max_unsigned ->
  Mem.range_perm m bd dbase (dbase+40) Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (Sassign dst src) E0 le mf Out_normal /\
  fe_at mf bd dbase (words5 w) /\
  (forall b pos k p, Mem.perm mf b pos k p <-> Mem.perm m b pos k p) /\
  lframe (fun b pos => b<>bd \/ pos<dbase \/ dbase+40<=pos) m mf.
Proof.
  intros TS TD ES ED HSep HField HB HA HM HF.
  pose proof HField as (SB & SA & SM & SP & SL).
  change (sbase+40<=Ptrofs.max_unsigned) in SM.
  change (Mem.range_perm m bs sbase (sbase+40) Cur Writable) in SP.
  assert (HSU : Ptrofs.unsigned (Ptrofs.repr sbase)=sbase) by (apply Ptrofs.unsigned_repr;lia).
  assert (HDU : Ptrofs.unsigned (Ptrofs.repr dbase)=dbase) by (apply Ptrofs.unsigned_repr;lia).
  assert (HReadable : Mem.range_perm m bs sbase (sbase+40) Cur Readable).
  { intros pos HP;eapply Mem.perm_implies;[apply SP;exact HP|constructor]. }
  destruct (Mem.range_perm_loadbytes m bs sbase 40 HReadable) as (bytes & HL).
  pose proof (Mem.loadbytes_length _ _ _ _ _ HL) as HLen.
  assert (HW : Mem.range_perm m bd dbase (dbase+Z.of_nat (length bytes)) Cur Writable).
  { rewrite HLen;apply freeable_range_writable;exact HF. }
  destruct (Mem.range_perm_storebytes m bd dbase bytes HW) as (mf & HS).
  assert (HDest : Mem.loadbytes mf bd dbase 40=Some bytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ HS) as HD;rewrite HLen in HD;exact HD. }
  exists mf;split.
  - eapply exec_Sassign_copy with (b:=bd) (b':=bs) (ofs:=Ptrofs.repr dbase)
      (ofs':=Ptrofs.repr sbase) (v:=Vptr bs (Ptrofs.repr sbase)).
    + exact ED.
    + exact ES.
    + rewrite TS,TD;reflexivity.
    + rewrite TD;eapply assign_loc_copy with (b':=bs) (ofs':=Ptrofs.repr sbase) (bytes:=bytes).
      * reflexivity.
      * intros _;change (8|Ptrofs.unsigned (Ptrofs.repr sbase));rewrite HSU;exact SA.
      * intros _;change (8|Ptrofs.unsigned (Ptrofs.repr dbase));rewrite HDU;exact HA.
      * left;congruence.
      * change (Mem.loadbytes m bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 40=Some bytes).
        rewrite HSU;exact HL.
      * rewrite HDU;exact HS.
  - split.
    + split;[exact HB|];split;[exact HA|];split;[exact HM|];split.
      * intros pos HP;eapply Mem.perm_storebytes_1;[exact HS|].
        eapply Mem.perm_implies;[apply HF;exact HP|constructor].
      * intros i v HI.
        assert (HIdx : (i<5)%nat).
        { change (i<length (words5 w))%nat;apply nth_error_Some;rewrite HI;discriminate. }
        assert (HZ : 0<=Z.of_nat i<5) by (pose proof (Nat2Z.is_nonneg i);lia).
        eapply equal_loadbytes_field with (m1:=m) (b1:=bs) (base1:=sbase) (n:=40) (bytes:=bytes).
        -- lia.
        -- change (8*Z.of_nat i+8<=40);lia.
        -- exact HL.
        -- exact HDest.
        -- change (8|dbase+8*Z.of_nat i);destruct HA as [k HK];exists (k+Z.of_nat i);lia.
        -- exact (SL i v HI).
    + split.
      * intros b pos k p;split;intro HP;
          [eapply Mem.perm_storebytes_2|eapply Mem.perm_storebytes_1];eassumption.
      * apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact HS|].
        intros pos HP HO;rewrite HLen in HP;destruct HO as [HN|[HN|HN]];[contradiction|lia|lia].
Qed.
