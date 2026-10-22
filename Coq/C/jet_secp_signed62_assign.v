(** Actual 40-byte Clight struct copy for field and signed62 objects.
    This uses by-copy semantics, not external libc or a replacement function. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_exec C.jet_sx_exec C.jet_sx_mem C.jet_struct_copy_loads
 C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_local_regions
 C.jet_secp_multiply_normalize_bridge C.jet_secp_field_read_preservation.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma copy40_cast_self ty m b : access_mode ty=By_copy ->
 Cop.sem_cast (Vptr b Ptrofs.zero) ty ty m=Some (Vptr b Ptrofs.zero).
Proof.
 intro Mode;destruct ty;cbn in Mode;try discriminate.
 all: try (destruct i;destruct s;discriminate Mode).
 all: try (destruct f;discriminate Mode).
 all: cbn [Cop.sem_cast Cop.classify_cast].
 all: match goal with |- context[if ?D then _ else _] =>
   destruct D;[reflexivity|congruence] end.
Qed.

Lemma fe_copy40_field m mf bs bd bytes w :
 Mem.loadbytes m bs 0 40=Some bytes -> Mem.loadbytes mf bd 0 40=Some bytes ->
 Mem.range_perm mf bd 0 40 Cur Freeable ->
 (forall i v,nth_error (words5 w) i=Some v ->
   Mem.load Mint64 m bs (8*Z.of_nat i)=Some (Vlong v)) ->
 fe_at mf bd 0 (words5 w).
Proof.
 intros Load Dest Free SL.
 split;[lia|];split;[exists 0;reflexivity|];split;
   [change (40<=18446744073709551615);lia|];split.
 - intros pos HP;eapply Mem.perm_implies;[apply Free;exact HP|constructor].
 - intros i v HI.
   assert (Idx : (i<5)%nat).
   { change (i<length (words5 w))%nat;apply nth_error_Some;rewrite HI;discriminate. }
   assert (IZ : 0<=Z.of_nat i<5) by (pose proof (Nat2Z.is_nonneg i);lia).
   eapply equal_loadbytes_field with (m1:=m) (b1:=bs) (base1:=0) (n:=40) (bytes:=bytes).
   + lia.
   + change (8*Z.of_nat i+8<=40);lia.
   + exact Load.
   + exact Dest.
   + change (8|0+8*Z.of_nat i);exists (Z.of_nat i);lia.
   + exact (SL i v HI).
Qed.

Theorem exec_fe_copy40_readable e le m src dst ty bs bd w :
 typeof src=ty -> typeof dst=ty -> access_mode ty=By_copy ->
 sizeof (genv_cenv secp_ge) ty=40 -> alignof_blockcopy (genv_cenv secp_ge) ty=8 ->
 eval_expr secp_ge e le m src (Vptr bs Ptrofs.zero) ->
 eval_lvalue secp_ge e le m dst bd Ptrofs.zero Full -> bs<>bd ->
 Mem.range_perm m bs 0 40 Cur Readable -> Mem.range_perm m bd 0 40 Cur Freeable ->
 (forall i v,nth_error (words5 w) i=Some v ->
   Mem.load Mint64 m bs (8*Z.of_nat i)=Some (Vlong v)) -> exists mf,
 Clight2.exec_stmt secp_ge e le m (Sassign dst src) E0 le mf Out_normal /\
 fe_at mf bd 0 (words5 w) /\
 Mem.range_perm mf bd 0 40 Cur Freeable /\
 lframe (fun b _=>b<>bd) m mf.
Proof.
 intros TS TD Mode Size Align ES ED Sep FS FD Input.
 assert (Readable : Mem.range_perm m bs 0 (0+40) Cur Readable).
 { exact FS. }
 destruct (Mem.range_perm_loadbytes m bs 0 40 Readable) as (bytes & Load).
 pose proof (Mem.loadbytes_length _ _ _ _ _ Load) as Len.
 assert (Write : Mem.range_perm m bd 0 (0+Z.of_nat (length bytes)) Cur Writable).
 { rewrite Len;apply freeable_range_writable;exact FD. }
 destruct (Mem.range_perm_storebytes m bd 0 bytes Write) as (mf & Store).
 assert (Dest : Mem.loadbytes mf bd 0 40=Some bytes).
 { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ Store) as D;rewrite Len in D;exact D. }
 assert (FDF : Mem.range_perm mf bd 0 40 Cur Freeable).
 { intros pos HP;eapply Mem.perm_storebytes_1;[exact Store|apply FD;exact HP]. }
 assert (Frame : lframe (fun b _=>b<>bd) m mf).
 { apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|].
   intros pos HP Outside;contradiction. }
 exists mf;split.
 - eapply exec_Sassign_copy with (b:=bd) (b':=bs) (ofs:=Ptrofs.zero) (ofs':=Ptrofs.zero)
    (v:=Vptr bs Ptrofs.zero).
   + exact ED.
   + exact ES.
   + rewrite TS,TD;apply copy40_cast_self;exact Mode.
   + rewrite TD;eapply assign_loc_copy with (b':=bs) (ofs':=Ptrofs.zero) (bytes:=bytes).
     * exact Mode.
     * rewrite Align;intros _;change (8|0);exists 0;reflexivity.
     * rewrite Align;intros _;change (8|0);exists 0;reflexivity.
     * left;congruence.
     * rewrite Size;exact Load.
     * exact Store.
 - split;[exact (fe_copy40_field m mf bs bd bytes w Load Dest FDF Input)|];split;assumption.
Qed.

Theorem exec_fe_copy40_owned e le m src dst ty bs bd w :
 typeof src=ty -> typeof dst=ty -> access_mode ty=By_copy ->
 sizeof (genv_cenv secp_ge) ty=40 -> alignof_blockcopy (genv_cenv secp_ge) ty=8 ->
 eval_expr secp_ge e le m src (Vptr bs Ptrofs.zero) ->
 eval_lvalue secp_ge e le m dst bd Ptrofs.zero Full -> bs<>bd ->
 Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bd 0 40 Cur Freeable ->
 fe_at m bs 0 (words5 w) -> exists mf,
 Clight2.exec_stmt secp_ge e le m (Sassign dst src) E0 le mf Out_normal /\
 fe_at mf bd 0 (words5 w) /\ fe_at mf bs 0 (words5 w) /\
 Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bd 0 40 Cur Freeable /\
 lframe (fun b _=>b<>bd) m mf.
Proof.
 intros TS TD Mode Size Align ES ED Sep FS FD Input.
 pose proof Input as (_ & _ & _ & _ & Loads).
 destruct (exec_fe_copy40_readable e le m src dst ty bs bd w TS TD Mode Size Align ES ED Sep
   ltac:(intros pos HP;eapply Mem.perm_implies;[apply FS;exact HP|constructor]) FD Loads)
   as (mf & Body & Out & Free & Frame).
 exists mf;split;[exact Body|];split;[exact Out|];split.
 - eapply field_at_lframe;[exact Input|exact Frame|];intros;exact Sep.
 - split.
   + eapply field_freeable_lframe;[exact Input|exact FS|exact Frame|];intros;exact Sep.
   + split;assumption.
Qed.

Definition signed62_assign_temps bd bs := PTree.set _src (Vptr bs Ptrofs.zero)
 (PTree.set _dst (Vptr bd Ptrofs.zero)
  (create_undef_temps (fn_temps f_secp256k1_modinv64_signed62_assign))).

Lemma signed62_assign_entry m bd bs :
 function_entry2 secp_ge f_secp256k1_modinv64_signed62_assign
  [Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero] m empty_env (signed62_assign_temps bd bs) m.
Proof.
 assert (Ok : fn_okb f_secp256k1_modinv64_signed62_assign=true) by reflexivity.
 destruct (fn_okb_true _ Ok) as (HN1 & HN2 & HD).
 constructor;[exact HN1|exact HN2|exact HD|constructor|reflexivity].
Qed.

Theorem eval_signed62_assign_readable w m bout bin : bout<>bin ->
 Mem.range_perm m bout 0 40 Cur Freeable ->
 Mem.range_perm m bin 0 40 Cur Readable ->
 (forall i v,nth_error (words5 w) i=Some v ->
   Mem.load Mint64 m bin (8*Z.of_nat i)=Some (Vlong v)) -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_signed62_assign)
  [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
 fe_at mf bout 0 (words5 w) /\ Mem.range_perm mf bout 0 40 Cur Freeable /\
 lframe (fun b _=>b<>bout) m mf.
Proof.
 intros NE FO FI Loads.
 set (ty:=Tstruct _secp256k1_modinv64_signed62 noattr).
 set (le:=signed62_assign_temps bout bin).
 assert (HD : le!_dst=Some (Vptr bout Ptrofs.zero)).
 { unfold le,signed62_assign_temps;rewrite PTree.gso by discriminate;apply PTree.gss. }
 assert (HS : le!_src=Some (Vptr bin Ptrofs.zero)) by (apply PTree.gss).
 destruct (exec_fe_copy40_readable empty_env le m
   (Ederef (Etempvar _src (tptr ty)) ty) (Ederef (Etempvar _dst (tptr ty)) ty)
   ty bin bout w eq_refl eq_refl eq_refl eq_refl eq_refl
   ltac:(eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact HS|apply deref_loc_copy;reflexivity])
   ltac:(apply eval_Ederef;apply eval_Etempvar;exact HD)
   ltac:(congruence) FI FO Loads) as (mf & Body & Out & OFree & Frame).
 exists mf;split.
 - eapply eval_funcall_internal with (e:=empty_env) (le1:=le) (le2:=le)
    (m1:=m) (m2:=mf) (out:=Out_normal).
   + apply signed62_assign_entry.
   + exact Body.
   + reflexivity.
   + reflexivity.
 - split;[exact Out|];split;assumption.
Qed.

Theorem eval_signed62_assign_from_storage w m bout bin : bout<>bin ->
 Mem.range_perm m bout 0 40 Cur Freeable -> fe_at m bin 0 (words5 w) ->
 Mem.range_perm m bin 0 40 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_signed62_assign)
  [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
 fe_at mf bout 0 (words5 w) /\ fe_at mf bin 0 (words5 w) /\
 Mem.range_perm mf bout 0 40 Cur Freeable /\ Mem.range_perm mf bin 0 40 Cur Freeable /\
 lframe (fun b _=>b<>bout) m mf.
Proof.
 intros NE FO FI FS;pose proof FI as (_ & _ & _ & _ & Loads).
 destruct (eval_signed62_assign_readable w m bout bin NE FO
   ltac:(intros pos HP;eapply Mem.perm_implies;[apply FS;exact HP|constructor]) Loads)
   as (mf & Call & Out & Free & Frame).
 exists mf;split;[exact Call|];split;[exact Out|];split.
 - eapply field_at_lframe;[exact FI|exact Frame|];intros;congruence.
 - split;[exact Free|];split.
   + eapply field_freeable_lframe;[exact FI|exact FS|exact Frame|];intros;congruence.
   + exact Frame.
Qed.
