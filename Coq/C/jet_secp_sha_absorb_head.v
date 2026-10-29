(** Shared actual setup of sha256_uchars before its loop. Both partial and
    block-filling calls use these same counter, overflow and cursor updates. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_sha_linkage C.jet_secp_linkage
  C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec
  C.jet_secp_sha_context C.jet_secp_sha_startup C.jet_secp_statement_prefix
  C.jet_clight_internal_preserve.
Require C.jets_sha C.jets_secp.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge sha_ge.

Definition secp_sha_absorb_head := statement_sequence [uc_pre1;uc_pre2;uc_ovf;uc_count] Sskip.
Lemma secp_sha_absorb_body : fn_body jets_secp.f_sha256_uchars=
  statement_sequence [uc_pre1;uc_pre2;uc_ovf;uc_count] (Ssequence uc_loop uc_tail).
Proof. reflexivity. Qed.

Theorem exec_secp_sha_absorb_head_counter used count total m bc ba oa :
  (used<64)%nat -> 0<=total -> total+Z.of_nat count<2305843009213693952 ->
  total mod 64=Z.of_nat used -> secp_sha_startup m ->
  Mem.range_perm m bc 0 88 Cur Freeable ->
  Mem.load Mint64 m bc 8=Some (Vlong (Int64.repr total)) ->
  Mem.load Mint8unsigned m bc 80=Some (Vint Int.zero) ->exists lef mf,
  Clight2.exec_stmt secp_ge empty_env (uc_le0 bc 0 ba oa (Int64.repr (Z.of_nat count))) m
    secp_sha_absorb_head E0 lef mf Out_normal /\
  lef!jets_sha._ctx=Some (Vptr bc Ptrofs.zero) /\lef!jets_sha._arr=Some (Vptr ba oa) /\
  lef!jets_sha._len=Some (Vlong (Int64.repr (Z.of_nat count))) /\
  lef!jets_sha._delta=Some (Vlong (Int64.repr (64-Z.of_nat used))) /\
  lef!jets_sha._block=Some (Vptr bc (Ptrofs.repr (16+Z.of_nat used))) /\
  Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr (total+Z.of_nat count))) /\
  Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
  Mem.range_perm mf bc 0 88 Cur Freeable /\
  (forall ch b ofs,(b<>bc \/ofs+size_chunk ch<=8 \/81<=ofs) ->Mem.load ch mf b ofs=Mem.load ch m b ofs) /\
  (forall ch ofs,16<=ofs ->ofs+size_chunk ch<=80 ->Mem.load ch mf bc ofs=Mem.load ch m bc ofs) /\
  (forall b ofs k p,Mem.perm m b ofs k p ->Mem.perm mf b ofs k p) /\
  lframe (fun b _=>b<>bc) m mf /\readonly_preserved m mf /\secp_sha_startup mf.
Proof.
  intros Used Nonnegative Total Remainder Startup Owned Counter Overflow.
  set (c:=Int64.repr total);set (vn:=Int64.repr (Z.of_nat count)).
  assert (CU:Int64.unsigned c=total) by
    (unfold c;apply Int64.unsigned_repr;change Int64.max_unsigned with 18446744073709551615;lia).
  assert (NU:Int64.unsigned vn=Z.of_nat count) by
    (unfold vn;apply Int64.unsigned_repr;change Int64.max_unsigned with 18446744073709551615;lia).
  assert (Mod:Int64.modu c c64=Int64.repr (Z.of_nat used)) by
    (rewrite modu64,CU,Remainder;reflexivity).
  assert (MU:Int64.unsigned (Int64.modu c c64)=Z.of_nat used).
  { rewrite Mod;apply Int64.unsigned_repr;change Int64.max_unsigned with 18446744073709551615;lia. }
  set (vd:=Int64.sub c64 (Int64.modu c c64)).
  assert (VD:vd=Int64.repr (64-Z.of_nat used)) by
    (unfold vd, Int64.sub;rewrite MU;reflexivity).
  set (oblk:=Ptrofs.add (Ptrofs.repr 0) (Ptrofs.repr 16)).
  set (ob:=Ptrofs.add oblk (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.modu c c64)))).
  assert (OB:ob=Ptrofs.repr (16+Z.of_nat used)).
  { rewrite <-(Ptrofs.repr_unsigned ob);unfold ob at 1;rewrite ptr_add_long by
      (rewrite MU;change (Ptrofs.unsigned oblk) with 16;change Ptrofs.max_unsigned with 18446744073709551615;lia).
    rewrite MU;reflexivity. }
  set (le0:=uc_le0 bc 0 ba oa vn).
  set (le1:=PTree.set jets_sha._delta (Vlong vd) (PTree.set jets_sha._t'9 (Vlong c) le0)).
  set (le2:=PTree.set jets_sha._block (Vptr bc ob) (PTree.set jets_sha._t'8 (Vlong c) le1)).
  assert (Access80:Mem.valid_access m Mint8unsigned bc 80 Writable).
  { split;[intros pos Range;eapply Mem.perm_implies;[apply Owned;change (80<=pos<81) in Range;lia|constructor]|
      exists 80;reflexivity]. }
  destruct (exec_secp_sha_available_overflow m le2 bc c vn ltac:(rewrite CU,NU;lia) eq_refl eq_refl
    Counter Overflow (proj2 (proj1 Startup)) Access80) as (le3 & m3 & Run3 & Store3 & Temps3).
  set (le4:=PTree.set jets_sha._t'4 (Vlong c) le3).
  assert (Access8:Mem.valid_access m3 Mint64 bc 8 Writable).
  { split.
    - intros pos Range;eapply Mem.perm_store_1;[exact Store3|];eapply Mem.perm_implies;
        [apply Owned;change (8<=pos<16) in Range;lia|constructor].
    - exists 1;reflexivity. }
  destruct (Mem.valid_access_store m3 Mint64 bc 8 (Vlong (Int64.add c vn)) Access8) as (mf & Store4).
  assert (Loads:forall ch b ofs,(b<>bc \/ofs+size_chunk ch<=8 \/81<=ofs) ->Mem.load ch mf b ofs=Mem.load ch m b ofs).
  { intros ch b ofs Outside;rewrite (Mem.load_store_other _ _ _ _ _ _ Store4)
      by (change (size_chunk Mint64) with 8;destruct Outside as [Other|[Before|After]];[left;exact Other|right;left;lia|right;right;lia]).
    apply (Mem.load_store_other _ _ _ _ _ _ Store3);change (size_chunk Mint8unsigned) with 1;
      destruct Outside as [Other|[Before|After]];[left;exact Other|right;left;lia|right;right;lia]. }
  assert (Perm:forall b ofs k p,Mem.perm m b ofs k p ->Mem.perm mf b ofs k p).
  { intros;eapply Mem.perm_store_1;[exact Store4|];eapply Mem.perm_store_1;[exact Store3|assumption]. }
  assert (Valid:forall b,Mem.valid_block m b ->Mem.valid_block mf b).
  { intros;eapply Mem.store_valid_block_1;[exact Store4|];eapply Mem.store_valid_block_1;[exact Store3|assumption]. }
  assert (Temps4:forall id,In id [jets_sha._ctx;jets_sha._arr;jets_sha._len;jets_sha._delta;jets_sha._block] ->le4!id=le2!id).
  { intros id Member;unfold le4;rewrite PTree.gso by
      (destruct Member as [<-|[<-|[<-|[<-|[<-|[]]]]]];discriminate);apply Temps3;exact Member. }
  assert (Frame:lframe (fun b _=>b<>bc) m mf).
  { split.
    - intros ch b ofs Old Outside;apply Loads;left;apply (Outside ofs);pose proof (size_chunk_pos ch);lia.
    - split;[intros;apply Perm;assumption|exact Valid]. }
  assert (Readonly:readonly_preserved m mf) by
    (eapply preserved_trans;[eapply store_preserved;exact Store3|eapply store_preserved;exact Store4]).
  exists le4,mf;split.
  - unfold secp_sha_absorb_head;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le1) (m1:=m).
    { unfold uc_pre1;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
      - apply exec_Sset;eapply (eval_secp_ctx_field SCounter) with (chunk:=Mint64) (base:=0);
          [lia|change (88<=18446744073709551615);lia|reflexivity|reflexivity|exact Counter].
      - apply exec_Sset;eapply eval_Ebinop with (v1:=Vint (Int.repr 64)) (v2:=Vlong (Int64.modu c c64));
          [constructor|eapply eval_Ebinop;[apply eval_Etempvar;apply PTree.gss|constructor|reflexivity]|reflexivity]. }
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le2) (m1:=m).
    { unfold uc_pre2;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
      - apply exec_Sset;eapply (eval_secp_ctx_field SCounter) with (chunk:=Mint64) (base:=0);
          [lia|change (88<=18446744073709551615);lia|reflexivity|reflexivity|exact Counter].
      - apply exec_Sset;eapply eval_Ebinop with (v1:=Vptr bc oblk) (v2:=Vlong (Int64.modu c c64));
          [apply eval_secp_ctx_block;reflexivity|eapply eval_Ebinop;[apply eval_Etempvar;apply PTree.gss|constructor|reflexivity]|reflexivity]. }
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le3) (m1:=m3);[exact Run3|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le4) (m1:=mf);[|constructor].
    unfold uc_count;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le4) (m1:=m3).
    + apply exec_Sset;eapply (eval_secp_ctx_field SCounter) with (chunk:=Mint64) (base:=0);
        [lia|change (88<=18446744073709551615);lia|reflexivity|rewrite Temps3 by (left;reflexivity);reflexivity|].
      rewrite (Mem.load_store_other _ _ _ _ _ _ Store3) by (right;left;cbn;lia);exact Counter.
    + eapply (exec_secp_ctx_assign SCounter) with (chunk:=Mint64) (base:=0) (v:=Vlong (Int64.add c vn));
        [lia|change (88<=18446744073709551615);lia|reflexivity|rewrite Temps4 by (left;reflexivity);reflexivity| |reflexivity|exact Store4].
      eapply eval_Ebinop;[apply eval_Etempvar;apply PTree.gss|
        apply eval_Etempvar;rewrite Temps4 by (do 2 right;left;reflexivity);reflexivity|reflexivity].
  - split;[rewrite Temps4 by (left;reflexivity);reflexivity|];
      split;[rewrite Temps4 by (right;left;reflexivity);reflexivity|];
      split;[rewrite Temps4 by (do 2 right;left;reflexivity);reflexivity|];
      split;[rewrite Temps4 by (do 3 right;left;reflexivity);unfold le2;rewrite !PTree.gso by discriminate;
        unfold le1;rewrite PTree.gss,VD;reflexivity|];
      split;[rewrite Temps4 by (do 4 right;left;reflexivity);unfold le2;rewrite PTree.gss,OB;reflexivity|];split.
    + rewrite (Mem.load_store_same _ _ _ _ _ _ Store4);unfold Int64.add;rewrite CU,NU;reflexivity.
    + split.
      * rewrite (Mem.load_store_other _ _ _ _ _ _ Store4) by (right;right;change (size_chunk Mint64) with 8;lia).
        rewrite (Mem.load_store_same _ _ _ _ _ _ Store3);reflexivity.
      * split;[intros pos Range;apply Perm,Owned;exact Range|];split;[exact Loads|];split.
        -- intros ch ofs Lo Hi;rewrite (Mem.load_store_other _ _ _ _ _ _ Store4) by (right;right;change (size_chunk Mint64) with 8;lia).
           apply (Mem.load_store_other _ _ _ _ _ _ Store3);right;left;exact Hi.
        -- split;[exact Perm|];split;[exact Frame|];split;[exact Readonly|].
           eapply secp_sha_startup_preserved;[exact Startup|exact Readonly|exact Frame|].
           intros pos;destruct (secp_sha_startup_separate m bc 88 Startup ltac:(lia) Owned) as [Other _];congruence.
Qed.

Theorem exec_secp_sha_absorb_head used count m bc ba oa :
  (used<64)%nat ->(used+count<=64)%nat ->secp_sha_startup m ->
  Mem.range_perm m bc 0 88 Cur Freeable ->
  Mem.load Mint64 m bc 8=Some (Vlong (Int64.repr (Z.of_nat used))) ->
  Mem.load Mint8unsigned m bc 80=Some (Vint Int.zero) ->exists lef mf,
  Clight2.exec_stmt secp_ge empty_env (uc_le0 bc 0 ba oa (Int64.repr (Z.of_nat count))) m
    secp_sha_absorb_head E0 lef mf Out_normal /\
  lef!jets_sha._ctx=Some (Vptr bc Ptrofs.zero) /\lef!jets_sha._arr=Some (Vptr ba oa) /\
  lef!jets_sha._len=Some (Vlong (Int64.repr (Z.of_nat count))) /\
  lef!jets_sha._delta=Some (Vlong (Int64.repr (64-Z.of_nat used))) /\
  lef!jets_sha._block=Some (Vptr bc (Ptrofs.repr (16+Z.of_nat used))) /\
  Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr (Z.of_nat (used+count)))) /\
  Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
  Mem.range_perm mf bc 0 88 Cur Freeable /\
  (forall ch b ofs,(b<>bc \/ofs+size_chunk ch<=8 \/81<=ofs) ->Mem.load ch mf b ofs=Mem.load ch m b ofs) /\
  (forall ch ofs,16<=ofs ->ofs+size_chunk ch<=80 ->Mem.load ch mf bc ofs=Mem.load ch m bc ofs) /\
  (forall b ofs k p,Mem.perm m b ofs k p ->Mem.perm mf b ofs k p) /\
  lframe (fun b _=>b<>bc) m mf /\readonly_preserved m mf /\secp_sha_startup mf.
Proof.
 intros Used Total Startup Owned Counter Overflow.
 replace (Z.of_nat (used+count)) with (Z.of_nat used+Z.of_nat count) by lia.
 eapply exec_secp_sha_absorb_head_counter;try eassumption.
 - lia.
 - lia.
 - apply Z.mod_small;lia.
Qed.
