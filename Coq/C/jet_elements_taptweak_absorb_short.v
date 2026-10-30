(** Original partial-block absorption in the linked Elements artifact.
    The existing bounded memcpy model supplies actual destination-ge witnesses. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Memory Values Events.
Require Import C.jet_memcpy_model C.jet_sha_linkage C.jet_secp_linkage
  C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec C.jet_readBit_layout
  C.jet_secp_sha_context C.jet_secp_sha_startup C.jet_secp_sha_absorb_head C.jet_sx_mem
  C.jet_secp_statement_prefix C.jet_clight_internal_preserve.
Require C.jets_sha C.jets_secp.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Require Import C.jet_elements_taptweak_pure.
Require Import C.jet_elements_taptweak_globals C.jet_elements_taptweak_context C.jet_elements_taptweak_absorb_head.
Local Opaque elements_taptweak_ge.
Lemma elements_taptweak_sha_memcpy_symbol : Genv.find_symbol elements_taptweak_ge jets_sha._memcpy=
  Some (elements_taptweak_symbol_block jets_secp._memcpy).
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_sha_memcpy_funct : Genv.find_funct elements_taptweak_ge
  (Vptr (elements_taptweak_symbol_block jets_secp._memcpy) Ptrofs.zero)=
  Some (External (EF_external "memcpy" memcpy_sig)
    (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) (tptr tvoid) cc_default).
Proof. vm_compute;reflexivity. Qed.
Local Opaque sha_ge elements_taptweak_ge.

Lemma exec_elements_taptweak_sha_memcpy_n (Hmodel:memcpy_model) n bx ba ob oa xs le m :
  bx<>ba -> (0<length xs<=64)%nat ->
  Ptrofs.unsigned oa+Z.of_nat (length xs)<=Ptrofs.max_unsigned ->
  Ptrofs.unsigned ob+Z.of_nat (length xs)<=Ptrofs.max_unsigned ->
  le!jets_sha._block=Some (Vptr bx ob) -> le!jets_sha._arr=Some (Vptr ba oa) ->
  le!n=Some (Vlong (Int64.repr (Z.of_nat (length xs)))) ->
  (forall i,(i<length xs)%nat -> Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i xs Int.zero))) ->
  Mem.range_perm m bx (Ptrofs.unsigned ob) (Ptrofs.unsigned ob+Z.of_nat (length xs)) Cur Writable ->
  exists mf,Clight2.exec_stmt elements_taptweak_ge empty_env le m (uc_memcpy n) E0 le mf Out_normal /\
  (forall i,(i<length xs)%nat -> Mem.load Mint8unsigned mf bx (Ptrofs.unsigned ob+Z.of_nat i)=
    Some (Vint (nth i xs Int.zero))) /\
  (forall ch b ofs,(b<>bx \/ ofs+size_chunk ch<=Ptrofs.unsigned ob \/
    Ptrofs.unsigned ob+Z.of_nat (length xs)<=ofs) ->Mem.load ch mf b ofs=Mem.load ch m b ofs) /\
  (forall b ofs k p,Mem.perm m b ofs k p ->Mem.perm mf b ofs k p) /\
  (forall b,Mem.valid_block m b ->Mem.valid_block mf b) /\ readonly_preserved m mf.
Proof.
  intros Separate Length SourceHi DestHi Block Arr Len Source Dest.
  destruct (memcpy_bytes_effect_store Hmodel (genv_genv elements_taptweak_ge) m ba oa bx ob xs
    ltac:(lia) SourceHi DestHi Source Dest ltac:(congruence))
    as (mf & Call & Bytes & Loads & Perm & Valid & Raw & Store).
  exists mf;split.
  - change le with (set_opttemp None (Vptr bx ob) le) at 2;unfold uc_memcpy.
    eapply exec_Scall with (vf:=Vptr (elements_taptweak_symbol_block jets_secp._memcpy) Ptrofs.zero)
      (vargs:=[Vptr bx ob;Vptr ba oa;Vlong (Int64.repr (Z.of_nat (length xs)))])
      (f:=External (EF_external "memcpy" memcpy_sig)
        (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) (tptr tvoid) cc_default).
    + reflexivity.
    + eapply eval_Elvalue;[apply eval_Evar_global;[reflexivity|exact elements_taptweak_sha_memcpy_symbol]|].
      apply deref_loc_reference;reflexivity.
    + eapply eval_Econs;[apply eval_Etempvar;exact Block|reflexivity|].
      eapply eval_Econs;[apply eval_Etempvar;exact Arr|reflexivity|].
      eapply eval_Econs;[apply eval_Etempvar;exact Len|reflexivity|apply eval_Enil].
    + exact elements_taptweak_sha_memcpy_funct.
    + reflexivity.
    + apply eval_funcall_external;exact Call.
  - split;[exact Bytes|];split;[exact Loads|];split;[exact Perm|];split;[exact Valid|].
    eapply storebytes_preserved;exact Store.
Qed.

Lemma exec_elements_taptweak_sha_memcpy (Hmodel:memcpy_model) bx ba ob oa xs le m :
  bx<>ba -> (0<length xs<=64)%nat ->
  Ptrofs.unsigned oa+Z.of_nat (length xs)<=Ptrofs.max_unsigned ->
  Ptrofs.unsigned ob+Z.of_nat (length xs)<=Ptrofs.max_unsigned ->
  le!jets_sha._block=Some (Vptr bx ob) -> le!jets_sha._arr=Some (Vptr ba oa) ->
  le!jets_sha._len=Some (Vlong (Int64.repr (Z.of_nat (length xs)))) ->
  (forall i,(i<length xs)%nat -> Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i xs Int.zero))) ->
  Mem.range_perm m bx (Ptrofs.unsigned ob) (Ptrofs.unsigned ob+Z.of_nat (length xs)) Cur Writable ->
  exists mf,Clight2.exec_stmt elements_taptweak_ge empty_env le m (uc_memcpy jets_sha._len) E0 le mf Out_normal /\
  (forall i,(i<length xs)%nat -> Mem.load Mint8unsigned mf bx (Ptrofs.unsigned ob+Z.of_nat i)=
    Some (Vint (nth i xs Int.zero))) /\
  (forall ch b ofs,(b<>bx \/ ofs+size_chunk ch<=Ptrofs.unsigned ob \/
    Ptrofs.unsigned ob+Z.of_nat (length xs)<=ofs) ->Mem.load ch mf b ofs=Mem.load ch m b ofs) /\
  (forall b ofs k p,Mem.perm m b ofs k p ->Mem.perm mf b ofs k p) /\
  (forall b,Mem.valid_block m b ->Mem.valid_block mf b) /\ readonly_preserved m mf.
Proof. exact (exec_elements_taptweak_sha_memcpy_n Hmodel jets_sha._len bx ba ob oa xs le m). Qed.

Lemma elements_taptweak_sha_uchars_entry m bx ba oa vn :
  function_entry2 elements_taptweak_ge jets_secp.f_sha256_uchars [Vptr bx Ptrofs.zero;Vptr ba oa;Vlong vn] m
    empty_env (uc_le0 bx 0 ba oa vn) m.
Proof.
  constructor.
  - cbn;constructor.
  - cbn;repeat constructor;cbn;intuition discriminate.
  - intros x y HX HY Hxy;cbn in HX,HY.
    repeat match goal with H:_ \/ _ |- _=>destruct H end;subst;
      first [contradiction|vm_compute in Hxy;discriminate|congruence].
  - constructor.
  - reflexivity.
Qed.

Theorem eval_elements_taptweak_sha_absorb_short_counter (Hmodel:memcpy_model) l bytes total m bx ba oa out :
  (length l+length bytes<64)%nat -> 0<=total ->
  total+Z.of_nat (length bytes)<2305843009213693952 ->
  total mod 64=Z.of_nat (length l) -> bx<>ba -> elements_taptweak_sha_startup m ->
  Mem.range_perm m bx 0 88 Cur Freeable ->
  Ptrofs.unsigned oa+Z.of_nat (length bytes)<=Ptrofs.max_unsigned ->
  Mem.load Mptr m bx 0=Some out ->
  Mem.load Mint64 m bx 8=Some (Vlong (Int64.repr total)) ->
  Mem.load Mint8unsigned m bx 80=Some (Vint Int.zero) ->
  (forall i,(i<length l)%nat ->Mem.load Mint8unsigned m bx (16+Z.of_nat i)=Some (Vint (nth i l Int.zero))) ->
  (forall i,(i<length bytes)%nat ->Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i bytes Int.zero))) ->exists mf,
  Clight2.eval_funcall elements_taptweak_ge m (Internal jets_secp.f_sha256_uchars)
    [Vptr bx Ptrofs.zero;Vptr ba oa;Vlong (Int64.repr (Z.of_nat (length bytes)))] E0 mf (Vint Int.one) /\
  Mem.load Mptr mf bx 0=Some out /\
  Mem.load Mint64 mf bx 8=Some (Vlong (Int64.repr (total+Z.of_nat (length bytes)))) /\
  Mem.load Mint8unsigned mf bx 80=Some (Vint Int.zero) /\
  (forall i,(i<length (l++bytes))%nat ->Mem.load Mint8unsigned mf bx (16+Z.of_nat i)=
    Some (Vint (nth i (l++bytes) Int.zero))) /\
  Mem.range_perm mf bx 0 88 Cur Freeable /\ lframe (fun b _=>b<>bx) m mf /\
  readonly_preserved m mf /\ elements_taptweak_sha_startup mf.
Proof.
  intros Short Nonnegative Total Remainder Separate Startup Owned SourceHi Pointer Counter Overflow Buffer Source.
  set (vn:=Int64.repr (Z.of_nat (length bytes))).
  destruct (exec_elements_taptweak_sha_absorb_head_counter (length l) (length bytes) total m bx ba oa
    ltac:(lia) Nonnegative Total Remainder Startup Owned Counter Overflow) as
    (le4 & m4 & Head & HC & HA & HN & HD & HB & HeadCounter & HeadOverflow & OwnedI &
     L34 & HeadBuffer & P34 & HeadFrame & R34 & StartupI).
  set (vd:=Int64.repr (64-Z.of_nat (length l))).
  set (ob:=Ptrofs.repr (16+Z.of_nat (length l))).
  set (le2:=PTree.set jets_sha._block (Vptr bx ob)
    (PTree.set jets_sha._delta (Vlong vd) (uc_le0 bx 0 ba oa vn))).
  assert (DU:Int64.unsigned vd=64-Z.of_nat (length l)) by
    (unfold vd;apply Int64.unsigned_repr;change Int64.max_unsigned with 18446744073709551615;lia).
  assert (NU:Int64.unsigned vn=Z.of_nat (length bytes)) by
    (unfold vn;apply Int64.unsigned_repr;change Int64.max_unsigned with 18446744073709551615;lia).
  assert (BU:Ptrofs.unsigned ob=16+Z.of_nat (length l)) by
    (unfold ob;apply Ptrofs.unsigned_repr;change Ptrofs.max_unsigned with 18446744073709551615;lia).
  assert (V34:forall b,Mem.valid_block m b ->Mem.valid_block m4 b) by (exact (proj2 (proj2 HeadFrame))).
  assert (Temps4:forall id,In id [jets_sha._ctx;jets_sha._arr;jets_sha._len;jets_sha._delta;jets_sha._block] ->le4!id=le2!id).
  { intros id [<-|[<-|[<-|[<-|[<-|[]]]]]];[exact HC|exact HA|exact HN|exact HD|exact HB]. }
  assert (Tail:exists mf,
    Clight2.exec_stmt elements_taptweak_ge empty_env le4 m4
      (Sifthenelse (Etempvar jets_sha._len tulong) (uc_memcpy jets_sha._len) Sskip) E0 le4 mf Out_normal /\
    (forall i,(i<length bytes)%nat ->Mem.load Mint8unsigned mf bx (16+Z.of_nat (length l)+Z.of_nat i)=
      Some (Vint (nth i bytes Int.zero))) /\
    (forall ch b ofs,(b<>bx \/ ofs+size_chunk ch<=16+Z.of_nat (length l) \/ 80<=ofs) ->
      Mem.load ch mf b ofs=Mem.load ch m4 b ofs) /\
    (forall b ofs k p,Mem.perm m4 b ofs k p ->Mem.perm mf b ofs k p) /\
    (forall b,Mem.valid_block m4 b ->Mem.valid_block mf b) /\readonly_preserved m4 mf).
  { destruct bytes as [|byte rest] eqn:Bytes.
    - exists m4;split;[|split;[intros i Index;cbn in Index;lia|split;[reflexivity|split;[auto|split;[auto|apply preserved_refl]]]]].
      eapply exec_Sifthenelse with (b:=false);[apply eval_Etempvar;rewrite Temps4 by (do 2 right;left;reflexivity);reflexivity|reflexivity|constructor].
    - destruct (exec_elements_taptweak_sha_memcpy Hmodel bx ba ob oa (byte::rest) le4 m4 Separate ltac:(cbn [length] in *;lia)
        SourceHi ltac:(rewrite BU;change Ptrofs.max_unsigned with 18446744073709551615;lia)
        ltac:(rewrite Temps4 by (do 4 right;left;reflexivity);reflexivity)
        ltac:(rewrite Temps4 by (right;left;reflexivity);reflexivity)
        ltac:(rewrite Temps4 by (do 2 right;left;reflexivity);reflexivity))
        as (mf & Copy & BytesF & Loads & Perm & Valid & Preserved).
      { intros i Index;rewrite L34 by (left;congruence);apply Source;exact Index. }
      { intros pos Range;apply P34;eapply Mem.perm_implies;[apply Owned;rewrite BU in Range;lia|constructor]. }
      exists mf;split.
      + eapply exec_Sifthenelse with (b:=true);[apply eval_Etempvar;rewrite Temps4 by (do 2 right;left;reflexivity);reflexivity| |exact Copy].
        cbn;unfold bool_val;cbn.
        assert (NZ:Int64.eq vn Int64.zero=false).
        { apply Int64.eq_false;intro Zero;rewrite Zero in NU;change (Int64.unsigned Int64.zero) with 0 in NU;cbn in NU;lia. }
        rewrite NZ;reflexivity.
      + split;[intros i Index;rewrite <-BU;apply BytesF;exact Index|];split.
        * intros ch b ofs Outside;apply Loads;rewrite BU;destruct Outside as [Other|[Before|After]];
            [left;exact Other|right;left;exact Before|right;right;lia].
        * split;[exact Perm|];split;assumption. }
  destruct Tail as (mf & TailRun & NewBytes & TailFrame & TailPerm & TailValid & TailPreserved).
  assert (OverflowF:Mem.load Mint8unsigned mf bx 80=Some (Vint Int.zero)).
  { rewrite TailFrame by (right;right;lia).
    exact HeadOverflow. }
  set (lef:=PTree.set jets_sha._t'2 (Vint Int.zero) le4).
  assert (Frame:lframe (fun b _=>b<>bx) m mf).
  { split.
    - intros ch b ofs Old Outside;rewrite TailFrame by (left;apply (Outside ofs);pose proof (size_chunk_pos ch);lia).
      apply L34;left;apply (Outside ofs);pose proof (size_chunk_pos ch);lia.
    - split;[intros;apply TailPerm,P34;assumption|intros;apply TailValid,V34;assumption]. }
  assert (Preserved:readonly_preserved m mf) by (eapply preserved_trans;[exact R34|exact TailPreserved]).
  exists mf;split.
  - eapply eval_funcall_internal with (e:=empty_env) (le1:=uc_le0 bx 0 ba oa vn) (m1:=m) (le2:=lef) (m2:=mf)
      (out:=Out_return (Some (Vint Int.one,tint))).
    + apply elements_taptweak_sha_uchars_entry.
    + rewrite elements_taptweak_sha_absorb_body.
      eapply exec_statement_prefix_then_last;[exact Head|].
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le4) (m1:=m4).
      { unfold uc_loop,Swhile;eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
        eapply exec_Sseq_2;[|discriminate];eapply exec_Sifthenelse with (b:=false);[| |constructor].
        - unfold uc_cond;eapply eval_Ebinop with (v1:=Vlong vd) (v2:=Vlong vn)
            (v:=Val.of_bool (Int64.cmpu Cle vd vn));
            [apply eval_Etempvar;rewrite Temps4 by (do 3 right;left;reflexivity);reflexivity|
             apply eval_Etempvar;rewrite Temps4 by (do 2 right;left;reflexivity);reflexivity|reflexivity].
        - rewrite cmpu_le_bool,DU,NU;rewrite (proj2 (Z.leb_gt _ _)) by lia;reflexivity. }
      unfold uc_tail;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le4) (m1:=mf);[exact TailRun|].
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lef) (m1:=mf).
      { apply exec_Sset;eapply (eval_elements_taptweak_ctx_field SOverflow) with (chunk:=Mint8unsigned) (base:=0);
          [lia|change (88<=18446744073709551615);lia|reflexivity|rewrite Temps4 by (left;reflexivity);reflexivity|exact OverflowF]. }
      apply exec_Sreturn_some;eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|reflexivity].
    + cbn;split;[discriminate|reflexivity].
    + reflexivity.
  - split.
    + rewrite TailFrame by (right;left;change (size_chunk Mptr) with 8;lia);rewrite L34 by (right;left;reflexivity);exact Pointer.
    + split.
      * rewrite TailFrame by (right;left;change (size_chunk Mint64) with 8;lia).
        exact HeadCounter.
      * split;[exact OverflowF|];split.
        -- intros i Index;rewrite app_length in Index;destruct (lt_dec i (length l)) as [Before|After].
           ++ rewrite app_nth1 by exact Before.
              rewrite TailFrame by (right;left;change (size_chunk Mint8unsigned) with 1;lia).
              rewrite HeadBuffer by (change (size_chunk Mint8unsigned) with 1;lia);apply Buffer;exact Before.
           ++ rewrite app_nth2 by lia;replace (16+Z.of_nat i) with
                (16+Z.of_nat (length l)+Z.of_nat (i-length l)) by lia;apply NewBytes;lia.
        -- split;[intros pos Range;apply TailPerm,P34,Owned;exact Range|];split;[exact Frame|];split;[exact Preserved|].
           eapply elements_taptweak_sha_startup_preserved;[exact Startup|exact Preserved|exact Frame|].
           intros ofs;destruct (elements_taptweak_sha_startup_separate m bx 88 Startup ltac:(lia) Owned) as [Other _];congruence.
Qed.

Theorem eval_elements_taptweak_sha_absorb_short (Hmodel:memcpy_model) l bytes m bx ba oa out :
  (length l+length bytes<64)%nat -> bx<>ba -> elements_taptweak_sha_startup m ->
  Mem.range_perm m bx 0 88 Cur Freeable ->
  Ptrofs.unsigned oa+Z.of_nat (length bytes)<=Ptrofs.max_unsigned ->
  Mem.load Mptr m bx 0=Some out ->
  Mem.load Mint64 m bx 8=Some (Vlong (Int64.repr (Z.of_nat (length l)))) ->
  Mem.load Mint8unsigned m bx 80=Some (Vint Int.zero) ->
  (forall i,(i<length l)%nat ->Mem.load Mint8unsigned m bx (16+Z.of_nat i)=Some (Vint (nth i l Int.zero))) ->
  (forall i,(i<length bytes)%nat ->Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i bytes Int.zero))) ->exists mf,
  Clight2.eval_funcall elements_taptweak_ge m (Internal jets_secp.f_sha256_uchars)
    [Vptr bx Ptrofs.zero;Vptr ba oa;Vlong (Int64.repr (Z.of_nat (length bytes)))] E0 mf (Vint Int.one) /\
  Mem.load Mptr mf bx 0=Some out /\
  Mem.load Mint64 mf bx 8=Some (Vlong (Int64.repr (Z.of_nat (length (l++bytes))))) /\
  Mem.load Mint8unsigned mf bx 80=Some (Vint Int.zero) /\
  (forall i,(i<length (l++bytes))%nat ->Mem.load Mint8unsigned mf bx (16+Z.of_nat i)=
    Some (Vint (nth i (l++bytes) Int.zero))) /\
  Mem.range_perm mf bx 0 88 Cur Freeable /\ lframe (fun b _=>b<>bx) m mf /\
  readonly_preserved m mf /\ elements_taptweak_sha_startup mf.
Proof.
 intros Short Separate Startup Owned SourceHi Pointer Counter Overflow Buffer Source.
 replace (Int64.repr (Z.of_nat (length (l++bytes)))) with
   (Int64.repr (Z.of_nat (length l)+Z.of_nat (length bytes))) by
   (f_equal;rewrite app_length;lia).
 eapply eval_elements_taptweak_sha_absorb_short_counter;try eassumption.
 - lia.
 - lia.
 - apply Z.mod_small;lia.
Qed.
