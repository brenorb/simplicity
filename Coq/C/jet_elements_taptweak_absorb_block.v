(** The original byte-absorption loop when the remaining bytes exactly fill
    the current block: actual memcpy, pointer/count updates, dispatched SHA
    compression, reset and terminating loop test. No compression oracle. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Memory Values Events.
Require sha.SHA256.
Require Import C.jet_memcpy_model C.jet_sx_mem C.jet_uint32_array_init
  C.jet_sha_linkage C.jet_sha_ctx8_model C.jet_sha_uchars_prep C.jet_sha_uchars_loop
  C.jet_secp_linkage C.jet_secp_sha_context C.jet_secp_sha_startup
  C.jet_secp_sha_absorb_short C.jet_clight_internal_preserve.
Require C.jets_sha C.jets_secp.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Require Import C.jet_elements_taptweak_pure.
Require Import C.jet_elements_taptweak_globals C.jet_elements_taptweak_context
 C.jet_elements_taptweak_dispatch C.jet_elements_taptweak_absorb_short.
Local Opaque elements_taptweak_ge.
Lemma elements_taptweak_sha_uchar_symbol : Genv.find_symbol elements_taptweak_ge jets_sha._sha256_compression_uchar=
  Some (elements_taptweak_symbol_block jets_secp._sha256_compression_uchar).
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_sha_uchar_funct : Genv.find_funct elements_taptweak_ge
  (Vptr (elements_taptweak_symbol_block jets_secp._sha256_compression_uchar) Ptrofs.zero)=
  Some (Internal jets_secp.f_sha256_compression_uchar).
Proof. vm_compute;reflexivity. Qed.
Local Opaque elements_taptweak_ge sha_ge.

Theorem exec_elements_taptweak_sha_fill_block (Hmodel:memcpy_model) l bytes regs le m bc bs ba oa :
  (length l<64)%nat ->(length l+length bytes=64)%nat ->length regs=8%nat ->
  bc<>ba ->bc<>bs ->elements_taptweak_sha_startup m ->
  Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->
  Ptrofs.unsigned oa+Z.of_nat (length bytes)<=Ptrofs.max_unsigned ->
  le!jets_sha._ctx=Some (Vptr bc Ptrofs.zero) ->le!jets_sha._arr=Some (Vptr ba oa) ->
  le!jets_sha._block=Some (Vptr bc (Ptrofs.repr (16+Z.of_nat (length l)))) ->
  le!jets_sha._delta=Some (Vlong (Int64.repr (Z.of_nat (length bytes)))) ->
  le!jets_sha._len=Some (Vlong (Int64.repr (Z.of_nat (length bytes)))) ->
  Mem.load Mptr m bc 0=Some (Vptr bs Ptrofs.zero) ->uint32_array_at m bs 0 regs ->
  (forall i,(i<length l)%nat ->Mem.load Mint8unsigned m bc (16+Z.of_nat i)=Some (Vint (nth i l Int.zero))) ->
  (forall i,(i<length bytes)%nat ->Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i bytes Int.zero))) ->exists lef mf,
  Clight2.exec_stmt elements_taptweak_ge empty_env le m uc_loop E0 lef mf Out_normal /\
  lef!jets_sha._ctx=le!jets_sha._ctx /\lef!jets_sha._len=Some (Vlong Int64.zero) /\
  lef!jets_sha._delta=Some (Vlong (Int64.repr 64)) /\
  lef!jets_sha._block=Some (Vptr bc (Ptrofs.repr 16)) /\
  uint32_array_at mf bs 0 (SHA256.hash_block regs (be_words (l++bytes))) /\
  Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\
  (forall ch ofs,(ofs+size_chunk ch<=16 \/80<=ofs) ->Mem.load ch mf bc ofs=Mem.load ch m bc ofs) /\
  lframe (fun b _=>b<>bc /\b<>bs) m mf /\readonly_preserved m mf /\elements_taptweak_sha_startup mf.
Proof.
  intros LL Full LR CA CS Startup FC FS SourceHi Ctx Arr Block Delta Len Pointer State Buffer Source.
  set (vn:=Int64.repr (Z.of_nat (length bytes))).
  set (ob:=Ptrofs.repr (16+Z.of_nat (length l))).
  assert (BU:Ptrofs.unsigned ob=16+Z.of_nat (length l)) by
    (unfold ob;apply Ptrofs.unsigned_repr;change Ptrofs.max_unsigned with 18446744073709551615;lia).
  destruct (exec_elements_taptweak_sha_memcpy_n Hmodel jets_sha._delta bc ba ob oa bytes le m CA ltac:(lia)
    SourceHi ltac:(rewrite BU;change Ptrofs.max_unsigned with 18446744073709551615;lia)
    Block Arr Delta Source ltac:(intros pos Range;eapply Mem.perm_implies;
      [apply FC;rewrite BU in Range;lia|constructor]))
    as (mi & Copy & New & Loads & Perm & Valid & Readonly).
  assert (Frame:lframe (fun b _=>b<>bc) m mi).
  { split.
    - intros ch b ofs Old Outside;apply Loads;left;apply (Outside ofs);pose proof (size_chunk_pos ch);lia.
    - split;[intros;apply Perm;assumption|exact Valid]. }
  assert (StartupI:elements_taptweak_sha_startup mi).
  { eapply elements_taptweak_sha_startup_preserved;[exact Startup|exact Readonly|exact Frame|].
    intros pos;destruct (elements_taptweak_sha_startup_separate m bc 88 Startup ltac:(lia) FC) as [Other _];congruence. }
  assert (StateI:uint32_array_at mi bs 0 regs).
  { intros i v Nth;rewrite Loads by (left;congruence);apply State;exact Nth. }
  assert (PointerI:Mem.load Mptr mi bc 0=Some (Vptr bs Ptrofs.zero)).
  { rewrite Loads by (right;left;rewrite BU;change (size_chunk Mptr) with 8;lia);exact Pointer. }
  assert (FullBytes:forall i,(i<64)%nat ->Mem.load Mint8unsigned mi bc (16+Z.of_nat i)=
    Some (Vint (nth i (l++bytes) Int.zero))).
  { intros i Index;destruct (lt_dec i (length l)) as [Before|After].
    - rewrite app_nth1 by exact Before;rewrite Loads by (right;left;rewrite BU;change (size_chunk Mint8unsigned) with 1;lia).
      apply Buffer;exact Before.
    - rewrite app_nth2 by lia;replace (16+Z.of_nat i) with (Ptrofs.unsigned ob+Z.of_nat (i-length l)) by (rewrite BU;lia).
      apply New;lia. }
  destruct (eval_elements_taptweak_sha_compression_uchar_owned_at regs (l++bytes) mi bs bc (Ptrofs.repr 16)
    LR ltac:(rewrite app_length;exact Full) StartupI StateI ltac:(intros pos Range;apply Perm,FS;exact Range)
    ltac:(change (80<=18446744073709551615);lia) FullBytes)
    as (mf & Compress & Output & OwnedState & CompFrame & CompReadonly & StartupF).
  set (oa':=Ptrofs.add oa (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 vn))).
  set (le1:=PTree.set jets_sha._arr (Vptr ba oa') le).
  set (le2:=PTree.set jets_sha._len (Vlong (Int64.sub vn vn)) le1).
  set (le3:=PTree.set jets_sha._t'3 (Vptr bs Ptrofs.zero) le2).
  set (le4:=PTree.set jets_sha._block (Vptr bc (Ptrofs.repr 16)) le3).
  set (lef:=PTree.set jets_sha._delta (Vlong (Int64.repr 64)) le4).
  assert (Sub:Int64.sub vn vn=Int64.zero) by (unfold Int64.sub;rewrite Z.sub_diag;reflexivity).
  assert (Ctx3:le3!jets_sha._ctx=Some (Vptr bc Ptrofs.zero)).
  { unfold le3,le2,le1;rewrite !PTree.gso by discriminate;exact Ctx. }
  assert (Body:Clight2.exec_stmt elements_taptweak_ge empty_env le m uc_loop_body E0 lef mf Out_normal).
  { unfold uc_loop_body;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Copy|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le1) (m1:=mi).
    { apply exec_Sset;eapply eval_Ebinop;[apply eval_Etempvar;exact Arr|apply eval_Etempvar;exact Delta|reflexivity]. }
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le2) (m1:=mi).
    { apply exec_Sset;eapply eval_Ebinop;
        [apply eval_Etempvar;unfold le1;rewrite PTree.gso by discriminate;exact Len|
         apply eval_Etempvar;unfold le1;rewrite PTree.gso by discriminate;exact Delta|reflexivity]. }
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le3) (m1:=mf).
    { eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le3) (m1:=mi).
      - apply exec_Sset;eapply (eval_elements_taptweak_ctx_field SOutput) with (chunk:=Mptr) (base:=0);
          [lia|change (88<=18446744073709551615);lia|reflexivity| |exact PointerI].
        unfold le2,le1;rewrite !PTree.gso by discriminate;exact Ctx.
      - change le3 with (set_opttemp None Vundef le3) at 2.
        eapply exec_Scall with (vf:=Vptr (elements_taptweak_symbol_block jets_secp._sha256_compression_uchar) Ptrofs.zero)
          (vargs:=[Vptr bs Ptrofs.zero;Vptr bc (Ptrofs.repr 16)])
          (f:=Internal jets_secp.f_sha256_compression_uchar) (vres:=Vundef).
        + reflexivity.
        + eapply eval_Elvalue;[apply eval_Evar_global;[reflexivity|exact elements_taptweak_sha_uchar_symbol]|].
          apply deref_loc_reference;reflexivity.
        + eapply eval_Econs;[apply eval_Etempvar;apply PTree.gss|reflexivity|].
          eapply eval_Econs with (v1:=Vptr bc (Ptrofs.repr 16));[|reflexivity|constructor].
          apply eval_elements_taptweak_ctx_block with (base:=0);exact Ctx3.
        + exact elements_taptweak_sha_uchar_funct.
        + reflexivity.
        + exact Compress. }
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le4) (m1:=mf).
    { apply exec_Sset;apply eval_elements_taptweak_ctx_block with (base:=0);exact Ctx3. }
    apply exec_Sset;eapply eval_Ecast;[constructor|reflexivity]. }
  assert (LenF:lef!jets_sha._len=Some (Vlong Int64.zero)).
  { unfold lef,le4,le3;rewrite !PTree.gso by discriminate;unfold le2;rewrite PTree.gss,Sub;reflexivity. }
  assert (VC:Mem.valid_block m bc) by (eapply Mem.perm_valid_block;apply (FC 0);lia).
  exists lef,mf;split.
  - unfold uc_loop,Swhile;eapply exec_Sloop_loop with (le1:=lef) (m1:=mf) (le2:=lef) (m2:=mf)
      (t1:=E0) (t2:=E0) (t3:=E0).
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[|exact Body].
      eapply exec_Sifthenelse with (b:=true).
      * unfold uc_cond;eapply eval_Ebinop with (v1:=Vlong vn) (v2:=Vlong vn) (v:=Val.of_bool (Int64.cmpu Cle vn vn));
          [apply eval_Etempvar;exact Delta|apply eval_Etempvar;exact Len|reflexivity].
      * rewrite cmpu_le_bool,Z.leb_refl;reflexivity.
      * constructor.
    + constructor.
    + constructor.
    + eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
      eapply exec_Sseq_2;[|discriminate];eapply exec_Sifthenelse with (b:=false).
      * unfold uc_cond;eapply eval_Ebinop with (v1:=Vlong (Int64.repr 64)) (v2:=Vlong Int64.zero)
          (v:=Val.of_bool false);
          [apply eval_Etempvar;apply PTree.gss|apply eval_Etempvar;exact LenF|reflexivity].
      * reflexivity.
      * constructor.
  - split.
    + unfold lef,le4,le3,le2,le1;rewrite !PTree.gso by discriminate;reflexivity.
    + split;[exact LenF|];split;[apply PTree.gss|];split.
      * unfold lef;rewrite PTree.gso by discriminate;apply PTree.gss.
      * split;[exact Output|];split.
        -- intros pos Range;apply (proj1 (proj2 CompFrame));[apply Valid;exact VC|congruence|apply Perm,FC;exact Range].
        -- split;[exact OwnedState|];split.
           ++ intros ch ofs Outside;rewrite (proj1 CompFrame) by (first [apply Valid;exact VC|intros;congruence]).
              apply Loads;rewrite BU;destruct Outside as [Before|After];[right;left;lia|right;right;lia].
           ++ split.
              ** eapply lframe_trans;[eapply lframe_implies;[exact Frame|]|eapply lframe_implies;[exact CompFrame|]];
                   intros b ofs [OtherC OtherS] Old;assumption.
              ** split;[eapply preserved_trans;eassumption|exact StartupF].
Qed.
