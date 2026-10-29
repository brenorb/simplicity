(** Original sha256_u64be call that completes a 56-byte buffer. The caller
    really allocates eight bytes, serializes the supplied word, absorbs it,
    returns the result and frees the array. Conditional on bounded memcpy. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Globalenvs Memory Values Events.
Require sha.SHA256.
Require Import C.jet_memcpy_model C.jet_sx_mem C.jet_uint32_array_init
  C.jet_sha_linkage C.jet_sha_ctx8_model C.jet_sha_be64_exec C.jet_sha_compress_call
  C.jet_secp_linkage C.jet_secp_sha_pure_transport C.jet_secp_sha_startup
  C.jet_secp_sha_absorb_full C.jet_clight_internal_preserve.
Require C.jets_sha C.jets_secp.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma secp_sha_u64_WriteBE64_symbol : Genv.find_symbol secp_ge jets_sha._WriteBE64=
  Some (secp_symbol_block jets_sha._WriteBE64).
Proof. vm_compute;reflexivity. Qed.
Lemma secp_sha_u64_WriteBE64_funct : Genv.find_funct secp_ge
  (Vptr (secp_symbol_block jets_sha._WriteBE64) Ptrofs.zero)=Some (Internal jets_secp.f_WriteBE64).
Proof. vm_compute;reflexivity. Qed.
Lemma secp_sha_u64_uchars_symbol : Genv.find_symbol secp_ge jets_sha._sha256_uchars=
  Some (secp_symbol_block jets_sha._sha256_uchars).
Proof. vm_compute;reflexivity. Qed.
Lemma secp_sha_u64_uchars_funct : Genv.find_funct secp_ge
  (Vptr (secp_symbol_block jets_sha._sha256_uchars) Ptrofs.zero)=Some (Internal jets_secp.f_sha256_uchars).
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge sha_ge.

Lemma secp_sha_u64_entry m mi bb bc x : Mem.alloc m 0 8=(mi,bb) ->
  function_entry2 secp_ge jets_secp.f_sha256_u64be [Vptr bc Ptrofs.zero;Vlong x] m
    (u64_env bb) (u64_temps bc 0 x) mi.
Proof.
  intro Alloc;constructor.
  - cbn;repeat constructor;cbn;intuition discriminate.
  - cbn;repeat constructor;cbn;intuition discriminate.
  - intros a b HX HY Hxy;cbn in HX,HY.
    repeat match goal with H:_ \/ _ |- _=>destruct H end;subst;
      first [contradiction|vm_compute in Hxy;discriminate|congruence].
  - eapply alloc_variables_cons with (m1:=mi) (b1:=bb).
    + change (Mem.alloc m 0 8=(mi,bb));exact Alloc.
    + constructor.
  - reflexivity.
Qed.
Lemma secp_sha_u64_blocks bb : blocks_of_env secp_ge (u64_env bb)=[(bb,0,8)].
Proof. reflexivity. Qed.

Theorem eval_secp_sha_u64_full_counter (Hmodel:memcpy_model) l regs x total m bc bs :
  length l=56%nat ->length regs=8%nat ->
  0<=total -> total+8<2305843009213693952 -> total mod 64=56 ->bc<>bs ->secp_sha_startup m ->
  Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->
  Mem.load Mptr m bc 0=Some (Vptr bs Ptrofs.zero) ->uint32_array_at m bs 0 regs ->
  Mem.load Mint64 m bc 8=Some (Vlong (Int64.repr total)) ->
  Mem.load Mint8unsigned m bc 80=Some (Vint Int.zero) ->
  (forall i,(i<56)%nat ->Mem.load Mint8unsigned m bc (16+Z.of_nat i)=Some (Vint (nth i l Int.zero))) ->
  exists mf,Clight2.eval_funcall secp_ge m (Internal jets_secp.f_sha256_u64be)
    [Vptr bc Ptrofs.zero;Vlong x] E0 mf (Vint Int.one) /\
  uint32_array_at mf bs 0 (SHA256.hash_block regs (be_words (l++c_be64_bytes x))) /\
  Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
  Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr (total+8))) /\
  Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
  Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\
  lframe (fun b _=>b<>bc /\b<>bs) m mf /\readonly_preserved m mf /\secp_sha_startup mf.
Proof.
  intros LL LR Nonnegative Total Remainder CS Startup FC FS Pointer State Counter Overflow Buffer.
  assert (VC:Mem.valid_block m bc) by (eapply Mem.perm_valid_block;apply (FC 0);lia).
  assert (VS:Mem.valid_block m bs) by (eapply Mem.perm_valid_block;apply (FS 0);lia).
  destruct (Mem.alloc m 0 8) as (m1,bb) eqn:Alloc.
  pose proof (mext_alloc _ _ _ _ _ Alloc) as (VA & LA & PA & AA).
  assert (Fresh:forall b,Mem.valid_block m b ->b<>bb).
  { intros b Old Same;subst b;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Old). }
  assert (FB:Mem.range_perm m1 bb 0 8 Cur Freeable) by (intros pos Range;eapply Mem.perm_alloc_2;eauto).
  destruct (eval_sha_WriteBE64 m1 bb Ptrofs.zero x ltac:(change (8<=18446744073709551615);lia)
    ltac:(intros pos Range;eapply Mem.perm_implies;[apply FB;exact Range|constructor]))
    as (m2 & Write & Bytes & LoadsW & PermW & ValidW).
  pose proof (secp_sha_transport_call sha_ge jets_sha._WriteBE64 jets_sha.f_WriteBE64 m1
    [Vptr bb Ptrofs.zero;Vlong x] E0 m2 Vundef (or_intror eq_refl)
    ltac:(do 4 right;left;reflexivity) Write) as WriteCall.
  assert (R2:readonly_preserved m m2).
  { eapply preserved_trans;[eapply alloc_preserved;exact Alloc|].
    eapply secp_sha_pure_preserved;[do 4 right;left;reflexivity|exact WriteCall]. }
  assert (K2:forall ch b ofs,Mem.valid_block m b ->Mem.load ch m2 b ofs=Mem.load ch m b ofs).
  { intros ch b ofs Old;rewrite LoadsW by (left;apply Fresh;exact Old);apply LA;exact Old. }
  assert (V2:forall b,Mem.valid_block m b ->Mem.valid_block m2 b) by (intros;apply ValidW,VA;assumption).
  assert (Frame2:lframe (fun _ _=>True) m m2).
  { split;[intros;apply K2;assumption|];split;[intros;apply PermW,PA;assumption|exact V2]. }
  assert (Ready2:secp_sha_startup m2).
  { eapply secp_sha_startup_preserved;[exact Startup|exact R2|exact Frame2|intros;exact I]. }
  destruct (eval_secp_sha_absorb_full_counter Hmodel l (c_be64_bytes x) regs total m2 bc bs bb Ptrofs.zero
    ltac:(rewrite LL;lia) ltac:(rewrite LL;reflexivity) LR Nonnegative ltac:(exact Total)
    ltac:(rewrite LL;exact Remainder) (Fresh bc VC) CS Ready2
    ltac:(intros pos Range;apply PermW,PA,FC;exact Range)
    ltac:(intros pos Range;apply PermW,PA,FS;exact Range)
    ltac:(change (8<=18446744073709551615);lia)) as
    (m3 & Absorb & Output & Pointer3 & Counter3 & Overflow3 & FC3 & FS3 & Frame3 & R3 & Ready3).
  { rewrite K2 by exact VC;exact Pointer. }
  { intros i v Nth;rewrite K2 by exact VS;apply State;exact Nth. }
  { rewrite K2 by exact VC;exact Counter. }
  { rewrite K2 by exact VC;exact Overflow. }
  { intros i Index;rewrite K2 by exact VC;apply Buffer;rewrite LL in Index;exact Index. }
  { intros i Index;apply Bytes;exact Index. }
  assert (VB2:Mem.valid_block m2 bb) by (apply ValidW;eapply Mem.valid_new_block;exact Alloc).
  assert (FB3:Mem.range_perm m3 bb 0 8 Cur Freeable).
  { intros pos Range;apply (proj1 (proj2 Frame3));[exact VB2| |apply PermW,FB;exact Range].
    split;[exact (not_eq_sym (Fresh bc VC))|exact (not_eq_sym (Fresh bs VS))]. }
  destruct (Mem.range_perm_free m3 bb 0 8 FB3) as (mf & Free).
  assert (FreeFrame:lframe (fun b _=>b<>bb) m3 mf).
  { apply lframe_unchanged;eapply Mem.free_unchanged_on;[exact Free|intros pos Range Other;apply Other;reflexivity]. }
  assert (RF:readonly_preserved m3 mf) by (eapply free_preserved;exact Free).
  assert (FinalFrame:lframe (fun b _=>b<>bc /\b<>bs) m mf).
  { split.
    - intros ch b ofs Old Outside.
      rewrite (proj1 FreeFrame) by (first [exact (proj2 (proj2 Frame3) b (V2 b Old))|intros;apply Fresh;exact Old]).
      rewrite (proj1 Frame3) by (first [apply V2;exact Old|exact Outside]);apply K2;exact Old.
    - split.
      + intros b ofs k p Old Outside Perm;apply (proj1 (proj2 FreeFrame)).
        * exact (proj2 (proj2 Frame3) b (V2 b Old)).
        * apply Fresh;exact Old.
        * apply (proj1 (proj2 Frame3));[apply V2;exact Old|exact Outside|apply PermW,PA;exact Perm].
      + intros b Old;apply (proj2 (proj2 FreeFrame)),(proj2 (proj2 Frame3)),V2;exact Old. }
  exists mf;split.
  - eapply eval_funcall_internal with (e:=u64_env bb) (le1:=u64_temps bc 0 x) (m1:=m1)
      (le2:=PTree.set jets_sha._t'1 (Vint Int.one) (u64_temps bc 0 x)) (m2:=m3)
      (out:=Out_return (Some (Vint Int.one,tbool))).
    + apply secp_sha_u64_entry;exact Alloc.
    + cbn [jets_secp.f_sha256_u64be fn_body].
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=u64_temps bc 0 x) (m1:=m2).
      { change (u64_temps bc 0 x) with (set_opttemp None Vundef (u64_temps bc 0 x)) at 2.
        eapply exec_Scall with (vf:=Vptr (secp_symbol_block jets_sha._WriteBE64) Ptrofs.zero)
          (vargs:=[Vptr bb Ptrofs.zero;Vlong x]) (f:=Internal jets_secp.f_WriteBE64) (vres:=Vundef).
        - reflexivity.
        - eapply eval_Elvalue;[apply eval_Evar_global;[reflexivity|exact secp_sha_u64_WriteBE64_symbol]|].
          apply deref_loc_reference;reflexivity.
        - eapply eval_Econs.
          + eapply eval_Elvalue;[apply eval_Evar_local;reflexivity|apply deref_loc_reference;reflexivity].
          + reflexivity.
          + eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|constructor].
        - exact secp_sha_u64_WriteBE64_funct.
        - reflexivity.
        - exact WriteCall. }
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
      { change (PTree.set jets_sha._t'1 (Vint Int.one) (u64_temps bc 0 x)) with
          (set_opttemp (Some jets_sha._t'1) (Vint Int.one) (u64_temps bc 0 x)).
        eapply exec_Scall with (vf:=Vptr (secp_symbol_block jets_sha._sha256_uchars) Ptrofs.zero)
          (vargs:=[Vptr bc Ptrofs.zero;Vptr bb Ptrofs.zero;Vlong (Int64.repr 8)])
          (f:=Internal jets_secp.f_sha256_uchars) (vres:=Vint Int.one).
        - reflexivity.
        - eapply eval_Elvalue;[apply eval_Evar_global;[reflexivity|exact secp_sha_u64_uchars_symbol]|].
          apply deref_loc_reference;reflexivity.
        - eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|].
          eapply eval_Econs.
          + eapply eval_Elvalue;[apply eval_Evar_local;reflexivity|apply deref_loc_reference;reflexivity].
          + reflexivity.
          + eapply eval_Econs;[constructor|reflexivity|constructor].
        - exact secp_sha_u64_uchars_funct.
        - reflexivity.
        - exact Absorb. }
      apply exec_Sreturn_some;apply eval_Etempvar;apply PTree.gss.
    + cbn;split;[discriminate|reflexivity].
    + rewrite secp_sha_u64_blocks;cbn [Mem.free_list];rewrite Free;reflexivity.
  - split.
    + intros i v Nth;erewrite Mem.load_free;[apply Output;exact Nth|exact Free|left;apply Fresh;exact VS].
    + split.
      * erewrite Mem.load_free;[exact Pointer3|exact Free|left;apply Fresh;exact VC].
      * split.
        -- erewrite Mem.load_free;[exact Counter3|exact Free|left;apply Fresh;exact VC].
        -- split.
           ++ erewrite Mem.load_free;[exact Overflow3|exact Free|left;apply Fresh;exact VC].
           ++ split.
              ** intros pos Range;apply (proj1 (proj2 FreeFrame));[apply (proj2 (proj2 Frame3)),V2;exact VC|apply Fresh;exact VC|apply FC3;exact Range].
              ** split.
                 --- intros pos Range;apply (proj1 (proj2 FreeFrame));[apply (proj2 (proj2 Frame3)),V2;exact VS|apply Fresh;exact VS|apply FS3;exact Range].
                 --- split;[exact FinalFrame|];split.
                     +++ eapply preserved_trans;[exact R2|];eapply preserved_trans;[exact R3|exact RF].
                     +++ eapply secp_sha_startup_preserved;[exact Ready3|exact RF|exact FreeFrame|].
                         intros pos;pose proof (proj1 (proj1 Startup)) as Dispatch.
                         unfold C.jet_secp_sha_dispatch.secp_sha_dispatch_ok in Dispatch.
                         apply Mem.load_valid_access in Dispatch;apply Fresh.
                         eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Dispatch|constructor].
Qed.

Theorem eval_secp_sha_u64_full (Hmodel:memcpy_model) l regs x m bc bs :
  length l=56%nat ->length regs=8%nat ->bc<>bs ->secp_sha_startup m ->
  Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->
  Mem.load Mptr m bc 0=Some (Vptr bs Ptrofs.zero) ->uint32_array_at m bs 0 regs ->
  Mem.load Mint64 m bc 8=Some (Vlong (Int64.repr 56)) ->
  Mem.load Mint8unsigned m bc 80=Some (Vint Int.zero) ->
  (forall i,(i<56)%nat ->Mem.load Mint8unsigned m bc (16+Z.of_nat i)=Some (Vint (nth i l Int.zero))) ->
  exists mf,Clight2.eval_funcall secp_ge m (Internal jets_secp.f_sha256_u64be)
    [Vptr bc Ptrofs.zero;Vlong x] E0 mf (Vint Int.one) /\
  uint32_array_at mf bs 0 (SHA256.hash_block regs (be_words (l++c_be64_bytes x))) /\
  Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
  Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 64)) /\
  Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
  Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\
  lframe (fun b _=>b<>bc /\b<>bs) m mf /\readonly_preserved m mf /\secp_sha_startup mf.
Proof.
 intros LL LR CS Startup FC FS Pointer State Counter Overflow Buffer.
 eapply eval_secp_sha_u64_full_counter with (total:=56);try eassumption;try lia;reflexivity.
Qed.
