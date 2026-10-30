(** Actual SHA byte-compression and indirect dispatch in the linked Elements artifact. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Memory Values Events.
Require sha.SHA256.
Require Import C.jet_transport C.jet_sha_linkage C.jet_secp_linkage
  C.jet_sha_compress_call C.jet_sha_compress_uchar C.jet_sha_be32_exec
  C.jet_sha_ctx8_model C.jet_sha_block_local
  C.jet_secp_sha_pure_transport C.jet_secp_sha_compression
  C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Require C.jets_sha C.jets_secp.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Require Import C.jet_elements_taptweak_pure C.jet_secp_sha_dispatch C.jet_uint32_array_init C.jet_sx_mem.
Require Import C.jet_elements_taptweak_globals C.jet_elements_taptweak_compression.
Definition elements_taptweak_sha_dispatch_ok m :=
  Mem.load Mptr m (elements_taptweak_symbol_block jets_secp._simplicity_sha256_compression) 0=
    Some (Vptr (elements_taptweak_symbol_block jets_secp._sha256_compression_portable) Ptrofs.zero).

Lemma elements_taptweak_sha_dispatch_symbol :
  Genv.find_symbol elements_taptweak_ge jets_secp._simplicity_sha256_compression=
    Some (elements_taptweak_symbol_block jets_secp._simplicity_sha256_compression).
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_sha_compression_funct :
  Genv.find_funct elements_taptweak_ge (Vptr (elements_taptweak_symbol_block jets_secp._sha256_compression_portable) Ptrofs.zero)=
    Some (Internal jets_secp.f_sha256_compression_portable).
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_sha_fill_checked : stmt_okb secp_ge elements_taptweak_ge (map fst secp_sha_pure_helpers)
  [jets_sha.___compound] (be_fill 15)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_sha_fill_closed : closed_stmtb secp_sha_pure_helpers (be_fill 15)=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque sha_ge elements_taptweak_ge.

Lemma elements_taptweak_sha_pure_table_ok:internal_table_ok elements_taptweak_ge secp_sha_pure_helpers.
Proof.
 intros id f Lookup;pose proof (internal_lookup_in _ _ _ Lookup) as Member.
 destruct (elements_taptweak_sha_pure_entries id f Member) as (b1 & b2 & S1 & F1 & S2 & F2).
 pose proof secp_sha_helpers_closed_checked as Checked;rewrite forallb_forall in Checked.
 specialize (Checked (id,f) Member);apply Bool.andb_true_iff in Checked;destruct Checked as [Body Vars].
 split;[exists b2;split;assumption|split;assumption].
Qed.
Lemma elements_taptweak_sha_fill_transport bk le m trace lef mf out:
 Clight2.exec_stmt sha_ge (cu_env bk) le m (be_fill 15) trace lef mf out ->
 Clight2.exec_stmt elements_taptweak_ge (cu_env bk) le m (be_fill 15) trace lef mf out.
Proof.
 intro Run;pose proof (secp_sha_fill_transport bk le m trace lef mf out Run) as SecpRun.
 exact (proj1 (transport_main secp_ge elements_taptweak_ge (map fst secp_sha_pure_helpers)
 (transportable_of_entries secp_ge elements_taptweak_ge secp_sha_pure_helpers
 elements_taptweak_sha_pure_entries elements_taptweak_sha_pure_ok))
 (cu_env bk) le m (be_fill 15) trace lef mf out SecpRun
 [(jets_sha.___compound,tarray tuint 16)] (secp_sha_cu_dom bk) elements_taptweak_sha_fill_checked).
Qed.
Lemma elements_taptweak_sha_cu_entry m m1 bk bs os bc oc : Mem.alloc m 0 64=(m1,bk) ->
  function_entry2 elements_taptweak_ge jets_secp.f_sha256_compression_uchar [Vptr bs os;Vptr bc oc] m
    (cu_env bk) (cu_temps bs os bc oc) m1.
Proof.
  intro Alloc;constructor.
  - cbn;repeat constructor;cbn;intuition discriminate.
  - cbn;repeat constructor;cbn;intuition discriminate.
  - intros x y HX HY Hxy;cbn in HX,HY.
    repeat match goal with H:_ \/ _ |- _=>destruct H end;subst;
      first [contradiction|vm_compute in Hxy;discriminate|congruence].
  - eapply alloc_variables_cons with (m1:=m1) (b1:=bk).
    + change (Mem.alloc m 0 64=(m1,bk));exact Alloc.
    + constructor.
  - reflexivity.
Qed.
Lemma elements_taptweak_sha_cu_blocks bk : blocks_of_env elements_taptweak_ge (cu_env bk)=[(bk,0,64)].
Proof. reflexivity. Qed.

Theorem eval_elements_taptweak_sha_compression_uchar m bs os bc oc (regs bytes:list int) :
  length regs=8%nat -> length bytes=64%nat ->
  Ptrofs.unsigned os+32<=Ptrofs.max_unsigned -> Ptrofs.unsigned oc+64<=Ptrofs.max_unsigned ->
  elements_taptweak_sha_dispatch_ok m ->
  (forall i,(i<8)%nat ->
    Mem.load Mint32 m bs (Ptrofs.unsigned os+4*Z.of_nat i)=Some (Vint (nth i regs Int.zero)) /\
    Mem.valid_access m Mint32 bs (Ptrofs.unsigned os+4*Z.of_nat i) Writable) ->
  (forall i,(i<64)%nat ->
    Mem.load Mint8unsigned m bc (Ptrofs.unsigned oc+Z.of_nat i)=Some (Vint (nth i bytes Int.zero))) ->
  exists mf,
  Clight2.eval_funcall elements_taptweak_ge m (Internal jets_secp.f_sha256_compression_uchar)
    [Vptr bs os;Vptr bc oc] E0 mf Vundef /\
  (forall i,(i<8)%nat -> Mem.load Mint32 mf bs (Ptrofs.unsigned os+4*Z.of_nat i)=
    Some (Vint (nth i (SHA256.hash_block regs (be_words bytes)) Int.zero))) /\
  (forall ch b ofs,Mem.valid_block m b ->
    (b<>bs \/ ofs+size_chunk ch<=Ptrofs.unsigned os \/ Ptrofs.unsigned os+32<=ofs) ->
    Mem.load ch mf b ofs=Mem.load ch m b ofs) /\
  (forall b ofs k p,Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm mf b ofs k p) /\
  (forall b,Mem.valid_block m b -> Mem.valid_block mf b) /\ readonly_preserved m mf.
Proof.
  intros LR LB SO CO Dispatch State Bytes.
  destruct (Mem.alloc m 0 64) as [m1 bk] eqn:Alloc.
  pose proof (mext_alloc _ _ _ _ _ Alloc) as (XV & XL & XP & XA).
  assert (Fresh:forall b,Mem.valid_block m b -> b<>bk).
  { intros b Old Same;subst b;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Old). }
  assert (VS:Mem.valid_block m bs).
  { destruct (State 0%nat ltac:(lia)) as [Load _];apply Mem.load_valid_access in Load.
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Load|constructor]. }
  assert (VC:Mem.valid_block m bc).
  { pose proof (Bytes 0%nat ltac:(lia)) as Load;apply Mem.load_valid_access in Load.
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Load|constructor]. }
  assert (VG:Mem.valid_block m (elements_taptweak_symbol_block jets_secp._simplicity_sha256_compression)).
  { unfold elements_taptweak_sha_dispatch_ok in Dispatch;apply Mem.load_valid_access in Dispatch.
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Dispatch|constructor]. }
  assert (Fill:fill_ok bc bk oc bytes m1).
  { split.
    - intros i Index;rewrite XL by exact VC;apply Bytes;exact Index.
    - intros j Index;eapply Mem.valid_access_implies with (p1:=Freeable);[|constructor].
      eapply Mem.valid_access_alloc_same;[exact Alloc|lia|change (size_chunk Mint32) with 4;lia|].
      exists (Z.of_nat j);change (align_chunk Mint32) with 4;lia. }
  destruct (be_fill_exec bc bk oc bytes (cu_env bk) (Fresh bc VC) CO eq_refl eq_refl 15 ltac:(lia)
    (cu_temps bs os bc oc) m1 Fill eq_refl)
    as (le2 & m2 & FillRun & Chunk & S & Fill2 & Words & Frame2 & Perm2 & Valid2).
  pose proof (elements_taptweak_sha_fill_transport _ _ _ _ _ _ _ FillRun) as Prefix.
  set (blk:=map (c_be_word bytes) (seq 0 16)).
  assert (BL:length blk=16%nat) by (unfold blk;rewrite map_length,seq_length;reflexivity).
  destruct (eval_sha_compression m2 bs os bk Ptrofs.zero regs blk LR BL SO
    ltac:(change (Ptrofs.unsigned Ptrofs.zero) with 0;change Ptrofs.max_unsigned with 18446744073709551615;lia)
    ltac:(left;apply Fresh;exact VS)) as (m3 & Compress & Output & Frame3 & Perm3 & Valid3).
  { intros i Index;destruct (State i Index) as [Load Access];split.
    - rewrite Frame2 by (apply Fresh;exact VS);rewrite XL by exact VS;exact Load.
    - destruct Access as [Perm Align];split;[|exact Align];intros pos Range;apply Perm2,XP,Perm;exact Range. }
  { intros i Index;change (Ptrofs.unsigned Ptrofs.zero) with 0;rewrite Z.add_0_l.
    rewrite (Words i ltac:(lia));unfold blk.
    rewrite (nth_indep _ Int.zero (c_be_word bytes 0)) by (rewrite map_length,seq_length;exact Index).
    rewrite map_nth,seq_nth by exact Index;reflexivity. }
  pose proof (elements_taptweak_sha_round_transport jets_sha._sha256_compression_portable
    jets_sha.f_sha256_compression_portable _ _ _ _ _ ltac:(do 7 right;left;reflexivity) Compress) as Call.
  assert (VK:Mem.valid_block m1 bk) by (eapply Mem.valid_new_block;exact Alloc).
  assert (PF:forall b lo hi,In (b,lo,hi) [(bk,0,64)] -> Mem.range_perm m3 b lo hi Cur Freeable).
  { intros b lo hi [Same|[]];injection Same as <- <- <-;intros pos Range.
    apply Perm3;[apply Valid2;exact VK|];apply Perm2;eapply Mem.perm_alloc_2;eauto. }
  destruct (free_list_blocks [(bk,0,64)] m3 PF ltac:(repeat constructor;cbn;tauto))
    as (mf & Free & FrameF & PermF & ValidF).
  cbn [map fst] in FrameF,PermF.
  assert (NotFresh:forall b,Mem.valid_block m b -> ~In b [bk]).
  { intros b Old [Same|[]];exact (Fresh b Old (eq_sym Same)). }
  exists mf;split.
  - set (le3:=PTree.set jets_sha._t'17
      (Vptr (elements_taptweak_symbol_block jets_secp._sha256_compression_portable) Ptrofs.zero) le2).
    eapply eval_funcall_internal with (e:=cu_env bk) (le1:=cu_temps bs os bc oc) (le2:=le3)
      (m1:=m1) (m2:=m3) (out:=Out_normal).
    + apply elements_taptweak_sha_cu_entry;exact Alloc.
    + change (fn_body jets_secp.f_sha256_compression_uchar) with (Ssequence (be_fill 15) be_tail).
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Prefix|];unfold be_tail.
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le3).
      * constructor;eapply eval_Elvalue.
        -- apply eval_Evar_global;[reflexivity|exact elements_taptweak_sha_dispatch_symbol].
        -- eapply deref_loc_value;[reflexivity|];unfold Mem.loadv.
           change (Ptrofs.unsigned Ptrofs.zero) with 0.
           rewrite Frame2 by (apply Fresh;exact VG);rewrite XL by exact VG;exact Dispatch.
      * change le3 with (set_opttemp None Vundef le3) at 2.
        eapply exec_Scall with
          (vf:=Vptr (elements_taptweak_symbol_block jets_secp._sha256_compression_portable) Ptrofs.zero)
          (vargs:=[Vptr bs os;Vptr bk Ptrofs.zero])
          (f:=Internal jets_secp.f_sha256_compression_portable) (vres:=Vundef).
        -- reflexivity.
        -- apply eval_Etempvar;apply PTree.gss.
        -- eapply eval_Econs.
           ++ apply eval_Etempvar;unfold le3;rewrite PTree.gso by discriminate;rewrite S;reflexivity.
           ++ reflexivity.
           ++ eapply eval_Econs with (v1:=Vptr bk Ptrofs.zero);[|reflexivity|apply eval_Enil].
              eapply eval_Elvalue;[eapply eval_Evar_local;reflexivity|];apply deref_loc_reference;reflexivity.
        -- exact elements_taptweak_sha_compression_funct.
        -- reflexivity.
        -- exact Call.
    + cbn;reflexivity.
    + rewrite elements_taptweak_sha_cu_blocks;exact Free.
  - split.
    + intros i Index;rewrite FrameF by (apply NotFresh;exact VS);rewrite (Output i Index).
      unfold blk;rewrite c_be_words_eq;[reflexivity|exact LB|].
      intros j J;eapply load_byte_range;apply Bytes;exact J.
    + split.
      * intros ch b ofs Old Outside;rewrite FrameF by (apply NotFresh;exact Old).
        rewrite Frame3;[|apply Valid2,XV;exact Old|exact Outside].
        rewrite Frame2 by (apply Fresh;exact Old);apply XL;exact Old.
      * split.
        -- intros b ofs k p Old Perm;apply PermF;[apply NotFresh;exact Old|].
           apply Perm3;[apply Valid2,XV;exact Old|];apply Perm2,XP;exact Perm.
        -- split;[intros b Old;apply ValidF,Valid3,Valid2,XV;exact Old|].
           eapply preserved_trans;[eapply alloc_preserved;exact Alloc|].
           eapply preserved_trans.
           ++ eapply (proj1 (internal_exec_preserved _ _ elements_taptweak_sha_pure_table_ok));[exact Prefix| |exact elements_taptweak_sha_fill_closed].
              apply plain_set;[apply plain_empty|reflexivity].
           ++ eapply preserved_trans;[eapply elements_taptweak_sha_round_preserved;exact Call|].
              eapply freelist_preserved;exact Free.
Qed.
Theorem eval_elements_taptweak_sha_compression_uchar_owned_at regs bytes m bs bb ob :
  length regs=8%nat -> length bytes=64%nat -> elements_taptweak_sha_startup m ->
  uint32_array_at m bs 0 regs -> Mem.range_perm m bs 0 32 Cur Freeable ->
  Ptrofs.unsigned ob+64<=Ptrofs.max_unsigned ->
  (forall i,(i<64)%nat -> Mem.load Mint8unsigned m bb (Ptrofs.unsigned ob+Z.of_nat i)=Some (Vint (nth i bytes Int.zero))) ->
  exists mf,Clight2.eval_funcall elements_taptweak_ge m (Internal jets_secp.f_sha256_compression_uchar)
    [Vptr bs Ptrofs.zero;Vptr bb ob] E0 mf Vundef /\
  uint32_array_at mf bs 0 (SHA256.hash_block regs (be_words bytes)) /\
  Mem.range_perm mf bs 0 32 Cur Freeable /\ lframe (fun b _=>b<>bs) m mf /\
  readonly_preserved m mf /\ elements_taptweak_sha_startup mf.
Proof.
  intros LR LB Startup State Owned ByteHi Bytes.
  assert (Access:forall i,(i<8)%nat ->Mem.valid_access m Mint32 bs (4*Z.of_nat i) Writable).
  { intros i Index;split.
    - intros pos Range;eapply Mem.perm_implies with (p1:=Freeable).
      + apply Owned;change (4*Z.of_nat i<=pos<4*Z.of_nat i+4) in Range;lia.
      + apply Memtype.perm_F_any.
    - change (4|4*Z.of_nat i);exists (Z.of_nat i);lia. }
  destruct (eval_elements_taptweak_sha_compression_uchar m bs Ptrofs.zero bb ob regs bytes LR LB
    ltac:(change (32<=18446744073709551615);lia) ByteHi
    (proj1 (proj1 Startup))
    ltac:(intros i Index;split;
      [apply State;apply nth_error_nth';rewrite LR;exact Index|apply Access;exact Index]) Bytes)
    as (mf & Call & Output & Loads & Perm & Valid & Preserved).
  assert (Frame:lframe (fun b _=>b<>bs) m mf).
  { split.
    - intros ch b ofs Old Outside;apply Loads;[exact Old|left;apply (Outside ofs);pose proof (size_chunk_pos ch);lia].
    - split;[intros;apply Perm;assumption|exact Valid]. }
  exists mf;split;[exact Call|];split.
  - intros i value Nth.
    assert (Index:(i<8)%nat).
    { rewrite <-(sha.common_lemmas.length_hash_block regs (be_words bytes) LR).
      - apply nth_error_Some;rewrite Nth;discriminate.
      - apply be_words_length;rewrite LB;reflexivity. }
    pose proof (Output i Index) as Load.
    apply nth_error_nth with (d:=Int.zero) in Nth;rewrite Nth in Load;exact Load.
  - split.
    + intros pos Range;apply Perm;[eapply Mem.perm_valid_block;apply (Owned 0);lia|apply Owned;exact Range].
    + split;[exact Frame|];split;[exact Preserved|].
      eapply elements_taptweak_sha_startup_preserved;[exact Startup|exact Preserved|exact Frame|].
      intros ofs;destruct (elements_taptweak_sha_startup_separate m bs 32 Startup ltac:(lia) Owned) as [Other _];congruence.
Qed.

Theorem eval_elements_taptweak_sha_compression_uchar_owned regs bytes m bs bb :
  length regs=8%nat -> length bytes=64%nat -> elements_taptweak_sha_startup m ->
  uint32_array_at m bs 0 regs -> Mem.range_perm m bs 0 32 Cur Freeable ->
  (forall i,(i<64)%nat -> Mem.load Mint8unsigned m bb (Z.of_nat i)=Some (Vint (nth i bytes Int.zero))) ->
  exists mf,Clight2.eval_funcall elements_taptweak_ge m (Internal jets_secp.f_sha256_compression_uchar)
    [Vptr bs Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef /\
  uint32_array_at mf bs 0 (SHA256.hash_block regs (be_words bytes)) /\
  Mem.range_perm mf bs 0 32 Cur Freeable /\ lframe (fun b _=>b<>bs) m mf /\
  readonly_preserved m mf /\ elements_taptweak_sha_startup mf.
Proof.
  intros LR LB Startup State Owned Bytes.
  exact (eval_elements_taptweak_sha_compression_uchar_owned_at regs bytes m bs bb Ptrofs.zero LR LB Startup State Owned
    ltac:(change (64<=18446744073709551615);lia) Bytes).
Qed.
