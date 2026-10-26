(** The frozen secp byte-compression wrapper, including its actual indirect
    call and private array lifetime. The byte-reading prefix reuses the SHA
    proof through checked statement transport; the dispatch load is explicit. *)
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

Definition secp_sha_dispatch_ok m :=
  Mem.load Mptr m (secp_symbol_block jets_secp._simplicity_sha256_compression) 0=
    Some (Vptr (secp_symbol_block jets_secp._sha256_compression_portable) Ptrofs.zero).

Lemma secp_sha_dispatch_symbol :
  Genv.find_symbol secp_ge jets_secp._simplicity_sha256_compression=
    Some (secp_symbol_block jets_secp._simplicity_sha256_compression).
Proof. vm_compute;reflexivity. Qed.
Lemma secp_sha_compression_funct :
  Genv.find_funct secp_ge (Vptr (secp_symbol_block jets_secp._sha256_compression_portable) Ptrofs.zero)=
    Some (Internal jets_secp.f_sha256_compression_portable).
Proof. vm_compute;reflexivity. Qed.
Lemma secp_sha_fill_checked : stmt_okb sha_ge secp_ge (map fst secp_sha_pure_helpers)
  [jets_sha.___compound] (be_fill 15)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma secp_sha_fill_closed : closed_stmtb secp_sha_pure_helpers (be_fill 15)=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque sha_ge secp_ge.

Lemma secp_sha_cu_dom bk : edom (cu_env bk) [(jets_sha.___compound,tarray tuint 16)].
Proof.
  intros id b ty Lookup;unfold cu_env in Lookup;rewrite PTree.gsspec in Lookup.
  destruct (peq id jets_sha.___compound) as [Same|Other].
  - subst id;injection Lookup as <- <-;left;reflexivity.
  - rewrite PTree.gempty in Lookup;discriminate.
Qed.
Lemma secp_sha_fill_transport bk le m trace lef mf out :
  Clight2.exec_stmt sha_ge (cu_env bk) le m (be_fill 15) trace lef mf out ->
  Clight2.exec_stmt secp_ge (cu_env bk) le m (be_fill 15) trace lef mf out.
Proof.
  intro Run;exact (proj1 (transport_main sha_ge secp_ge (map fst secp_sha_pure_helpers)
    (transportable_of_entries sha_ge secp_ge secp_sha_pure_helpers
      (secp_sha_helpers_entries sha_ge (or_intror eq_refl))
      (secp_sha_helpers_ok sha_ge (or_intror eq_refl))))
    (cu_env bk) le m (be_fill 15) trace lef mf out Run
    [(jets_sha.___compound,tarray tuint 16)] (secp_sha_cu_dom bk) secp_sha_fill_checked).
Qed.
Lemma secp_sha_cu_entry m m1 bk bs os bc oc : Mem.alloc m 0 64=(m1,bk) ->
  function_entry2 secp_ge jets_secp.f_sha256_compression_uchar [Vptr bs os;Vptr bc oc] m
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
Lemma secp_sha_cu_blocks bk : blocks_of_env secp_ge (cu_env bk)=[(bk,0,64)].
Proof. reflexivity. Qed.

Theorem eval_secp_sha_compression_uchar m bs os bc oc (regs bytes:list int) :
  length regs=8%nat -> length bytes=64%nat ->
  Ptrofs.unsigned os+32<=Ptrofs.max_unsigned -> Ptrofs.unsigned oc+64<=Ptrofs.max_unsigned ->
  secp_sha_dispatch_ok m ->
  (forall i,(i<8)%nat ->
    Mem.load Mint32 m bs (Ptrofs.unsigned os+4*Z.of_nat i)=Some (Vint (nth i regs Int.zero)) /\
    Mem.valid_access m Mint32 bs (Ptrofs.unsigned os+4*Z.of_nat i) Writable) ->
  (forall i,(i<64)%nat ->
    Mem.load Mint8unsigned m bc (Ptrofs.unsigned oc+Z.of_nat i)=Some (Vint (nth i bytes Int.zero))) ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal jets_secp.f_sha256_compression_uchar)
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
  assert (VG:Mem.valid_block m (secp_symbol_block jets_secp._simplicity_sha256_compression)).
  { unfold secp_sha_dispatch_ok in Dispatch;apply Mem.load_valid_access in Dispatch.
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
  pose proof (secp_sha_fill_transport _ _ _ _ _ _ _ FillRun) as Prefix.
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
  pose proof (secp_sha_compression_transport jets_sha._sha256_compression_portable
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
      (Vptr (secp_symbol_block jets_secp._sha256_compression_portable) Ptrofs.zero) le2).
    eapply eval_funcall_internal with (e:=cu_env bk) (le1:=cu_temps bs os bc oc) (le2:=le3)
      (m1:=m1) (m2:=m3) (out:=Out_normal).
    + apply secp_sha_cu_entry;exact Alloc.
    + change (fn_body jets_secp.f_sha256_compression_uchar) with (Ssequence (be_fill 15) be_tail).
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Prefix|];unfold be_tail.
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le3).
      * constructor;eapply eval_Elvalue.
        -- apply eval_Evar_global;[reflexivity|exact secp_sha_dispatch_symbol].
        -- eapply deref_loc_value;[reflexivity|];unfold Mem.loadv.
           change (Ptrofs.unsigned Ptrofs.zero) with 0.
           rewrite Frame2 by (apply Fresh;exact VG);rewrite XL by exact VG;exact Dispatch.
      * change le3 with (set_opttemp None Vundef le3) at 2.
        eapply exec_Scall with
          (vf:=Vptr (secp_symbol_block jets_secp._sha256_compression_portable) Ptrofs.zero)
          (vargs:=[Vptr bs os;Vptr bk Ptrofs.zero])
          (f:=Internal jets_secp.f_sha256_compression_portable) (vres:=Vundef).
        -- reflexivity.
        -- apply eval_Etempvar;apply PTree.gss.
        -- eapply eval_Econs.
           ++ apply eval_Etempvar;unfold le3;rewrite PTree.gso by discriminate;rewrite S;reflexivity.
           ++ reflexivity.
           ++ eapply eval_Econs with (v1:=Vptr bk Ptrofs.zero);[|reflexivity|apply eval_Enil].
              eapply eval_Elvalue;[eapply eval_Evar_local;reflexivity|];apply deref_loc_reference;reflexivity.
        -- exact secp_sha_compression_funct.
        -- reflexivity.
        -- exact Call.
    + cbn;reflexivity.
    + rewrite secp_sha_cu_blocks;exact Free.
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
           ++ eapply (proj1 (internal_exec_preserved _ _ secp_sha_pure_table_ok));[exact Prefix| |exact secp_sha_fill_closed].
              apply plain_set;[apply plain_empty|reflexivity].
           ++ eapply preserved_trans;[eapply secp_sha_compression_preserved;exact Call|].
              eapply freelist_preserved;exact Free.
Qed.
