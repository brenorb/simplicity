(** The actual call of [sha256_compression_portable] in the SHA translation
    unit: allocation of its eight address-taken locals, execution of the body
    through the verified interpreter, and deallocation.  The state array ends
    up holding [SHA256.hash_block]; everything else is preserved. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_round C.jet_sha_interp C.jet_sha_interp_sound.
Require Import C.jet_sha_compress_fun C.jet_sha_compress_rounds.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 300.

(** Memory extension by allocation of fresh blocks. *)
Definition mext (m m' : mem) : Prop :=
  (forall b, Mem.valid_block m b -> Mem.valid_block m' b) /\
  (forall ch b ofs, Mem.valid_block m b -> Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
  (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
  (forall ch b ofs p, Mem.valid_access m ch b ofs p -> Mem.valid_access m' ch b ofs p).

Lemma mext_refl m : mext m m.
Proof.
  unfold mext. split; [auto|]. split; [reflexivity|]. split; auto.
Qed.

Lemma mext_trans m1 m2 m3 : mext m1 m2 -> mext m2 m3 -> mext m1 m3.
Proof.
  intros (V1 & L1 & P1 & A1) (V2 & L2 & P2 & A2). unfold mext.
  split; [intros b0 H; apply V2, V1, H|].
  split; [intros ch b0 ofs H; rewrite L2 by (apply V1; exact H); apply L1; exact H|].
  split; [intros b0 ofs k p H; apply P2, P1, H|].
  intros ch b0 ofs p H; apply A2, A1, H.
Qed.

Lemma mext_alloc m lo hi m' b : Mem.alloc m lo hi = (m', b) -> mext m m'.
Proof.
  intros HA. unfold mext.
  split; [intros b0 H; eapply Mem.valid_block_alloc; eauto|].
  split; [intros ch b0 ofs H; eapply Mem.load_alloc_unchanged; eauto|].
  split; [intros b0 ofs k p H; eapply Mem.perm_alloc_1; eauto|].
  intros ch b0 ofs p H; eapply Mem.valid_access_alloc_other; eauto.
Qed.

Lemma alloc4_access m m' b :
  Mem.alloc m 0 4 = (m', b) ->
  Mem.valid_access m' Mint32 b 0 Freeable /\ ~ Mem.valid_block m b /\ Mem.valid_block m' b /\
  Mem.range_perm m' b 0 4 Cur Freeable.
Proof.
  intros HA. split; [|split; [|split]].
  - eapply Mem.valid_access_alloc_same; [exact HA|lia|cbn; lia|exists 0; reflexivity].
  - eapply Mem.fresh_block_alloc; eauto.
  - eapply Mem.valid_new_block; eauto.
  - intros ofs Ho. eapply Mem.perm_alloc_2; eauto.
Qed.

(** Freeing a list of distinct, fully-owned blocks. *)
Lemma free_list_blocks : forall (l : list (block * Z * Z)) m,
  (forall b lo hi, In (b, lo, hi) l -> Mem.range_perm m b lo hi Cur Freeable) ->
  NoDup (map (fun x => fst (fst x)) l) ->
  exists m',
    Mem.free_list m l = Some m' /\
    (forall ch b ofs, ~ In b (map (fun x => fst (fst x)) l) -> Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, ~ In b (map (fun x => fst (fst x)) l) -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  induction l as [|[[b lo] hi] l IH]; intros m HP HN.
  - exists m. cbn. repeat split; auto.
  - cbn [map fst] in HN. apply NoDup_cons_iff in HN. destruct HN as [Hnotin HN'].
    assert (HPb : Mem.range_perm m b lo hi Cur Freeable) by (apply HP; left; reflexivity).
    destruct (Mem.range_perm_free m b lo hi HPb) as [m1 HF].
    destruct (IH m1) as (m' & HFL & HL & HPm & HV).
    + intros b' lo' hi' Hin ofs Ho. eapply Mem.perm_free_1; [exact HF| |apply (HP b' lo' hi' (or_intror Hin)); exact Ho].
      left. intro Heq. subst b'. apply Hnotin.
      exact (in_map (fun x : block * Z * Z => fst (fst x)) l (b, lo', hi') Hin).
    + exact HN'.
    + exists m'. cbn [Mem.free_list]. rewrite HF. split; [exact HFL|]. split; [|split].
      * intros ch b' ofs Hb'.
        rewrite HL by (intro Hi; apply Hb'; right; exact Hi).
        eapply Mem.load_free; [exact HF|]. left. intro Heq. subst b'. apply Hb'. left. reflexivity.
      * intros b' ofs k p Hb' Hp. apply HPm; [intro Hi; apply Hb'; right; exact Hi|].
        eapply Mem.perm_free_1; [exact HF| |exact Hp]. left. intro Heq. subst b'. apply Hb'. left. reflexivity.
      * intros b' Hv. apply HV. eapply Mem.valid_block_free_1; eauto.
Qed.

Definition sha_locals_env (ba bb bc0 bd be bf bg bh : block) : Clight.env :=
  PTree.set _h (bh, tuint) (PTree.set _g (bg, tuint) (PTree.set _f (bf, tuint) (PTree.set _e (be, tuint)
    (PTree.set _d (bd, tuint) (PTree.set _c (bc0, tuint) (PTree.set _b (bb, tuint)
      (PTree.set _a (ba, tuint) empty_env))))))).

Theorem eval_sha_compression m bs os bc oc (regs blk : list int) :
  length regs = 8%nat -> length blk = 16%nat ->
  Ptrofs.unsigned os + 32 <= Ptrofs.max_unsigned ->
  Ptrofs.unsigned oc + 64 <= Ptrofs.max_unsigned ->
  (bs <> bc \/ Ptrofs.unsigned os + 32 <= Ptrofs.unsigned oc \/ Ptrofs.unsigned oc + 64 <= Ptrofs.unsigned os) ->
  (forall i, (i < 8)%nat ->
     Mem.load Mint32 m bs (Ptrofs.unsigned os + 4 * Z.of_nat i) = Some (Vint (nth i regs Int.zero)) /\
     Mem.valid_access m Mint32 bs (Ptrofs.unsigned os + 4 * Z.of_nat i) Writable) ->
  (forall i, (i < 16)%nat ->
     Mem.load Mint32 m bc (Ptrofs.unsigned oc + 4 * Z.of_nat i) = Some (Vint (nth i blk Int.zero))) ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_compression_portable)
      [Vptr bs os; Vptr bc oc] E0 m' Vundef /\
    (forall i, (i < 8)%nat ->
       Mem.load Mint32 m' bs (Ptrofs.unsigned os + 4 * Z.of_nat i) =
         Some (Vint (nth i (SHA256.hash_block regs blk) Int.zero))) /\
    (forall ch b ofs, Mem.valid_block m b ->
       (b <> bs \/ ofs + size_chunk ch <= Ptrofs.unsigned os \/ Ptrofs.unsigned os + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros Hlr Hlb Hso Hco Hsc HS HC.
  destruct (Mem.alloc m 0 4) as [m1 ba] eqn:A1.
  destruct (Mem.alloc m1 0 4) as [m2 bb] eqn:A2.
  destruct (Mem.alloc m2 0 4) as [m3 bc0] eqn:A3.
  destruct (Mem.alloc m3 0 4) as [m4 bd] eqn:A4.
  destruct (Mem.alloc m4 0 4) as [m5 be] eqn:A5.
  destruct (Mem.alloc m5 0 4) as [m6 bf] eqn:A6.
  destruct (Mem.alloc m6 0 4) as [m7 bg] eqn:A7.
  destruct (Mem.alloc m7 0 4) as [m8 bh] eqn:A8.
  pose proof (mext_alloc _ _ _ _ _ A1) as X1. pose proof (mext_alloc _ _ _ _ _ A2) as X2.
  pose proof (mext_alloc _ _ _ _ _ A3) as X3. pose proof (mext_alloc _ _ _ _ _ A4) as X4.
  pose proof (mext_alloc _ _ _ _ _ A5) as X5. pose proof (mext_alloc _ _ _ _ _ A6) as X6.
  pose proof (mext_alloc _ _ _ _ _ A7) as X7. pose proof (mext_alloc _ _ _ _ _ A8) as X8.
  destruct (alloc4_access _ _ _ A1) as (P1 & F1 & V1 & R1). destruct (alloc4_access _ _ _ A2) as (P2 & F2 & V2 & R2).
  destruct (alloc4_access _ _ _ A3) as (P3 & F3 & V3 & R3). destruct (alloc4_access _ _ _ A4) as (P4 & F4 & V4 & R4).
  destruct (alloc4_access _ _ _ A5) as (P5 & F5 & V5 & R5). destruct (alloc4_access _ _ _ A6) as (P6 & F6 & V6 & R6).
  destruct (alloc4_access _ _ _ A7) as (P7 & F7 & V7 & R7). destruct (alloc4_access _ _ _ A8) as (P8 & F8 & V8 & R8).
  assert (X28 : mext m2 m8) by (repeat (eapply mext_trans; [eassumption|]); apply mext_refl).
  assert (X18 : mext m1 m8) by (eapply mext_trans; eassumption).
  assert (X08 : mext m m8) by (eapply mext_trans; eassumption).
  assert (X38 : mext m3 m8) by (repeat (eapply mext_trans; [eassumption|]); apply mext_refl).
  assert (X48 : mext m4 m8) by (repeat (eapply mext_trans; [eassumption|]); apply mext_refl).
  assert (X58 : mext m5 m8) by (repeat (eapply mext_trans; [eassumption|]); apply mext_refl).
  assert (X68 : mext m6 m8) by (repeat (eapply mext_trans; [eassumption|]); apply mext_refl).
  assert (X78 : mext m7 m8) by (repeat (eapply mext_trans; [eassumption|]); apply mext_refl).
  set (lb := [ba; bb; bc0; bd; be; bf; bg; bh]).
  set (env := sha_locals_env ba bb bc0 bd be bf bg bh).
  (* validity ordering of the fresh blocks *)
  assert (W1 : Mem.valid_block m2 ba) by (apply X2; exact V1).
  assert (W2 : Mem.valid_block m3 bb) by (apply X3; exact V2).
  assert (W3 : Mem.valid_block m4 bc0) by (apply X4; exact V3).
  assert (W4 : Mem.valid_block m5 bd) by (apply X5; exact V4).
  assert (W5 : Mem.valid_block m6 be) by (apply X6; exact V5).
  assert (W6 : Mem.valid_block m7 bf) by (apply X7; exact V6).
  assert (Hfresh : forall b, Mem.valid_block m b -> ~ In b lb).
  { intros b Hv Hin. unfold lb in Hin. cbn in Hin.
    assert (Hv1 := proj1 X1 b Hv). assert (Hv2 := proj1 X2 b Hv1). assert (Hv3 := proj1 X3 b Hv2).
    assert (Hv4 := proj1 X4 b Hv3). assert (Hv5 := proj1 X5 b Hv4). assert (Hv6 := proj1 X6 b Hv5).
    assert (Hv7 := proj1 X7 b Hv6).
    repeat (destruct Hin as [Hin|Hin]; [subst b; contradiction|]). exact Hin. }
  assert (Hnodup : NoDup lb).
  { unfold lb.
    assert (Y1 := proj1 X3 _ W1). assert (Y2 := proj1 X4 _ Y1). assert (Y3 := proj1 X5 _ Y2).
    assert (Y4 := proj1 X6 _ Y3). assert (Y5 := proj1 X7 _ Y4).
    assert (Z2 := proj1 X4 _ W2). assert (Z3 := proj1 X5 _ Z2). assert (Z4 := proj1 X6 _ Z3).
    assert (Z5 := proj1 X7 _ Z4).
    assert (U3 := proj1 X5 _ W3). assert (U4 := proj1 X6 _ U3). assert (U5 := proj1 X7 _ U4).
    assert (T4 := proj1 X6 _ W4). assert (T5 := proj1 X7 _ T4).
    assert (S5 := proj1 X7 _ W5).
    repeat constructor; cbn; intro Hin;
      repeat (destruct Hin as [Hin|Hin]; [subst; contradiction|]); exact Hin. }
  assert (Hvs : Mem.valid_block m bs).
  { destruct (HS 0%nat ltac:(lia)) as [_ PW]. eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies; [exact PW|constructor]. }
  assert (Hvc : Mem.valid_block m bc).
  { pose proof (HC 0%nat ltac:(lia)) as HL. apply Mem.load_valid_access in HL.
    eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies; [exact HL|constructor]. }
  assert (Hbs : ~ In bs lb) by (apply Hfresh; exact Hvs).
  assert (Hbc : ~ In bc lb) by (apply Hfresh; exact Hvc).
  assert (Henv : forall i x b, nth_error lids i = Some x -> nth_error lb i = Some b -> env!x = Some (b, tuint)).
  { intros i x b Hx Hb. unfold lb in Hb.
    do 8 (destruct i as [|i]; [cbn in Hx, Hb; injection Hx as <-; injection Hb as <-; reflexivity|]).
    cbn in Hx. destruct i; discriminate. }
  set (st0 := mk_cst (repeat Int.zero 16) 0 (repeat Int.zero 8) 0 [] regs blk).
  set (le0 := PTree.set _chunk (Vptr bc oc) (PTree.set _s (Vptr bs os)
    (create_undef_temps (fn_temps f_sha256_compression_portable)))).
  assert (Hacc8 : forall b, In b lb -> Mem.valid_access m8 Mint32 b 0 Writable).
  { intros b Hin. eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    unfold lb in Hin. cbn in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
    - apply (proj2 (proj2 (proj2 X18))). exact P1.
    - apply (proj2 (proj2 (proj2 X28))). exact P2.
    - apply (proj2 (proj2 (proj2 X38))). exact P3.
    - apply (proj2 (proj2 (proj2 X48))). exact P4.
    - apply (proj2 (proj2 (proj2 X58))). exact P5.
    - apply (proj2 (proj2 (proj2 X68))). exact P6.
    - apply (proj2 (proj2 (proj2 X78))). exact P7.
    - exact P8. }
  assert (HR0 : sha_R lb bs os bc oc st0 le0 m8).
  { unfold sha_R, st0. cbn [wv wdef lv ldef scratch sarr chunk].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hlr|]. split; [exact Hlb|].
    split; [lia|]. split; [lia|].
    split; [intros i x Hi; lia|].
    split; [intros t v Hv; cbn in Hv; discriminate|].
    split; [unfold le0; rewrite PTree.gso by discriminate; apply PTree.gss|].
    split; [unfold le0; apply PTree.gss|].
    split.
    { intros i b Hb. split; [|intros Hi; lia].
      apply Hacc8. eapply nth_error_In. exact Hb. }
    split.
    { intros i Hi. destruct (HS i Hi) as [HL PW]. split.
      - rewrite (proj1 (proj2 X08)) by exact Hvs. exact HL.
      - apply (proj2 (proj2 (proj2 X08))). exact PW. }
    { intros i Hi. rewrite (proj1 (proj2 X08)) by exact Hvc. exact (HC i Hi). } }
  destruct (compress_interp regs blk Hlr Hlb) as (stf & Hinterp & Hsarr).
  destruct (interp_spine_sound env lb bs os bc oc ltac:(reflexivity) Hnodup Hbs Hbc Henv
    ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) Hso Hco Hsc 79
    (fn_body f_sha256_compression_portable) st0 stf le0 m8 HR0 Hinterp)
    as (le' & me & Hexec & HRf & (FL & FP & FV)).
  (* free the locals *)
  set (fl := [bg; bc0; ba; be; bh; bd; bb; bf]).
  assert (Hblocks : blocks_of_env sha_ge env = map (fun b => (b, 0, 4)) fl) by reflexivity.
  assert (Hincl : incl lb fl) by (intros x Hx; unfold lb, fl in *; cbn in *; tauto).
  assert (Hincl' : incl fl lb) by (intros x Hx; unfold lb, fl in *; cbn in *; tauto).
  assert (Hnodupf : NoDup fl) by (eapply NoDup_incl_NoDup; [exact Hnodup|cbn; lia|exact Hincl]).
  assert (Hmapfst : map (fun x : block * Z * Z => fst (fst x)) (map (fun b => (b, 0, 4)) fl) = fl)
    by reflexivity.
  assert (Hperm8 : forall b, In b lb -> Mem.range_perm m8 b 0 4 Cur Freeable).
  { intros b Hin ofs Ho. unfold lb in Hin. cbn in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
    - apply (proj1 (proj2 (proj2 X18))). apply R1; exact Ho.
    - apply (proj1 (proj2 (proj2 X28))). apply R2; exact Ho.
    - apply (proj1 (proj2 (proj2 X38))). apply R3; exact Ho.
    - apply (proj1 (proj2 (proj2 X48))). apply R4; exact Ho.
    - apply (proj1 (proj2 (proj2 X58))). apply R5; exact Ho.
    - apply (proj1 (proj2 (proj2 X68))). apply R6; exact Ho.
    - apply (proj1 (proj2 (proj2 X78))). apply R7; exact Ho.
    - apply R8; exact Ho. }
  destruct (free_list_blocks (map (fun b => (b, 0, 4)) fl) me) as (mf & HFL & HLf & HPf & HVf).
  { intros b lo hi Hin. apply in_map_iff in Hin. destruct Hin as (b' & Heq & Hin'). injection Heq as <- <- <-.
    intros ofs Ho. apply FP. apply Hperm8; [apply Hincl'; exact Hin'|exact Ho]. }
  { rewrite Hmapfst. exact Hnodupf. }
  rewrite Hmapfst in HLf, HPf.
  exists mf. split; [|split; [|split; [|split]]].
  - eapply eval_funcall_internal with (e := env) (le1 := le0) (m1 := m8) (le2 := le') (m2 := me)
      (out := Out_normal).
    + apply function_entry2_intro.
      * cbn. repeat constructor; cbn; intuition discriminate.
      * cbn. repeat constructor; cbn; intuition discriminate.
      * assert (D : if list_disjoint_dec ident_eq (var_names (fn_params f_sha256_compression_portable))
          (var_names (fn_temps f_sha256_compression_portable)) then True else False) by (vm_compute; exact I).
        destruct (list_disjoint_dec ident_eq (var_names (fn_params f_sha256_compression_portable))
          (var_names (fn_temps f_sha256_compression_portable))); [assumption|contradiction].
      * cbn [f_sha256_compression_portable fn_vars].
        eapply alloc_variables_cons; [exact A1|]. eapply alloc_variables_cons; [exact A2|].
        eapply alloc_variables_cons; [exact A3|]. eapply alloc_variables_cons; [exact A4|].
        eapply alloc_variables_cons; [exact A5|]. eapply alloc_variables_cons; [exact A6|].
        eapply alloc_variables_cons; [exact A7|]. eapply alloc_variables_cons; [exact A8|].
        apply alloc_variables_nil.
      * reflexivity.
    + exact Hexec.
    + cbn. reflexivity.
    + rewrite Hblocks. exact HFL.
  - intros i Hi.
    rewrite HLf by (intro Hin; apply Hbs; apply Hincl'; exact Hin).
    destruct HRf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RSA & _).
    rewrite <- Hsarr. exact (proj1 (RSA i Hi)).
  - intros chunk0 b ofs Hv Ho.
    assert (Hnl : ~ In b lb) by (apply Hfresh; exact Hv).
    rewrite HLf by (intro Hin; apply Hnl; apply Hincl'; exact Hin).
    rewrite FL by assumption.
    exact (proj1 (proj2 X08) chunk0 b ofs Hv).
  - intros b ofs k p Hv Hp.
    assert (Hnl : ~ In b lb) by (apply Hfresh; exact Hv).
    apply HPf; [intro Hin; apply Hnl; apply Hincl'; exact Hin|].
    apply FP. exact (proj1 (proj2 (proj2 X08)) b ofs k p Hp).
  - intros b Hv. apply HVf. apply FV. exact (proj1 X08 b Hv).
Qed.
