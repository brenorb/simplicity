(** [copyOutput] (elements/env.c): the output record built from a raw
    output, with the null-data parse advancing the caller's opcode cursor. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_init C.jet_sha_ctx_abs C.jet_sha_be32_exec C.jet_sha_uchars_exec.
Require Import C.jet_sha_compress_call C.jet_sha_tapdata_prep.
Require Import C.jet_elements_env_field_eval C.jet_elements_env_tomidstate C.jet_elements_env_hashbuffer.
Require Import C.jet_elements_env_copyrawamt C.jet_elements_env_copyrawconf C.jet_elements_env_calc_token.
Require Import C.jet_elements_env_isfee C.jet_elements_env_nulldata_count.
Require Import C.jet_elements_env_parse_defs C.jet_elements_env_parse_mem C.jet_elements_env_parse_ops.
Require Import C.jet_elements_env_parse_iter C.jet_elements_env_parse.
Require Import C.jet_elements_env_copyout_defs C.jet_elements_env_copyout_calls C.jet_elements_env_copyout_stmts.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Ltac zo :=
  repeat match goal with
         | H : ?a <> ?b |- _ => match type of a with block => clear H end
         end; lia.

Definition co_env (bK1 bK2 : block) : env :=
  PTree.set ___compound__1 (bK2, RBUF) (PTree.set ___compound (bK1, RBUF) empty_env).

Lemma co_entry m m1 m2 bK1 bK2 v1 v2 v3 v4 :
  Mem.alloc m 0 16 = (m1, bK1) -> Mem.alloc m1 0 16 = (m2, bK2) ->
  function_entry2 sha_ge f_copyOutput [v1; v2; v3; v4] m (co_env bK1 bK2)
    (PTree.set _output v4 (PTree.set _allocationLen v3 (PTree.set _allocation v2
       (PTree.set _result v1 (create_undef_temps (fn_temps f_copyOutput)))))) m2.
Proof.
  intros A1 A2. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst; try contradiction; discriminate.
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bK1); [change (Mem.alloc m 0 16 = (m1, bK1)); exact A1|].
    eapply alloc_variables_cons with (m1 := m2) (b1 := bK2); [change (Mem.alloc m1 0 16 = (m2, bK2)); exact A2|].
    constructor.
  - reflexivity.
Qed.

Lemma co_blocks bK1 bK2 :
  blocks_of_env sha_ge (co_env bK1 bK2) = [(bK2, 0, 16); (bK1, 0, 16)].
Proof. vm_compute. reflexivity. Qed.

Local Opaque sha_ge.

(** What the null-data parse leaves in the record and in the caller's
    cursor cells. *)
Definition co_pnd (m : mem) (bres : block) (ores : Z) (ba : block) (oa : Z) (bl : block) (ol : Z)
    (bop : block) (oop alen : Z) (r : option (list pn_ent)) : Prop :=
  match r with
  | None => Mem.load Mptr m bres (ores + 224) = Some (Vlong Int64.zero)
  | Some ents =>
      Z.of_nat (length ents) <= alen /\
      Mem.load Mptr m bres (ores + 224) = Some (Vptr bop (Ptrofs.repr oop)) /\
      Mem.load Mint64 m bres (ores + 224 + 8) = Some (Vlong (Int64.repr (Z.of_nat (length ents)))) /\
      (forall k, (k < length ents)%nat -> pn_ent_at bop oop m (Z.of_nat k) (nth k ents (0, None))) /\
      Mem.load Mptr m ba oa = Some (Vptr bop (Ptrofs.repr (oop + 36 * Z.of_nat (length ents)))) /\
      Mem.load Mint64 m bl ol = Some (Vlong (Int64.repr (alen - Z.of_nat (length ents))))
  end.

Lemma co_pnd_same m m' bres ores ba oa bl ol bop oop alen r :
  (forall ch ofs, ores + 224 <= ofs -> ofs + size_chunk ch <= ores + 240 ->
     Mem.load ch m' bres ofs = Mem.load ch m bres ofs) ->
  same_on bop m m' -> same_on ba m m' -> same_on bl m m' ->
  co_pnd m bres ores ba oa bl ol bop oop alen r -> co_pnd m' bres ores ba oa bl ol bop oop alen r.
Proof.
  intros HR HO HA HL. destruct r as [ents|]; cbn [co_pnd].
  - intros (H1 & H2 & H3 & H4 & H5 & H6). split; [exact H1|].
    split; [rewrite HR by (change (size_chunk Mptr) with 8; lia); exact H2|].
    split; [rewrite HR by (change (size_chunk Mint64) with 8; lia); exact H3|].
    split; [intros k Hk; apply (pn_ent_at_ext bop oop m m'); [exact HO|exact (H4 k Hk)]|].
    split; [rewrite HA; exact H5|rewrite HL; exact H6].
  - intros H. rewrite HR by (change (size_chunk Mptr) with 8; lia). exact H.
Qed.

Definition co_isnd (r : option (list pn_ent)) : bool := match r with None => false | Some _ => true end.

Definition co_v7 (bop : block) (oop : Z) (r : option (list pn_ent)) : val :=
  match r with None => Vlong Int64.zero | Some _ => Vptr bop (Ptrofs.repr oop) end.

Theorem eval_copyOutput (Hmodel : memcpy_model) m bres ores bout oout ba oa bl ol bop oop alen
    (sA : rawsrc) dA (sV : rawsrc) dV (sN : rawsrc) dN (sS : bufsrc) lenS (sJ : bufsrc) lenJ (sR : bufsrc) lenR :
  0 <= ores /\ ores + 248 <= Ptrofs.max_unsigned -> (8 | ores) ->
  0 <= oout /\ oout + 72 <= Ptrofs.max_unsigned ->
  0 <= oa /\ oa + 8 <= Ptrofs.max_unsigned -> 0 <= ol /\ ol + 8 <= Ptrofs.max_unsigned ->
  0 <= oop /\ oop + 36 * alen <= Ptrofs.max_unsigned -> (4 | oop) -> 0 <= alen <= 4294967295 ->
  Mem.load Mptr m bout oout = Some (rs_val sA) ->
  Mem.load Mptr m bout (oout + 8) = Some (rs_val sV) ->
  Mem.load Mptr m bout (oout + 16) = Some (rs_val sN) ->
  buf_at m bout (oout + 24) sS lenS -> buf_at m bout (oout + 40) sJ lenJ -> buf_at m bout (oout + 56) sR lenR ->
  conf_ok m sA dA -> amt_ok m sV dV -> conf_ok m sN dN ->
  Mem.range_perm m bres ores (ores + 248) Cur Writable ->
  Mem.load Mptr m ba oa = Some (Vptr bop (Ptrofs.repr oop)) ->
  Mem.load Mint64 m bl ol = Some (Vlong (Int64.repr alen)) ->
  Mem.range_perm m bop oop (oop + 36 * alen) Cur Writable ->
  Mem.weak_valid_pointer m bop oop = true ->
  Mem.valid_access m Mptr ba oa Writable -> Mem.valid_access m Mint64 bl ol Writable ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  bout <> bres -> rs_other sA bres -> rs_other sV bres -> rs_other sN bres ->
  buf_other sS bres -> buf_other sJ bres -> buf_other sR bres -> GC <> bres -> GM <> bres ->
  bres <> bop -> ba <> bop -> bl <> bop -> bout <> bop -> buf_other sS bop -> GC <> bop -> GM <> bop ->
  ba <> bres -> bl <> bres -> ba <> bl -> bout <> ba -> bout <> bl ->
  buf_other sJ bop -> buf_other sJ ba -> buf_other sJ bl ->
  buf_other sR bop -> buf_other sR ba -> buf_other sR bl ->
  GC <> ba -> GC <> bl -> GM <> ba -> GM <> bl ->
  exists mf,
    Clight2.eval_funcall sha_ge m (Internal f_copyOutput)
      [Vptr bres (Ptrofs.repr ores); Vptr ba (Ptrofs.repr oa); Vptr bl (Ptrofs.repr ol); Vptr bout (Ptrofs.repr oout)]
      E0 mf Vundef /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 mf bres (ores + 180 + 4 * Z.of_nat j) =
        Some (Vint (nth j (hash_buffer_regs (buf_bytes sS)) Int.zero))) /\
    Mem.load Mint8unsigned mf bres (ores + 241) = Some (Vint (b2i (Int.eq (Int.repr 0) lenS))) /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 mf bres (ores + 4 * Z.of_nat j) =
        Some (Vint (nth j (snd (conf_of dA)) Int.zero))) /\
    Mem.load Mint32 mf bres (ores + 32) = Some (Vint (fst (conf_of dA))) /\
    Mem.load Mint32 mf bres (ores + 104 + 32) = Some (Vint (amt_prefix dV)) /\
    amt_at mf bres (ores + 104) dV /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 mf bres (ores + 144 + 4 * Z.of_nat j) =
        Some (Vint (nth j (snd (conf_of dN)) Int.zero))) /\
    Mem.load Mint32 mf bres (ores + 144 + 32) = Some (Vint (fst (conf_of dN))) /\
    co_pnd mf bres ores ba oa bl ol bop oop alen (pn_run alen lenS (buf_bytes sS)) /\
    Mem.load Mint8unsigned mf bres (ores + 240) = Some (Vint (b2i (co_isnd (pn_run alen lenS (buf_bytes sS))))) /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 mf bres (ores + 36 + 4 * Z.of_nat j) =
        Some (Vint (nth j (hash_buffer_regs (if is_conf (fst (conf_of dA)) then buf_bytes sJ else [])) Int.zero))) /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 mf bres (ores + 68 + 4 * Z.of_nat j) =
        Some (Vint (nth j (hash_buffer_regs (if is_conf (amt_prefix dV) then buf_bytes sR else [])) Int.zero))) /\
    Mem.load Mint64 mf bres (ores + 216) = Some (Vlong Int64.zero) /\
    (forall ch b ofs, Mem.valid_block m b ->
       (b <> bres \/ ofs + size_chunk ch <= ores \/ ores + 248 <= ofs) ->
       (b <> bop \/ ofs + size_chunk ch <= oop \/ oop + 36 * alen <= ofs) ->
       (b <> ba \/ ofs + size_chunk ch <= oa \/ oa + 8 <= ofs) ->
       (b <> bl \/ ofs + size_chunk ch <= ol \/ ol + 8 <= ofs) ->
       Mem.load ch mf b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm mf b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros Hores HorA Hoout Hoa Hol Hoop HoopA Halen HLA HLV HLN HbS HbJ HbR HcA HcV HcN PR HLa HLl PO HW VAa VAl
    Hdisp HMax Nor NAr NVr NNr NSr NJr NRr NGr NMr Nro Nao Nlo Noo NSo NGo NMo Nar Nlr Nal Noa Nol
    NJo NJa NJl NRo NRa NRl NGa NGl NMa NMl.
  assert (VG : Mem.valid_block m GC).
  { pose proof Hdisp as Hd'. unfold sha_dispatch_ok in Hd'. exact (pn_load_valid _ _ _ _ _ Hd'). }
  pose proof (pn_load_valid _ _ _ _ _ HMax) as VM.
  assert (Vr : Mem.valid_block m bres) by (eapply Mem.perm_valid_block; apply (PR ores); zo).
  pose proof (pn_load_valid _ _ _ _ _ HLa) as Va.
  pose proof (pn_load_valid _ _ _ _ _ HLl) as Vl.
  pose proof (pn_load_valid _ _ _ _ _ HLA) as Vo.
  pose proof (weak_valid_block _ _ _ HW) as Vop.
  destruct (Mem.alloc m 0 16) as [ma1 bK1] eqn:A1.
  destruct (Mem.alloc ma1 0 16) as [m0 bK2] eqn:A2.
  assert (HAL : alloc_list m [16; 16] = (m0, [bK1; bK2])).
  { cbn [alloc_list]. rewrite A1, A2. reflexivity. }
  destruct (alloc_list_props _ _ _ _ HAL) as ((XV & XL & XP & XA) & FRh & ND & FA).
  inversion FA as [|? ? ? ? [PK10 VK10] FA1]; subst.
  inversion FA1 as [|? ? ? ? [PK20 VK20] FA2]; subst. clear FA FA1 FA2 HAL.
  assert (DK : bK1 <> bK2).
  { inversion ND as [|? ? HN1 _]; subst. cbn [In] in HN1. intro E. apply HN1. left. symmetry. exact E. }
  assert (NF : forall b, Mem.valid_block m b -> b <> bK1 /\ b <> bK2).
  { intros b Hb. pose proof (FRh b Hb) as HN. cbn [In] in HN. split; intro E; apply HN; rewrite E; tauto. }
  set (e := co_env bK1 bK2).
  set (le0 := PTree.set _output (Vptr bout (Ptrofs.repr oout)) (PTree.set _allocationLen (Vptr bl (Ptrofs.repr ol))
     (PTree.set _allocation (Vptr ba (Ptrofs.repr oa)) (PTree.set _result (Vptr bres (Ptrofs.repr ores))
        (create_undef_temps (fn_temps f_copyOutput)))))).
  assert (FIN : forall le' mX,
    Clight2.exec_stmt sha_ge e le0 m0 (fn_body f_copyOutput) E0 le' mX Out_normal ->
    (forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm mX b ofs k p) ->
    exists mf,
      Clight2.eval_funcall sha_ge m (Internal f_copyOutput)
        [Vptr bres (Ptrofs.repr ores); Vptr ba (Ptrofs.repr oa); Vptr bl (Ptrofs.repr ol); Vptr bout (Ptrofs.repr oout)]
        E0 mf Vundef /\
      (forall ch b ofs, Mem.valid_block m b -> Mem.load ch mf b ofs = Mem.load ch mX b ofs) /\
      (forall b ofs k p, Mem.valid_block m b -> Mem.perm mX b ofs k p -> Mem.perm mf b ofs k p) /\
      (forall b, Mem.valid_block mX b -> Mem.valid_block mf b)).
  { intros le' mX HX HPX.
    destruct (free_list_blocks [(bK2, 0, 16); (bK1, 0, 16)] mX) as (mf & HFL & HLf & HPf & HVf).
    { intros b0 lo hi HIn o Ho. cbn [In] in HIn. apply HPX.
      destruct HIn as [E|[E|[]]]; injection E as <- <- <-; [apply PK20|apply PK10]; exact Ho. }
    { cbn [map fst]. apply NoDup_cons; [cbn [In]; intros [E|[]]; exact (DK E)|].
      apply NoDup_cons; [intros []|apply NoDup_nil]. }
    cbn [map fst] in HLf, HPf.
    assert (NIn : forall b, Mem.valid_block m b -> ~ In b [bK2; bK1]).
    { intros b Hb HIn. destruct (NF b Hb) as (? & ?). cbn [In] in HIn.
      repeat (destruct HIn as [HIn|HIn]; [symmetry in HIn; contradiction|]). exact HIn. }
    exists mf. split; [|split; [|split]].
    - eapply eval_funcall_internal with (e := e) (le1 := le0) (m1 := m0) (le2 := le') (m2 := mX) (out := Out_normal).
      + eapply co_entry; eassumption.
      + exact HX.
      + reflexivity.
      + unfold e. rewrite co_blocks. exact HFL.
    - intros ch b ofs Hb. apply HLf, NIn, Hb.
    - intros b ofs k p Hb Hp. apply HPf; [apply NIn, Hb|exact Hp].
    - exact HVf. }
  assert (HC0 : col bres ores bout oout le0) by (split; reflexivity).
  assert (Ha0 : le0!_allocation = Some (Vptr ba (Ptrofs.repr oa))) by reflexivity.
  assert (Hl0 : le0!_allocationLen = Some (Vptr bl (Ptrofs.repr ol))) by reflexivity.
  (* sources as seen from a memory that agrees with [m] off the record *)
  assert (SRC : forall m', (forall ch b ofs, Mem.valid_block m b -> b <> bres -> Mem.load ch m' b ofs = Mem.load ch m b ofs) ->
     (forall b, Mem.valid_block m b -> Mem.valid_block m' b) ->
     conf_ok m' sA dA /\ amt_ok m' sV dV /\ conf_ok m' sN dN /\
     buf_at m' bout (oout + 24) sS lenS /\ same_on bout m m').
  { intros m' HK HVV. split; [|split; [|split; [|split]]].
    - apply (conf_ok_same m m'); [|exact HcA]. destruct sA as [|b o]; cbn; [exact I|].
      intros ch ofs. apply HK; [exact (conf_ok_valid _ _ _ _ HcA)|exact NAr].
    - apply (amt_ok_same m m'); [|exact HcV]. destruct sV as [|b o]; cbn; [exact I|].
      intros ch ofs. apply HK; [exact (amt_ok_valid _ _ _ _ HcV)|exact NVr].
    - apply (conf_ok_same m m'); [|exact HcN]. destruct sN as [|b o]; cbn; [exact I|].
      intros ch ofs. apply HK; [exact (conf_ok_valid _ _ _ _ HcN)|exact NNr].
    - apply (buf_at_same m m'); [intros ch ofs; apply HK; assumption| |exact HbS].
      destruct sS as [|b o bs]; cbn; [exact I|]. destruct HbS as (_ & _ & _ & Vb & _).
      split; [intros ch ofs; apply HK; [exact Vb|exact NSr]|apply HVV].
    - intros ch ofs. apply HK; assumption. }
  assert (PRm : forall o, ores <= o < ores + 248 -> Mem.perm m bres o Cur Writable) by exact PR.
  (* 1: scriptPubKey hash *)
  assert (K0 : forall ch b ofs, Mem.valid_block m b -> b <> bres -> Mem.load ch m0 b ofs = Mem.load ch m b ofs)
    by (intros; apply XL; assumption).
  destruct (SRC m0 K0 XV) as (_ & _ & _ & HbS0 & _).
  destruct (hashbuf_any Hmodel m0 bres (ores + 180) bout (oout + 24) sS lenS) as (m1 & HX1 & R1 & FR1 & PM1 & V1);
    try assumption; try zo.
  { exact (div4_of_8 ores 180 45 HorA eq_refl). }
  { intros o Ho. apply XP, PR. zo. }
  { unfold sha_dispatch_ok. rewrite XL by exact VG. exact Hdisp. }
  { rewrite XL by exact VM. exact HMax. }
  pose proof (co_s1_exec e bres ores bout oout Hores Hoout le0 m0 m1 eq_refl HC0 HX1) as X1.
  assert (SF1 : forall ch ofs, (ofs + size_chunk ch <= ores + 180 \/ ores + 212 <= ofs) ->
     Mem.load ch m1 bres ofs = Mem.load ch m0 bres ofs).
  { intros ch ofs Hd. apply FR1; [apply XV, Vr|right; zo]. }
  assert (K1 : forall ch b ofs, Mem.valid_block m b -> b <> bres -> Mem.load ch m1 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb Nb. rewrite FR1 by (try (apply XV, Hb); left; exact Nb). apply K0; assumption. }
  assert (P1 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m1 b ofs k p).
  { intros b ofs k p Hp. apply PM1; [eapply Mem.perm_valid_block; exact Hp|exact Hp]. }
  (* 2: emptyScript *)
  destruct (SRC m1 K1 (fun b Hb => V1 b (XV b Hb))) as (_ & _ & _ & HbS1 & _).
  destruct (co_s2_exec e bres ores bout oout Hores Hoout le0 m1 lenS HC0) as (m2 & X2 & St2).
  { replace (oout + 32) with (oout + 24 + 8) by zo. exact (proj1 HbS1). }
  { apply P1, XP, PR. zo. }
  set (le2 := PTree.set _t'11 (Vint lenS) le0) in *.
  assert (SF2 : forall ch ofs, (ofs + size_chunk ch <= ores + 241 \/ ores + 242 <= ofs) ->
     Mem.load ch m2 bres ofs = Mem.load ch m1 bres ofs).
  { intros ch ofs Hd. apply (Mem.load_store_other _ _ _ _ _ _ St2). right.
    change (size_chunk Mint8unsigned) with 1. zo. }
  assert (K2 : forall ch b ofs, Mem.valid_block m b -> b <> bres -> Mem.load ch m2 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb Nb. rewrite (Mem.load_store_other _ _ _ _ _ _ St2) by (left; exact Nb). apply K1; assumption. }
  assert (P2 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m2 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact St2|apply P1, Hp]. }
  assert (V2 : forall b, Mem.valid_block m0 b -> Mem.valid_block m2 b).
  { intros b Hb. eapply Mem.store_valid_block_1; [exact St2|apply V1, Hb]. }
  assert (HC2 : col bres ores bout oout le2) by (apply col_set; [discriminate|discriminate|exact HC0]).
  (* 3: asset *)
  destruct (SRC m2 K2 (fun b Hb => V2 b (XV b Hb))) as (HcA2 & _ & _ & _ & So2).
  destruct (copyconf_any bres (ores + 0) m2 sA dA) as (m3 & HX3 & A3 & Pf3 & FR3 & PM3 & V3);
    try assumption; try zo.
  { exact (div4_of_8 ores 0 0 HorA eq_refl). }
  { intros o Ho. apply P2, XP, PR. zo. }
  set (le3 := PTree.set _t'10 (rs_val sA) le2).
  assert (X3 : Clight2.exec_stmt sha_ge e le2 m2 co_s3 E0 le3 m3 Out_normal).
  { unfold co_s3. eapply co_copy_stmt with (f := f_copyRawConfidential) (dout := 0) (dres := 0);
      [exact Hores|exact Hoout|reflexivity|exact co_sym_copyRawConfidential|exact co_fun_copyRawConfidential
      |reflexivity|discriminate|discriminate|exact HC2|exact envu_rout_asset|lia|exact envu_sout_asset|lia
      |rewrite Z.add_0_r, So2; exact HLA|exact HX3]. }
  rewrite Z.add_0_r in A3, Pf3, FR3.
  assert (SF3 : forall ch ofs, (ofs + size_chunk ch <= ores \/ ores + 36 <= ofs) ->
     Mem.load ch m3 bres ofs = Mem.load ch m2 bres ofs).
  { intros ch ofs Hd. apply FR3; [apply V2, XV, Vr|right; zo]. }
  assert (K3 : forall ch b ofs, Mem.valid_block m b -> b <> bres -> Mem.load ch m3 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb Nb. rewrite FR3 by (try (apply V2, XV, Hb); left; exact Nb). apply K2; assumption. }
  assert (P3 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m3 b ofs k p).
  { intros b ofs k p Hp. apply PM3; [apply V2; eapply Mem.perm_valid_block; exact Hp|apply P2, Hp]. }
  assert (V3' : forall b, Mem.valid_block m0 b -> Mem.valid_block m3 b) by (intros b Hb; apply V3, V2, Hb).
  assert (HC3 : col bres ores bout oout le3) by (apply col_set; [discriminate|discriminate|exact HC2]).
  (* 4: amount *)
  destruct (SRC m3 K3 (fun b Hb => V3' b (XV b Hb))) as (_ & HcV3 & _ & _ & So3).
  destruct (copyamt_any bres (ores + 104) m3 sV dV) as (m4 & HX4 & Pf4 & A4 & FR4 & PM4 & V4);
    try assumption; try zo.
  { apply Z.divide_add_r; [exact HorA|exists 13; reflexivity]. }
  { intros o Ho. apply P3, XP, PR. zo. }
  set (le4 := PTree.set _t'9 (rs_val sV) le3).
  assert (X4 : Clight2.exec_stmt sha_ge e le3 m3 co_s4 E0 le4 m4 Out_normal).
  { unfold co_s4. eapply co_copy_stmt with (f := f_copyRawAmt) (dout := 8) (dres := 104);
      [exact Hores|exact Hoout|reflexivity|exact co_sym_copyRawAmt|exact co_fun_copyRawAmt
      |reflexivity|discriminate|discriminate|exact HC3|exact envu_rout_value|lia|exact envu_sout_amt|lia
      |rewrite So3; exact HLV|exact HX4]. }
  assert (SF4 : forall ch ofs, (ofs + size_chunk ch <= ores + 104 \/ ores + 144 <= ofs) ->
     Mem.load ch m4 bres ofs = Mem.load ch m3 bres ofs).
  { intros ch ofs Hd. apply FR4. right; zo. }
  assert (K4 : forall ch b ofs, Mem.valid_block m b -> b <> bres -> Mem.load ch m4 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb Nb. rewrite FR4 by (left; exact Nb). apply K3; assumption. }
  assert (P4 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m4 b ofs k p) by (intros b ofs k p Hp; apply PM4, P3, Hp).
  assert (V4' : forall b, Mem.valid_block m0 b -> Mem.valid_block m4 b) by (intros b Hb; apply V4, V3', Hb).
  assert (HC4 : col bres ores bout oout le4) by (apply col_set; [discriminate|discriminate|exact HC3]).
  (* 5: nonce *)
  destruct (SRC m4 K4 (fun b Hb => V4' b (XV b Hb))) as (_ & _ & HcN4 & _ & So4).
  destruct (copyconf_any bres (ores + 144) m4 sN dN) as (m5 & HX5 & A5 & Pf5 & FR5 & PM5 & V5);
    try assumption; try zo.
  { exact (div4_of_8 ores 144 36 HorA eq_refl). }
  { intros o Ho. apply P4, XP, PR. zo. }
  set (le5 := PTree.set _t'8 (rs_val sN) le4).
  assert (X5 : Clight2.exec_stmt sha_ge e le4 m4 co_s5 E0 le5 m5 Out_normal).
  { unfold co_s5. eapply co_copy_stmt with (f := f_copyRawConfidential) (dout := 16) (dres := 144);
      [exact Hores|exact Hoout|reflexivity|exact co_sym_copyRawConfidential|exact co_fun_copyRawConfidential
      |reflexivity|discriminate|discriminate|exact HC4|exact envu_rout_nonce|lia|exact envu_sout_nonce|lia
      |rewrite So4; exact HLN|exact HX5]. }
  assert (SF5 : forall ch ofs, (ofs + size_chunk ch <= ores + 144 \/ ores + 180 <= ofs) ->
     Mem.load ch m5 bres ofs = Mem.load ch m4 bres ofs).
  { intros ch ofs Hd. apply FR5; [apply V4', XV, Vr|right; zo]. }
  assert (K5 : forall ch b ofs, Mem.valid_block m b -> b <> bres -> Mem.load ch m5 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb Nb. rewrite FR5 by (try (apply V4', XV, Hb); left; exact Nb). apply K4; assumption. }
  assert (P5 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m5 b ofs k p).
  { intros b ofs k p Hp. apply PM5; [apply V4'; eapply Mem.perm_valid_block; exact Hp|apply P4, Hp]. }
  assert (V5' : forall b, Mem.valid_block m0 b -> Mem.valid_block m5 b) by (intros b Hb; apply V5, V4', Hb).
  assert (HC5 : col bres ores bout oout le5) by (apply col_set; [discriminate|discriminate|exact HC4]).
  (* 6: the null-data parse *)
  destruct (SRC m5 K5 (fun b Hb => V5' b (XV b Hb))) as (_ & _ & _ & HbS5 & So5).
  destruct (buf_parse_facts _ _ _ _ _ HbS5) as (HobM & HBuf5 & HBs5).
  pose proof (buf_blk_valid _ _ _ _ _ HbS Vo) as VbS.
  destruct (eval_parseNullData Hmodel m5 bres (ores + 224) ba oa bl ol bop oop alen bout (oout + 24) lenS
              (buf_blk bout sS) (buf_ofs sS) (buf_bytes sS)) as (m6 & HX6 & HPost6 & PM6 & V6);
    try assumption; try zo.
  { apply Z.divide_add_r; [exact HorA|exists 28; reflexivity]. }
  { rewrite K5 by assumption. exact HLa. }
  { rewrite K5 by assumption. exact HLl. }
  { exact (proj1 HbS5). }
  { intros o Ho. apply P5, XP, PR. zo. }
  { intros o Ho. apply P5, XP, PO, Ho. }
  { apply V5', XV, Vop. }
  { split; [intros o Ho; apply P5, XP; exact (proj1 VAa o Ho)|exact (proj2 VAa)]. }
  { split; [intros o Ho; apply P5, XP; exact (proj1 VAl o Ho)|exact (proj2 VAl)]. }
  { unfold sha_dispatch_ok. rewrite K5 by assumption. exact Hdisp. }
  { rewrite K5 by assumption. exact HMax. }
  { left. exact Nro. }
  { apply buf_blk_other; assumption. }
  { apply buf_blk_other; assumption. }
  remember (pn_run alen lenS (buf_bytes sS)) as r eqn:Er in *.
  assert (X6 : Clight2.exec_stmt sha_ge e le5 m5 co_s6 E0 le5 m6 Out_normal).
  { apply (co_s6_exec e bres ores bout oout Hores Hoout le5 m5 m6 ba oa bl ol eq_refl HC5);
      [unfold le5, le4, le3, le2; rewrite !PTree.gso by discriminate; exact Ha0
      |unfold le5, le4, le3, le2; rewrite !PTree.gso by discriminate; exact Hl0|exact HX6]. }
  assert (H6 : co_pnd m6 bres ores ba oa bl ol bop oop alen r /\
     (forall ch b ofs, Mem.valid_block m b ->
        (b <> bres \/ ofs + size_chunk ch <= ores + 224 \/ ores + 240 <= ofs) ->
        (b <> bop \/ ofs + size_chunk ch <= oop \/ oop + 36 * alen <= ofs) ->
        (b <> ba \/ ofs + size_chunk ch <= oa \/ oa + 8 <= ofs) ->
        (b <> bl \/ ofs + size_chunk ch <= ol \/ ol + 8 <= ofs) ->
        Mem.load ch m6 b ofs = Mem.load ch m5 b ofs)).
  { revert HPost6. destruct r as [ents|]; cbn [co_pnd].
    - intros (H1 & H2 & H3 & H4 & H5 & H6 & H7). split; [exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6)))))|].
      intros ch b ofs Hb D1 D2 D3 D4. apply H7; try assumption; [apply V5', XV, Hb|].
      destruct D1 as [D|[D|D]]; [left; exact D|right; left; exact D|right; right; zo].
    - intros (H1 & H2). split; [exact H1|].
      intros ch b ofs Hb D1 D2 _ _. apply H2; try assumption; [apply V5', XV, Hb|].
      destruct D1 as [D|[D|D]]; [left; exact D|right; left; exact D|right; right; zo]. }
  destruct H6 as (PND6 & FR6).
  assert (SF6 : forall ch ofs, (ofs + size_chunk ch <= ores + 224 \/ ores + 240 <= ofs) ->
     Mem.load ch m6 bres ofs = Mem.load ch m5 bres ofs).
  { intros ch ofs Hd. apply FR6; [exact Vr|right; exact Hd|left; exact Nro
      |left; apply not_eq_sym; exact Nar|left; apply not_eq_sym; exact Nlr]. }
  (* off the record, the array and the cursor cells *)
  assert (K6 : forall ch b ofs, Mem.valid_block m b -> b <> bres ->
     (b <> bop \/ ofs + size_chunk ch <= oop \/ oop + 36 * alen <= ofs) ->
     (b <> ba \/ ofs + size_chunk ch <= oa \/ oa + 8 <= ofs) ->
     (b <> bl \/ ofs + size_chunk ch <= ol \/ ol + 8 <= ofs) ->
     Mem.load ch m6 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb Nb D2 D3 D4. rewrite FR6 by (try assumption; left; exact Nb). apply K5; assumption. }
  assert (P6 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m6 b ofs k p).
  { intros b ofs k p Hp. apply PM6; [apply V5'; eapply Mem.perm_valid_block; exact Hp|apply P5, Hp]. }
  assert (V6' : forall b, Mem.valid_block m0 b -> Mem.valid_block m6 b) by (intros b Hb; apply V6, V5', Hb).
  (* 7: isNullData *)
  assert (HL7 : Mem.load Mptr m6 bres (ores + 224) = Some (co_v7 bop oop r)).
  { unfold co_v7. revert PND6. destruct r; cbn [co_pnd]; [intros (_ & H & _); exact H|intros H; exact H]. }
  destruct (co_s7_exec e bres ores bout oout Hores le5 m6 (co_v7 bop oop r) (co_isnd r) HC5 HL7) as (m7 & X7 & St7).
  { unfold co_v7, co_isnd. destruct r; [right|left; split; reflexivity].
    exists bop, (Ptrofs.repr oop). split; [reflexivity|]. split; [reflexivity|].
    rewrite Ptrofs.unsigned_repr by zo. apply (weak_valid_keep m m6); [|exact HW].
    intros o k p Hp. apply P6, XP, Hp. }
  { apply P6, XP, PR. zo. }
  set (le7 := PTree.set _t'7 (co_v7 bop oop r) le5) in *.
  assert (SF7 : forall ch ofs, (ofs + size_chunk ch <= ores + 240 \/ ores + 241 <= ofs) ->
     Mem.load ch m7 bres ofs = Mem.load ch m6 bres ofs).
  { intros ch ofs Hd. apply (Mem.load_store_other _ _ _ _ _ _ St7). right.
    change (size_chunk Mint8unsigned) with 1. zo. }
  assert (O7 : forall ch b ofs, b <> bres -> Mem.load ch m7 b ofs = Mem.load ch m6 b ofs).
  { intros ch b ofs Nb. apply (Mem.load_store_other _ _ _ _ _ _ St7). left; exact Nb. }
  assert (P7 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m7 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact St7|apply P6, Hp]. }
  assert (V7 : forall b, Mem.valid_block m0 b -> Mem.valid_block m7 b).
  { intros b Hb. eapply Mem.store_valid_block_1; [exact St7|apply V6', Hb]. }
  assert (HC7 : col bres ores bout oout le7) by (apply col_set; [discriminate|discriminate|exact HC5]).
  (* sources of the two proofs, the SHA globals *)
  assert (SRC2 : forall m', (forall ch b ofs, Mem.valid_block m b -> b <> bres -> b <> bop -> b <> ba -> b <> bl ->
        Mem.load ch m' b ofs = Mem.load ch m b ofs) ->
     (forall b, Mem.valid_block m b -> Mem.valid_block m' b) ->
     buf_at m' bout (oout + 40) sJ lenJ /\ buf_at m' bout (oout + 56) sR lenR /\
     sha_dispatch_ok m' /\ Mem.load Mint64 m' GM 0 = Some (Vlong sha_max_counter)).
  { intros m' HK HVV. split; [|split; [|split]].
    - apply (buf_at_same m m'); [intros ch ofs; apply HK; assumption| |exact HbJ].
      destruct sJ as [|b o bs]; cbn; [exact I|]. destruct HbJ as (_ & _ & _ & Vb & _).
      split; [intros ch ofs; apply HK; [exact Vb|exact NJr|exact NJo|exact NJa|exact NJl]|apply HVV].
    - apply (buf_at_same m m'); [intros ch ofs; apply HK; assumption| |exact HbR].
      destruct sR as [|b o bs]; cbn; [exact I|]. destruct HbR as (_ & _ & _ & Vb & _).
      split; [intros ch ofs; apply HK; [exact Vb|exact NRr|exact NRo|exact NRa|exact NRl]|apply HVV].
    - unfold sha_dispatch_ok. rewrite HK by assumption. exact Hdisp.
    - rewrite HK by assumption. exact HMax. }
  assert (K7 : forall ch b ofs, Mem.valid_block m b -> b <> bres -> b <> bop -> b <> ba -> b <> bl ->
     Mem.load ch m7 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb N1 N2 N3 N4. rewrite O7 by exact N1. apply K6; try assumption; left; assumption. }
  destruct (NF bres Vr) as (Rk1 & Rk2). destruct (NF bout Vo) as (Ok1 & Ok2).
  destruct (NF GC VG) as (Gk1 & Gk2). destruct (NF GM VM) as (Mk1 & Mk2).
  assert (BK : forall s len o, buf_at m bout o s len -> buf_other s bK1 /\ buf_other s bK2).
  { intros s len o (_ & _ & H). destruct s as [|b ob bs]; cbn; [split; exact I|].
    destruct H as (_ & Vb & _). destruct (NF b Vb). split; assumption. }
  (* 8: surjection proof hash *)
  destruct (SRC2 m7 K7 (fun b Hb => V7 b (XV b Hb))) as (HbJ7 & _ & Hdisp7 & HMax7).
  assert (Pf7 : Mem.load Mint32 m7 bres (ores + 0 + 32) = Some (Vint (fst (conf_of dA)))).
  { rewrite Z.add_0_r. rewrite SF7, SF6, SF5, SF4 by (change (size_chunk Mint32) with 4; zo). exact Pf3. }
  assert (PK7 : Mem.range_perm m7 bK1 0 16 Cur Writable).
  { intros o Ho. eapply Mem.perm_implies; [apply P7, PK10, Ho|constructor]. }
  assert (PR7 : Mem.range_perm m7 bres (ores + 36) (ores + 36 + 32) Cur Writable).
  { intros o Ho. apply P7, XP, PR. zo. }
  destruct (co_proof_exec e bres ores bout oout Hores Hoout Hmodel _t'6 _t'1 _t'2 _asset _surjectionProofHash
              _surjectionProof ___compound _confidential 0 36 40 bK1 le7 m7 (fst (conf_of dA)) sJ lenJ
              eq_refl eq_refl eq_refl envu_sout_asset envu_confidential_prefix envu_sout_surjectionProofHash
              envu_rout_surjectionProof ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (div4_of_8 ores 36 9 HorA eq_refl)
              ltac:(lia) ltac:(lia) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) HC7 Pf7 HbJ7 NJr (proj1 (BK _ _ _ HbJ)) Nor Ok1
              (not_eq_sym Rk1) NGr NMr Gk1 Mk1 PK7 PR7 Hdisp7 HMax7)
    as (le8 & m8 & X8 & HC8 & R8 & FR8 & PM8 & V8).
  assert (SF8 : forall ch ofs, (ofs + size_chunk ch <= ores + 36 \/ ores + 68 <= ofs) ->
     Mem.load ch m8 bres ofs = Mem.load ch m7 bres ofs).
  { intros ch ofs Hd. apply FR8; [apply V7, XV, Vr|exact Rk1|right; zo]. }
  assert (O8 : forall ch b ofs, Mem.valid_block m b -> b <> bres -> Mem.load ch m8 b ofs = Mem.load ch m7 b ofs).
  { intros ch b ofs Hb Nb. destruct (NF b Hb). apply FR8; [apply V7, XV, Hb|assumption|left; exact Nb]. }
  assert (P8 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m8 b ofs k p).
  { intros b ofs k p Hp. apply PM8; [apply V7; eapply Mem.perm_valid_block; exact Hp|apply P7, Hp]. }
  assert (V8' : forall b, Mem.valid_block m0 b -> Mem.valid_block m8 b) by (intros b Hb; apply V8, V7, Hb).
  assert (K8 : forall ch b ofs, Mem.valid_block m b -> b <> bres -> b <> bop -> b <> ba -> b <> bl ->
     Mem.load ch m8 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb N1 N2 N3 N4. rewrite O8 by assumption. apply K7; assumption. }
  (* 9: range proof hash *)
  destruct (SRC2 m8 K8 (fun b Hb => V8' b (XV b Hb))) as (_ & HbR8 & Hdisp8 & HMax8).
  assert (Pf8 : Mem.load Mint32 m8 bres (ores + 104 + 32) = Some (Vint (amt_prefix dV))).
  { rewrite SF8, SF7, SF6, SF5 by (change (size_chunk Mint32) with 4; zo). exact Pf4. }
  assert (PK8 : Mem.range_perm m8 bK2 0 16 Cur Writable).
  { intros o Ho. eapply Mem.perm_implies; [apply P8, PK20, Ho|constructor]. }
  assert (PR8 : Mem.range_perm m8 bres (ores + 68) (ores + 68 + 32) Cur Writable).
  { intros o Ho. apply P8, XP, PR. zo. }
  destruct (co_proof_exec e bres ores bout oout Hores Hoout Hmodel _t'5 _t'3 _t'4 _amt _rangeProofHash
              _rangeProof ___compound__1 _confAmount 104 68 56 bK2 le8 m8 (amt_prefix dV) sR lenR
              eq_refl eq_refl eq_refl envu_sout_amt envu_confAmount_prefix envu_sout_rangeProofHash
              envu_rout_rangeProof ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (div4_of_8 ores 68 17 HorA eq_refl)
              ltac:(lia) ltac:(lia) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) HC8 Pf8 HbR8 NRr (proj2 (BK _ _ _ HbR)) Nor Ok2
              (not_eq_sym Rk2) NGr NMr Gk2 Mk2 PK8 PR8 Hdisp8 HMax8)
    as (le9 & m9 & X9 & HC9 & R9 & FR9 & PM9 & V9).
  assert (SF9 : forall ch ofs, (ofs + size_chunk ch <= ores + 68 \/ ores + 100 <= ofs) ->
     Mem.load ch m9 bres ofs = Mem.load ch m8 bres ofs).
  { intros ch ofs Hd. apply FR9; [apply V8', XV, Vr|exact Rk2|right; zo]. }
  assert (O9 : forall ch b ofs, Mem.valid_block m b -> b <> bres -> Mem.load ch m9 b ofs = Mem.load ch m8 b ofs).
  { intros ch b ofs Hb Nb. destruct (NF b Hb). apply FR9; [apply V8', XV, Hb|assumption|left; exact Nb]. }
  assert (P9 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m9 b ofs k p).
  { intros b ofs k p Hp. apply PM9; [apply V8'; eapply Mem.perm_valid_block; exact Hp|apply P8, Hp]. }
  assert (V9' : forall b, Mem.valid_block m0 b -> Mem.valid_block m9 b) by (intros b Hb; apply V9, V8', Hb).
  (* 10: assetFee *)
  assert (VA10 : Mem.valid_access m9 Mint64 bres (ores + 216) Writable).
  { split; [intros o Ho; apply P9, XP, PR; change (size_chunk Mint64) with 8 in Ho; zo
           |change (align_chunk Mint64) with 8; apply Z.divide_add_r; [exact HorA|exists 27; reflexivity]]. }
  destruct (Mem.valid_access_store m9 Mint64 bres (ores + 216) (Vlong Int64.zero) VA10) as [m10 St10].
  assert (X10 : Clight2.exec_stmt sha_ge e le9 m9
     (Sassign (Efield (Ederef (Etempvar _result (tptr SOUT)) SOUT) _assetFee tulong) (Econst_int (Int.repr 0) tint))
     E0 le9 m10 Out_normal).
  { eapply exec_Sassign with (v2 := Vint (Int.repr 0)) (v := Vlong Int64.zero).
    - apply (co_res_field e bres ores bout oout Hores le9 m9); [exact HC9|exact envu_sout_assetFee|lia].
    - apply eval_Econst_int.
    - reflexivity.
    - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev. rewrite Ptrofs.unsigned_repr by zo. exact St10. }
  assert (SF10 : forall ch ofs, (ofs + size_chunk ch <= ores + 216 \/ ores + 224 <= ofs) ->
     Mem.load ch m10 bres ofs = Mem.load ch m9 bres ofs).
  { intros ch ofs Hd. apply (Mem.load_store_other _ _ _ _ _ _ St10). right. change (size_chunk Mint64) with 8. zo. }
  assert (O10 : forall ch b ofs, b <> bres -> Mem.load ch m10 b ofs = Mem.load ch m9 b ofs).
  { intros ch b ofs Nb. apply (Mem.load_store_other _ _ _ _ _ _ St10). left; exact Nb. }
  assert (P10 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m10 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact St10|apply P9, Hp]. }
  destruct (FIN le9 m10) as (mf & XF & HLf & HPf & HVf).
  { rewrite copyOutput_body_shape.
    eapply pn_seq1; [exact X1|]. eapply pn_seq1; [exact X2|]. eapply pn_seq1; [exact X3|].
    eapply pn_seq1; [exact X4|]. eapply pn_seq1; [exact X5|]. eapply pn_seq1; [exact X6|].
    eapply pn_seq1; [exact X7|]. eapply pn_seq1; [rewrite co_s8_shape; exact X8|].
    rewrite co_s9_shape. eapply pn_seq1; [exact X9|exact X10]. }
  { exact P10. }
  (* other blocks, from the parse to the end *)
  assert (OE : forall ch b ofs, Mem.valid_block m b -> b <> bres -> Mem.load ch mf b ofs = Mem.load ch m6 b ofs).
  { intros ch b ofs Hb Nb. rewrite HLf by exact Hb. rewrite O10 by exact Nb.
    rewrite O9, O8 by assumption. apply O7, Nb. }
  exists mf. split; [exact XF|].
  split. { intros j Hj. rewrite HLf by exact Vr.
           rewrite SF10, SF9, SF8, SF7, SF6, SF5, SF4, SF3, SF2 by (change (size_chunk Mint32) with 4; zo).
           exact (R1 j Hj). }
  split. { rewrite HLf by exact Vr.
           rewrite SF10, SF9, SF8, SF7, SF6, SF5, SF4, SF3 by (change (size_chunk Mint8unsigned) with 1; zo).
           rewrite (Mem.load_store_same _ _ _ _ _ _ St2). destruct (Int.eq (Int.repr 0) lenS); reflexivity. }
  split. { intros j Hj. rewrite HLf by exact Vr.
           rewrite SF10, SF9, SF8, SF7, SF6, SF5, SF4 by (change (size_chunk Mint32) with 4; zo).
           exact (uint32_array_at_nth _ _ _ _ A3 (conf_of_length dA) j Hj). }
  split. { rewrite HLf by exact Vr.
           rewrite SF10, SF9, SF8, SF7, SF6, SF5, SF4 by (change (size_chunk Mint32) with 4; zo). exact Pf3. }
  split. { rewrite HLf by exact Vr.
           rewrite SF10, SF9, SF8, SF7, SF6, SF5 by (change (size_chunk Mint32) with 4; zo). exact Pf4. }
  split. { apply (amt_at_same m4 mf); [|exact A4]. intros ch ofs H1 H2. rewrite HLf by exact Vr.
           rewrite SF10, SF9, SF8, SF7, SF6, SF5 by zo. reflexivity. }
  split. { intros j Hj. rewrite HLf by exact Vr.
           rewrite SF10, SF9, SF8, SF7, SF6 by (change (size_chunk Mint32) with 4; zo).
           exact (uint32_array_at_nth _ _ _ _ A5 (conf_of_length dN) j Hj). }
  split. { rewrite HLf by exact Vr.
           rewrite SF10, SF9, SF8, SF7, SF6 by (change (size_chunk Mint32) with 4; zo). exact Pf5. }
  split. { apply (co_pnd_same m6 mf); [|intros ch ofs; apply OE; [exact Vop|apply not_eq_sym; exact Nro]
             |intros ch ofs; apply OE; assumption|intros ch ofs; apply OE; assumption|exact PND6].
           intros ch ofs H1 H2. rewrite HLf by exact Vr. rewrite SF10, SF9, SF8, SF7 by zo. reflexivity. }
  split. { rewrite HLf by exact Vr.
           rewrite SF10, SF9, SF8 by (change (size_chunk Mint8unsigned) with 1; zo).
           rewrite (Mem.load_store_same _ _ _ _ _ _ St7). destruct (co_isnd r); reflexivity. }
  split. { intros j Hj. rewrite HLf by exact Vr.
           rewrite SF10, SF9 by (change (size_chunk Mint32) with 4; zo). exact (R8 j Hj). }
  split. { intros j Hj. rewrite HLf by exact Vr.
           rewrite SF10 by (change (size_chunk Mint32) with 4; zo). exact (R9 j Hj). }
  split. { rewrite HLf by exact Vr. rewrite (Mem.load_store_same _ _ _ _ _ _ St10). reflexivity. }
  split; [|split].
  - intros ch b ofs Hb D1 D2 D3 D4. destruct (eq_block b bres) as [->|Nb].
    + rewrite HLf by exact Vr.
      assert (Hout : ofs + size_chunk ch <= ores \/ ores + 248 <= ofs)
        by (destruct D1 as [D|D]; [exfalso; apply D; reflexivity|exact D]).
      rewrite SF10, SF9, SF8, SF7, SF6, SF5, SF4, SF3, SF2, SF1 by zo. apply XL, Vr.
    + rewrite OE by assumption. apply K6; assumption.
  - intros b ofs k p Hb Hp. apply HPf; [exact Hb|apply P10, XP, Hp].
  - intros b Hb. apply HVf. eapply Mem.store_valid_block_1; [exact St10|]. apply V9', XV, Hb.
Qed.
