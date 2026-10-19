(** [simplicity_bitcoin_mallocTapEnv] (bitcoin/env.c), complete: for a
    readable raw taproot environment with [pathLen <= 128] the call returns a
    fresh block holding the leaf version, the internal key, the script CMR,
    the path, and the three cached hashes [tapLeafHash], [tappathHash] and
    [tapEnvHash] computed by the actual C code; memory that existed before
    the call is unchanged.

    Input requirements (premises): the raw structure and the data it points
    to are readable; the path length is at most 128; the SHA dispatch
    pointer, the maximum counter and the "TapLeaf" tag array hold their
    initial values (the start-up invariant).  Conditional on [memcpy_model].
    CompCert's [malloc] never fails, so the NULL-return path after it is not
    covered. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init C.jet_sha256_iv_init.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_bitmachine_rep.
Require Import C.jet_sha_compress_call C.jet_sha_add_n_init C.jet_sha_be32_exec C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_write C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_sha_add_n_calls.
Require Import C.jet_sha_tapdata_prep C.jet_sha_ctx_abs C.jet_sha_tagged_ctx.
Require Import C.jet_bitcoin_make_tapleaf_exec.
Require Import C.jet_env_store_words C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_ctxo.
Require Import C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_key C.jet_bitcoin_env_tapenv_fill.
Require Import C.jet_bitcoin_env_tapenv_cmr C.jet_bitcoin_env_tapenv_loop C.jet_bitcoin_env_tapenv_path.
Require Import C.jet_bitcoin_env_tapenv_tail.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 600.

Definition te_env (bK bCmp bC bC1 bR bR1 bR2 : block) : env :=
  PTree.set __res__2 (bR2, CTX) (PTree.set __res__1 (bR1, MID) (PTree.set __res (bR, CTX)
    (PTree.set _ctx__1 (bC1, CTX) (PTree.set _ctx (bC, CTX) (PTree.set ___compound (bCmp, TE)
      (PTree.set _internalKey (bK, MID) empty_env)))))).

Section Blocks.
Variables (bK bCmp bC bC1 bR bR1 bR2 : block).
Definition te_block_list : list (block * Z * Z) :=
  ltac:(let r := eval vm_compute in (blocks_of_env sha_ge (te_env bK bCmp bC bC1 bR bR1 bR2)) in exact r).
Lemma te_blocks : blocks_of_env sha_ge (te_env bK bCmp bC bC1 bR bR1 bR2) = te_block_list.
Proof. vm_compute. reflexivity. Qed.
End Blocks.

Lemma te_entry m m1 m2 m3 m4 m5 m6 m7 bK bCmp bC bC1 bR bR1 bR2 vraw :
  Mem.alloc m 0 32 = (m1, bK) -> Mem.alloc m1 0 176 = (m2, bCmp) -> Mem.alloc m2 0 88 = (m3, bC) ->
  Mem.alloc m3 0 88 = (m4, bC1) -> Mem.alloc m4 0 88 = (m5, bR) -> Mem.alloc m5 0 32 = (m6, bR1) ->
  Mem.alloc m6 0 88 = (m7, bR2) ->
  function_entry2 sha_ge f_simplicity_bitcoin_mallocTapEnv [vraw] m
    (te_env bK bCmp bC bC1 bR bR1 bR2)
    (PTree.set _rawEnv vraw (create_undef_temps (fn_temps f_simplicity_bitcoin_mallocTapEnv))) m7.
Proof.
  intros A1 A2 A3 A4 A5 A6 A7. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst; try contradiction; discriminate.
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bK); [rewrite te_sizeof_MID_Z; exact A1|].
    eapply alloc_variables_cons with (m1 := m2) (b1 := bCmp); [rewrite te_sizeof_TE_Z; exact A2|].
    eapply alloc_variables_cons with (m1 := m3) (b1 := bC); [change (Mem.alloc m2 0 88 = (m3, bC)); exact A3|].
    eapply alloc_variables_cons with (m1 := m4) (b1 := bC1); [change (Mem.alloc m3 0 88 = (m4, bC1)); exact A4|].
    eapply alloc_variables_cons with (m1 := m5) (b1 := bR); [change (Mem.alloc m4 0 88 = (m5, bR)); exact A5|].
    eapply alloc_variables_cons with (m1 := m6) (b1 := bR1); [rewrite te_sizeof_MID_Z; exact A6|].
    eapply alloc_variables_cons with (m1 := m7) (b1 := bR2); [change (Mem.alloc m6 0 88 = (m7, bR2)); exact A7|].
    constructor.
  - reflexivity.
Qed.

Local Opaque sha_ge.

(** What the allocated taproot environment holds. *)
Definition tapenv_built (m : mem) (bA : block) (nb cb0 : int) (kb cmrb : list int) (pb : nat -> list int) : Prop :=
  let N := Int.unsigned nb in
  let Nn := Z.to_nat N in
  let v := Int.and cb0 (Int.repr 254) in
  let kw := tm_words kb in
  let cw := tm_words cmrb in
  let L := make_tapleaf_regs v cw in
  let P := te_tappath_regs pb Nn in
  Mem.load Mptr m bA 0 = Some (te_path_value N bA) /\
  (forall j, (j < 8)%nat -> Mem.load Mint32 m bA (8 + 4 * Z.of_nat j) = Some (Vint (nth j L Int.zero))) /\
  (forall j, (j < 8)%nat -> Mem.load Mint32 m bA (40 + 4 * Z.of_nat j) = Some (Vint (nth j P Int.zero))) /\
  (forall j, (j < 8)%nat ->
     Mem.load Mint32 m bA (72 + 4 * Z.of_nat j) = Some (Vint (nth j (te_tapenv_regs L P kw) Int.zero))) /\
  (forall j, (j < 8)%nat -> Mem.load Mint32 m bA (104 + 4 * Z.of_nat j) = Some (Vint (nth j kw Int.zero))) /\
  (forall j, (j < 8)%nat -> Mem.load Mint32 m bA (136 + 4 * Z.of_nat j) = Some (Vint (nth j cw Int.zero))) /\
  Mem.load Mint8unsigned m bA 168 = Some (Vint nb) /\
  Mem.load Mint8unsigned m bA 169 = Some (Vint v) /\
  (forall j i, (j < Nn)%nat -> (i < 8)%nat ->
     Mem.load Mint32 m bA (176 + 32 * Z.of_nat j + 4 * Z.of_nat i) =
       Some (Vint (nth i (tm_words (pb j)) Int.zero))).

Ltac sepb := first [assumption | ne | (apply not_eq_sym; ne) | congruence].

Theorem eval_mallocTapEnv (Hmodel : memcpy_model) m braw oraw bcb ocb bcm ocm
    (nb cb0 : int) (kb cmrb : list int) (pb : nat -> list int) :
  0 <= oraw /\ oraw + 24 <= Ptrofs.max_unsigned ->
  0 <= Int.unsigned nb <= 128 ->
  Mem.load Mptr m braw oraw = Some (Vptr bcb ocb) ->
  Mem.load Mptr m braw (oraw + 8) = Some (Vptr bcm ocm) ->
  Mem.load Mint8unsigned m braw (oraw + 16) = Some (Vint nb) ->
  Ptrofs.unsigned ocb + 33 + 32 * Int.unsigned nb <= Ptrofs.max_unsigned ->
  Mem.load Mint8unsigned m bcb (Ptrofs.unsigned ocb) = Some (Vint cb0) ->
  (forall i, (i < 32)%nat ->
     Mem.load Mint8unsigned m bcb (Ptrofs.unsigned ocb + 1 + Z.of_nat i) = Some (Vint (nth i kb Int.zero))) ->
  (forall j i, (j < Z.to_nat (Int.unsigned nb))%nat -> (i < 32)%nat ->
     Mem.load Mint8unsigned m bcb (Ptrofs.unsigned ocb + 33 + 32 * Z.of_nat j + Z.of_nat i) =
       Some (Vint (nth i (pb j) Int.zero))) ->
  Ptrofs.unsigned ocm + 32 <= Ptrofs.max_unsigned ->
  (forall i, (i < 32)%nat ->
     Mem.load Mint8unsigned m bcm (Ptrofs.unsigned ocm + Z.of_nat i) = Some (Vint (nth i cmrb Int.zero))) ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  sha_tapleaf_tag_ok m ->
  exists m' bA,
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_bitcoin_mallocTapEnv)
      [Vptr braw (Ptrofs.repr oraw)] E0 m' (Vptr bA Ptrofs.zero) /\
    ~ Mem.valid_block m bA /\
    tapenv_built m' bA nb cb0 kb cmrb pb /\
    (forall ch b ofs, Mem.valid_block m b -> Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b) /\
    Mem.load Mptr m' bA (-8) = Some (Vlong (Int64.repr (176 + 32 * Int.unsigned nb))) /\
    Mem.range_perm m' bA (-8) (176 + 32 * Int.unsigned nb) Cur Freeable.
Proof.
  intros Horaw HN HCb HCm HLen Hocb HCb0 HKb HPb Hocm HCmB Hdisp HMax HTag.
  set (N := Int.unsigned nb) in *. set (Nn := Z.to_nat N) in *.
  set (v := Int.and cb0 (Int.repr 254)).
  set (kw := tm_words kb). set (cw := tm_words cmrb).
  set (TAG := sha_symbol_block _tagName__1) in *.
  assert (VG : Mem.valid_block m GC) by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m GM) by (eapply load_valid_block; exact HMax).
  assert (VT : Mem.valid_block m TAG) by (eapply load_valid_block; exact (HTag 0%nat ltac:(lia))).
  assert (Vraw : Mem.valid_block m braw) by (eapply load_valid_block; exact HCb).
  assert (Vcb : Mem.valid_block m bcb) by (eapply load_valid_block; exact HCb0).
  assert (Vcm : Mem.valid_block m bcm) by (eapply load_valid_block; exact (HCmB 0%nat ltac:(lia))).
  destruct (Mem.alloc m 0 32) as [ma1 bK] eqn:A1.
  destruct (Mem.alloc ma1 0 176) as [ma2 bCmp] eqn:A2.
  destruct (Mem.alloc ma2 0 88) as [ma3 bC] eqn:A3.
  destruct (Mem.alloc ma3 0 88) as [ma4 bC1] eqn:A4.
  destruct (Mem.alloc ma4 0 88) as [ma5 bR] eqn:A5.
  destruct (Mem.alloc ma5 0 32) as [ma6 bR1] eqn:A6.
  destruct (Mem.alloc ma6 0 88) as [m0 bR2] eqn:A7.
  assert (HAL : alloc_list m [32; 176; 88; 88; 88; 32; 88] = (m0, [bK; bCmp; bC; bC1; bR; bR1; bR2])).
  { cbn [alloc_list]. rewrite A1, A2, A3, A4, A5, A6, A7. reflexivity. }
  destruct (alloc_list_props _ _ _ _ HAL) as ((XV & XL & XP & XA) & FRh & ND & FA).
  inversion FA as [|? ? ? ? [PK0 VK0] FA1]; subst.
  inversion FA1 as [|? ? ? ? [PCmp0 VCmp0] FA2]; subst.
  inversion FA2 as [|? ? ? ? [PC0 VC0] FA3]; subst.
  inversion FA3 as [|? ? ? ? [PC10 VC10] FA4]; subst.
  inversion FA4 as [|? ? ? ? [PR0 VR0] FA5]; subst.
  inversion FA5 as [|? ? ? ? [PR10 VR10] FA6]; subst.
  inversion FA6 as [|? ? ? ? [PR20 VR20] FA7]; subst. clear FA FA1 FA2 FA3 FA4 FA5 FA6 FA7 HAL.
  apply NoDup_cons_iff in ND. destruct ND as [ND1 ND].
  apply NoDup_cons_iff in ND. destruct ND as [ND2 ND].
  apply NoDup_cons_iff in ND. destruct ND as [ND3 ND].
  apply NoDup_cons_iff in ND. destruct ND as [ND4 ND].
  apply NoDup_cons_iff in ND. destruct ND as [ND5 ND].
  apply NoDup_cons_iff in ND. destruct ND as [ND6 _].
  assert (Fresh : forall b, Mem.valid_block m b -> ~ In b [bK; bCmp; bC; bC1; bR; bR1; bR2]) by exact FRh.
  pose proof (Fresh GC VG) as FG. pose proof (Fresh GM VM) as FM. pose proof (Fresh TAG VT) as FT.
  pose proof (Fresh braw Vraw) as Fraw. pose proof (Fresh bcb Vcb) as Fcb. pose proof (Fresh bcm Vcm) as Fcm.
  set (e := te_env bK bCmp bC bC1 bR bR1 bR2).
  (* 1: guards, sizes, malloc *)
  assert (HLen0 : Mem.load Mint8unsigned m0 braw (oraw + 16) = Some (Vint nb)) by (rewrite XL by exact Vraw; exact HLen).
  assert (HWeak : Mem.weak_valid_pointer m0 braw (Ptrofs.unsigned (Ptrofs.repr oraw)) = true).
  { rewrite Ptrofs.unsigned_repr by lia. unfold Mem.weak_valid_pointer. apply orb_true_iff. left.
    apply Mem.valid_pointer_nonempty_perm.
    assert (HL0 : Mem.load Mptr m0 braw oraw = Some (Vptr bcb ocb)) by (rewrite XL by exact Vraw; exact HCb).
    apply Mem.load_valid_access in HL0. destruct HL0 as [HR _].
    eapply Mem.perm_implies; [apply HR; change (size_chunk Mptr) with 8; lia|constructor]. }
  destruct (te_prelude e braw oraw nb eq_refl Horaw HN m0 HLen0 HWeak)
    as (m1 & m2 & bA & le1 & HA & HS & Hle1 & K1).
  fold N in HA, HS, Hle1.
  assert (NAfresh : ~ Mem.valid_block m0 bA) by (eapply Mem.fresh_block_alloc; exact HA).
  assert (NAold : forall b, Mem.valid_block m0 b -> b <> bA) by (intros b Hb E; apply NAfresh; rewrite <- E; exact Hb).
  assert (NAl : ~ In bA [bK; bCmp; bC; bC1; bR; bR1; bR2]).
  { intros HIn. cbn [In] in HIn.
    destruct HIn as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; apply NAfresh; rewrite <- E; assumption. }
  assert (NGA : GC <> bA) by (apply NAold, XV, VG).
  assert (NMA : GM <> bA) by (apply NAold, XV, VM).
  assert (NrA : braw <> bA) by (apply NAold, XV, Vraw).
  assert (NcA : bcb <> bA) by (apply NAold, XV, Vcb).
  assert (NmA : bcm <> bA) by (apply NAold, XV, Vcm).
  assert (L2 : forall ch b ofs, Mem.valid_block m0 b -> Mem.load ch m2 b ofs = Mem.load ch m0 b ofs).
  { intros ch b ofs Hb. rewrite (Mem.load_store_other _ _ _ _ _ _ HS) by (left; apply NAold, Hb).
    eapply Mem.load_alloc_unchanged; [exact HA|exact Hb]. }
  assert (P2 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m2 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact HS|]. eapply Mem.perm_alloc_1; [exact HA|exact Hp]. }
  assert (V2 : forall b, Mem.valid_block m0 b -> Mem.valid_block m2 b).
  { intros b Hb. eapply Mem.store_valid_block_1; [exact HS|]. eapply Mem.valid_block_alloc; [exact HA|exact Hb]. }
  assert (PH2 : Mem.range_perm m2 bA (-8) (176 + 32 * N) Cur Freeable).
  { intros o Ho. eapply Mem.perm_store_1; [exact HS|]. eapply Mem.perm_alloc_2; [exact HA|exact Ho]. }
  assert (PA2 : Mem.range_perm m2 bA 0 (176 + 32 * N) Cur Freeable).
  { intros o Ho. apply PH2. lia. }
  assert (HH2 : Mem.load Mptr m2 bA (-8) = Some (Vlong (Int64.repr (176 + 32 * N)))).
  { rewrite (Mem.load_store_same _ _ _ _ _ _ HS). reflexivity. }
  assert (VA2 : Mem.valid_block m2 bA).
  { eapply Mem.store_valid_block_1; [exact HS|]. eapply Mem.valid_new_block; exact HA. }
  assert (Kold2 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m2 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite L2 by (apply XV, Hb). apply XL, Hb. }
  (* 2: the internal key *)
  destruct (te_key e braw oraw nb bA bK bcb ocb kb eq_refl eq_refl Horaw HN ltac:(sepb)
    ltac:(unfold N in *; lia) le1 m2 Hle1)
    as (m3 & le2 & HSt3 & Hle2 & K2).
  { rewrite Kold2 by exact Vraw. exact HCb. }
  { rewrite Kold2 by exact Vraw. exact HLen. }
  { sepb. }
  { intros i Hi. rewrite Kold2 by exact Vcb. apply HKb, Hi. }
  { intros o Ho. eapply Mem.perm_implies; [apply P2, PK0, Ho|constructor]. }
  fold N in Hle2.
  assert (L3 : forall ch b ofs, b <> bK -> Mem.load ch m3 b ofs = Mem.load ch m2 b ofs).
  { intros ch b ofs Hb. apply (store_words_load_other _ _ _ _ _ HSt3). left. exact Hb. }
  assert (P3 : forall b ofs k p, Mem.perm m2 b ofs k p -> Mem.perm m3 b ofs k p).
  { intros b ofs k p Hp. apply (store_words_perm _ _ _ _ _ HSt3). exact Hp. }
  assert (V3 : forall b, Mem.valid_block m2 b -> Mem.valid_block m3 b).
  { intros b Hb. unfold Mem.valid_block. rewrite (store_words_nextblock _ _ _ _ _ HSt3). exact Hb. }
  assert (HKw3 : forall j, (j < 8)%nat -> Mem.load Mint32 m3 bK (4 * Z.of_nat j) = Some (Vint (nth j kw Int.zero))).
  { intros j Hj. apply (u32_nth m3 bK 0 kw); [eapply store_words_loads; exact HSt3|exact Hj]. }
  assert (Kold3 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m3 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. pose proof (Fresh b Hb) as Fb. rewrite L3 by sepb. apply Kold2, Hb. }
  (* 3: the compound literal *)
  destruct (te_fill e bCmp bK bA braw bcb oraw ocb nb cb0 kw eq_refl eq_refl Horaw
    ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) le2 m3 Hle2)
    as (m4 & le3 & (F1 & F2 & F3 & F4) & Hle3 & L4 & P4 & V4 & K3).
  { rewrite Kold3 by exact Vraw. exact HCb. }
  { rewrite Kold3 by exact Vraw. exact HLen. }
  { rewrite Kold3 by exact Vcb. exact HCb0. }
  { exact HKw3. }
  { intros o Ho. eapply Mem.perm_implies; [apply P3, P2, PK0, Ho|constructor]. }
  { intros o Ho. eapply Mem.perm_implies; [apply P3, P2, PCmp0, Ho|constructor]. }
  { intros o Ho. eapply Mem.perm_implies; [apply P3, PA2; lia|constructor]. }
  fold N in Hle3, F1.
  assert (Kold4 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m4 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. pose proof (Fresh b Hb) as Fb.
    rewrite L4; [apply Kold3, Hb|sepb|left; apply NAold, XV, Hb]. }
  (* 4: the script CMR *)
  destruct (te_cmr e braw oraw bA bcm ocm cmrb N eq_refl Horaw ltac:(sepb) Hocm le3 m4 Hle3)
    as (m5 & le4 & HSt5 & Hle4 & K4).
  { rewrite Kold4 by exact Vraw. exact HCm. }
  { intros i Hi. rewrite Kold4 by exact Vcm. apply HCmB, Hi. }
  { intros o Ho. eapply Mem.perm_implies; [apply P4, P3, PA2; lia|constructor]. }
  assert (L5 : forall ch b ofs, (b <> bA \/ ofs + size_chunk ch <= 136 \/ 168 <= ofs) ->
    Mem.load ch m5 b ofs = Mem.load ch m4 b ofs).
  { intros ch b ofs Hc. apply (store_words_load_other _ _ _ _ _ HSt5).
    destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc|right; left; exact Hc|right; right; exact Hc]. }
  assert (P5 : forall b ofs k p, Mem.perm m4 b ofs k p -> Mem.perm m5 b ofs k p).
  { intros b ofs k p Hp. apply (store_words_perm _ _ _ _ _ HSt5). exact Hp. }
  assert (V5 : forall b, Mem.valid_block m4 b -> Mem.valid_block m5 b).
  { intros b Hb. unfold Mem.valid_block. rewrite (store_words_nextblock _ _ _ _ _ HSt5). exact Hb. }
  assert (HCw5 : forall j, (j < 8)%nat -> Mem.load Mint32 m5 bA (136 + 4 * Z.of_nat j) = Some (Vint (nth j cw Int.zero))).
  { intros j Hj. apply (u32_nth m5 bA 136 cw); [eapply store_words_loads; exact HSt5|exact Hj]. }
  assert (Vold5 : forall b, Mem.valid_block m b -> Mem.valid_block m5 b).
  { intros b Hb. apply V5, V4, V3, V2, XV, Hb. }
  assert (Kold5 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m5 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite L5 by (left; apply NAold, XV, Hb). apply Kold4, Hb. }
  assert (Pall5 : forall b ofs k p, Mem.perm m2 b ofs k p -> Mem.perm m5 b ofs k p).
  { intros b ofs k p Hp. apply P5, P4, P3, Hp. }
  (* 5: the tap-path hash *)
  destruct (te_path Hmodel e bC bR2 bA braw bcb oraw ocb nb pb eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb)
    ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) Horaw HN le4 m5 Hle4)
    as (m6 & le5 & HTp & HPathW & L6 & P6 & V6 & Hle5 & K5).
  { rewrite Kold5 by exact Vraw. exact HCb. }
  { exact Hocb. }
  { intros j i Hj Hi. rewrite Kold5 by exact Vcb. apply HPb; assumption. }
  { rewrite L5 by (right; right; lia). exact F3. }
  { apply Vold5, Vcb. }
  { intros o Ho. eapply Mem.perm_implies; [apply Pall5, PA2, Ho|constructor]. }
  { intros o Ho. apply Pall5, P2, PC0, Ho. }
  { intros o Ho. apply Pall5, P2, PR20, Ho. }
  { unfold sha_dispatch_ok. rewrite Kold5 by exact VG. exact Hdisp. }
  { rewrite Kold5 by exact VM. exact HMax. }
  fold N in Hle5. fold Nn in HTp, HPathW.
  assert (Kold6 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m6 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. pose proof (Fresh b Hb) as Fb.
    rewrite L6; [apply Kold5, Hb|apply Vold5, Hb|sepb|sepb|left; apply NAold, XV, Hb]. }
  assert (LA6 : forall ch ofs, (ofs + size_chunk ch <= 40 \/ (72 <= ofs /\ ofs + size_chunk ch <= 176)) ->
    Mem.load ch m6 bA ofs = Mem.load ch m5 bA ofs).
  { intros ch ofs Hc. apply L6; [apply V5, V4, V3, VA2|sepb|sepb|right; exact Hc]. }
  (* 6: the leaf hash, the environment hash, return *)
  destruct (te_tail Hmodel e bC1 bR bR1 bA braw oraw N v cw (te_tappath_regs pb Nn) kw
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb)
    ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) ltac:(sepb) (zero_ext8_and254 cb0) eq_refl le5 m6 Hle5)
    as (m7 & le' & HExec & HLeaf & HEnvH & L7 & P7 & V7).
  { rewrite LA6 by (right; cbn; lia). rewrite L5 by (right; right; lia). exact F4. }
  { intros j Hj. rewrite LA6 by (right; change (size_chunk Mint32) with 4; lia). apply HCw5, Hj. }
  { exact HTp. }
  { intros j Hj. rewrite LA6 by (right; change (size_chunk Mint32) with 4; lia).
    rewrite L5 by (right; left; change (size_chunk Mint32) with 4; lia). apply F2, Hj. }
  { intros o Ho. eapply Mem.perm_implies; [apply P6, Pall5, PA2; lia|constructor]. }
  { intros o Ho. apply P6, Pall5, P2, PR10, Ho. }
  { intros o Ho. apply P6, Pall5, P2, PC10, Ho. }
  { intros o Ho. apply P6, Pall5, P2, PR0, Ho. }
  { unfold sha_dispatch_ok. rewrite Kold6 by exact VG. exact Hdisp. }
  { rewrite Kold6 by exact VM. exact HMax. }
  { intros i Hi. rewrite Kold6 by exact VT. apply HTag, Hi. }
  assert (VA6 : Mem.valid_block m6 bA) by (apply V6, V5, V4, V3, VA2).
  assert (LA7 : forall ch ofs,
    (ofs + size_chunk ch <= 8 \/ (40 <= ofs /\ ofs + size_chunk ch <= 72) \/ 104 <= ofs) ->
    Mem.load ch m7 bA ofs = Mem.load ch m6 bA ofs).
  { intros ch ofs Hc. apply L7; [exact VA6|sepb|sepb|sepb|right; exact Hc]. }
  assert (Kold7 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m7 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. pose proof (Fresh b Hb) as Fb.
    rewrite L7; [apply Kold6, Hb|apply V6, Vold5, Hb|sepb|sepb|sepb|left; apply NAold, XV, Hb]. }
  assert (Pall7 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m7 b ofs k p).
  { intros b ofs k p Hp. apply P7, P6, Pall5, P2, Hp. }
  (* freeing the locals *)
  destruct (free_list_blocks (te_block_list bK bCmp bC bC1 bR bR1 bR2) m7) as (mf & HFL & HLf & HPf & HVf).
  { intros b lo hi HIn ofs Hr. apply Pall7. cbn [te_block_list In] in HIn.
    repeat (destruct HIn as [E|HIn]; [injection E as <- <- <-;
      first [apply PK0|apply PCmp0|apply PC0|apply PC10|apply PR0|apply PR10|apply PR20]; exact Hr|]).
    contradiction. }
  { cbn [te_block_list map fst].
    repeat (apply NoDup_cons;
      [let HIn := fresh in intro HIn; cbn [In] in HIn;
       repeat (destruct HIn as [HIn|HIn]; [revert HIn; sepb|]); exact HIn|]).
    apply NoDup_nil. }
  cbn [te_block_list map fst] in HLf, HPf.
  exists mf, bA.
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - eapply eval_funcall_internal with (e := e) (m1 := m0) (m2 := m7)
      (out := Out_return (Some (Vptr bA Ptrofs.zero, tptr TE))).
    + eapply te_entry; eassumption.
    + apply K1, K2, K3, K4, K5. exact HExec.
    + cbn. split; [discriminate|reflexivity].
    + unfold e. rewrite te_blocks. exact HFL.
  - intros Hv. apply NAfresh, XV, Hv.
  - assert (LAf : forall ch ofs, Mem.load ch mf bA ofs = Mem.load ch m7 bA ofs).
    { intros ch ofs. apply HLf. intros HIn. apply NAl. cbn [In] in HIn |- *. tauto. }
    unfold tapenv_built. fold N. fold Nn. fold v. fold kw. fold cw.
    split.
    { rewrite LAf, LA7 by (left; cbn; lia). rewrite LA6 by (left; cbn; lia).
      rewrite L5 by (right; left; cbn; lia). exact F1. }
    split; [intros j Hj; rewrite LAf; apply HLeaf, Hj|].
    split.
    { intros j Hj. rewrite LAf, LA7 by (right; left; change (size_chunk Mint32) with 4; lia). apply HTp, Hj. }
    split; [intros j Hj; rewrite LAf; apply HEnvH, Hj|].
    split.
    { intros j Hj. rewrite LAf, LA7 by (right; right; lia).
      rewrite LA6 by (right; change (size_chunk Mint32) with 4; lia).
      rewrite L5 by (right; left; change (size_chunk Mint32) with 4; lia). apply F2, Hj. }
    split.
    { intros j Hj. rewrite LAf, LA7 by (right; right; lia).
      rewrite LA6 by (right; change (size_chunk Mint32) with 4; lia). apply HCw5, Hj. }
    split.
    { rewrite LAf, LA7 by (right; right; lia). rewrite LA6 by (right; cbn; lia).
      rewrite L5 by (right; right; lia). exact F3. }
    split.
    { rewrite LAf, LA7 by (right; right; lia). rewrite LA6 by (right; cbn; lia).
      rewrite L5 by (right; right; lia). exact F4. }
    intros j i Hj Hi. rewrite LAf, LA7 by (right; right; lia). apply HPathW; assumption.
  - intros ch b ofs Hb. rewrite HLf; [apply Kold7, Hb|].
    intros HIn. apply (Fresh b Hb). cbn [In] in HIn |- *. tauto.
  - intros b ofs k p Hp. apply HPf; [|apply Pall7, XP, Hp].
    intros HIn. apply (Fresh b (Mem.perm_valid_block _ _ _ _ _ Hp)). cbn [In] in HIn |- *. tauto.
  - intros b Hb. apply HVf, V7, V6, Vold5, Hb.
  - rewrite HLf by (intros HIn; apply NAl; cbn [In] in HIn |- *; tauto).
    rewrite LA7 by (left; cbn; lia). rewrite LA6 by (left; cbn; lia).
    rewrite L5 by (right; left; cbn; lia).
    rewrite L4; [|sepb|right; left; cbn; lia]. rewrite L3 by sepb. exact HH2.
  - intros o Ho. apply HPf; [intros HIn; apply NAl; cbn [In] in HIn |- *; tauto|].
    apply P7, P6, Pall5, PH2, Ho.
Qed.
