(** [simplicity_bitcoin_mallocTransaction] (bitcoin/env.c), complete: for a
    readable raw transaction the call returns a fresh block holding the
    transaction structure -- the copied inputs and outputs, the totals,
    [isFinal], and the thirteen cached SHA-256 states computed by the actual
    C code -- and memory that existed before the call is unchanged.

    Input requirements (premises): the raw structure, its input and output
    arrays and the buffers they point to are readable and lie inside the
    address space; the SHA dispatch pointer and the maximum counter hold
    their initial values (the start-up invariant).  The array pointers are
    only required for non-empty arrays.  Conditional on [memcpy_model].
    CompCert's [malloc] never fails, so the NULL-return path after it is not
    covered. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_init C.jet_sha_ctx8_model.
Require Import C.jet_sha_compress_call C.jet_sha_add_n_calls C.jet_sha_tapdata_prep.
Require Import C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_uchars_prep C.jet_sha_uchars_exec.
Require Import C.jet_sha_finalize_exec C.jet_sha_ctx_abs.
Require Import C.jet_env_store_words C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_hashbuffer.
Require Import C.jet_bitcoin_env_ctxo C.jet_bitcoin_env_ctxs C.jet_bitcoin_env_ctxs_ops C.jet_bitcoin_env_ctxs_calls.
Require Import C.jet_bitcoin_env_ctxs_core C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_tail.
Require Import C.jet_bitcoin_env_copyoutput C.jet_bitcoin_env_copyinput_fill C.jet_bitcoin_env_copyinput.
Require Import C.jet_bitcoin_env_tx_prelude C.jet_bitcoin_env_tx_fill C.jet_bitcoin_env_tx_init.
Require Import C.jet_bitcoin_env_tx_txid C.jet_bitcoin_env_tx_inblock C.jet_bitcoin_env_tx_txhash.
Require Import C.jet_bitcoin_env_tx_calls C.jet_bitcoin_env_tx_outdefs C.jet_bitcoin_env_tx_outloop C.jet_bitcoin_env_tx_outblock.
Require Import C.jet_bitcoin_env_tx_indefs C.jet_bitcoin_env_tx_inops C.jet_bitcoin_env_tx_inloop C.jet_bitcoin_env_tx_inexec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Definition mt_vars : list (ident * type) := fn_vars f_simplicity_bitcoin_mallocTransaction.
Definition mt_env (bs : list block) : env :=
  fold_left (fun (e : env) xb => PTree.set (fst (fst xb)) (snd xb, snd (fst xb)) e) (combine mt_vars bs) empty_env.

Lemma mt_var_sizes : map (fun v : ident * type => sizeof sha_ge (snd v)) mt_vars = 488 :: repeat 88 24.
Proof. vm_compute; reflexivity. Qed.

Lemma alloc_vars_list (ge : genv) : forall (vars : list (ident * type)) (e : env) m m' bs,
  alloc_list m (map (fun v : ident * type => sizeof ge (snd v)) vars) = (m', bs) ->
  alloc_variables ge e m vars
    (fold_left (fun (e : env) xb => PTree.set (fst (fst xb)) (snd xb, snd (fst xb)) e) (combine vars bs) e) m'.
Proof.
  induction vars as [|[id ty] vars IH]; intros e m m' bs H; cbn [alloc_list map] in H.
  - injection H as <- <-. cbn. constructor.
  - cbn [snd] in H. destruct (Mem.alloc m 0 (sizeof ge ty)) as [m1 b] eqn:A.
    destruct (alloc_list m1 (map (fun v : ident * type => sizeof ge (snd v)) vars)) as [m2 bs'] eqn:R.
    injection H as <- <-. cbn [combine fold_left fst snd].
    eapply alloc_variables_cons; [exact A|]. apply IH. exact R.
Qed.

Section Blocks.
Variables (bCmp bP bV bS bU bQ bN bG bI bOV bOS bOO bT bR0 bR1 bR2 bR3 bR4 bR5 bR6 bR7 bR8 bR9 bR10 bR11 : block).
Definition mt_block_list : list (block * Z * Z) :=
  ltac:(let r := eval vm_compute in (blocks_of_env sha_ge (mt_env [bCmp; bP; bV; bS; bU; bQ; bN; bG; bI; bOV; bOS; bOO; bT; bR0; bR1; bR2; bR3; bR4; bR5; bR6; bR7; bR8; bR9; bR10; bR11])) in exact r).
Lemma mt_blocks : blocks_of_env sha_ge (mt_env [bCmp; bP; bV; bS; bU; bQ; bN; bG; bI; bOV; bOS; bOO; bT; bR0; bR1; bR2; bR3; bR4; bR5; bR6; bR7; bR8; bR9; bR10; bR11]) = mt_block_list.
Proof. vm_compute. reflexivity. Qed.
End Blocks.

Lemma mt_entry m m0 bs vraw :
  alloc_list m (488 :: repeat 88 24) = (m0, bs) ->
  function_entry2 sha_ge f_simplicity_bitcoin_mallocTransaction [vraw] m (mt_env bs)
    (PTree.set _rawTx vraw (create_undef_temps (fn_temps f_simplicity_bitcoin_mallocTransaction))) m0.
Proof.
  intros HAL. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst; try contradiction; discriminate.
  - unfold mt_env. apply alloc_vars_list. rewrite mt_var_sizes. exact HAL.
  - reflexivity.
Qed.

Local Opaque sha_ge.

Lemma Forall2_left_all {A B} (P : A -> B -> Prop) (Q : A -> Prop) (l1 : list A) (l2 : list B) :
  Forall2 P l1 l2 -> (forall a b, P a b -> Q a) -> forall a, In a l1 -> Q a.
Proof.
  induction 1 as [|a b l1 l2 Hab _ IH]; intros HQ x Hx; [destruct Hx|].
  destruct Hx as [<-|Hx]; [eapply HQ; exact Hab|apply IH; assumption].
Qed.

Lemma Forall2_combine_In {A B} (P : A -> B -> Prop) (l1 : list A) (l2 : list B) :
  Forall2 P l1 l2 -> forall a b, In (a, b) (combine l1 l2) -> P a b.
Proof.
  induction 1 as [|a b l1 l2 Hab _ IH]; intros x y Hxy; cbn in Hxy; [contradiction|].
  destruct Hxy as [E|Hxy]; [injection E as <- <-; exact Hab|apply IH, Hxy].
Qed.

Lemma notin_ne {A} (x y : A) (l : list A) : ~ In x l -> In y l -> x <> y.
Proof. intros H1 H2 ->. exact (H1 H2). Qed.

Lemma NoDup_nth_ne {A} (l : list A) i j (x y : A) :
  NoDup l -> nth_error l i = Some x -> nth_error l j = Some y -> i <> j -> x <> y.
Proof.
  intros ND Hi Hj Hij E. subst y. apply Hij.
  eapply (proj1 (NoDup_nth_error l) ND); [apply nth_error_Some; congruence|congruence].
Qed.

Lemma item_ok_intro e bA r c f d bR bC :
  e!r = Some (bR, CTX) -> e!c = Some (bC, CTX) -> envu_field_at _bitcoinTransaction f d ->
  0 <= d /\ d + 32 <= 488 -> (4 | d) -> bA <> bC -> bA <> bR -> bR <> bC ->
  GC <> bC -> GM <> bC -> GC <> bR -> GM <> bR -> item_ok e bA (r, c, f, d, bR, bC).
Proof. intros. cbn [item_ok]. repeat (split; [assumption|]). assumption. Qed.

Ltac inb' := cbn [In]; repeat (first [left; reflexivity | right]); fail.
Ltac idx x l := lazymatch l with | x :: _ => constr:(O) | _ :: ?t => let n := idx x t in constr:(S n) end.
Ltac ndne :=
  lazymatch goal with
  | ND : NoDup ?l |- ?x <> ?y =>
      let i := idx x l in let j := idx y l in
      exact (NoDup_nth_ne l i j x y ND eq_refl eq_refl ltac:(discriminate))
  end.
Ltac nal :=
  match goal with
  | F : ~ In ?x ?l |- ?x <> ?y => apply (notin_ne x y l F); inb'
  | F : ~ In ?y ?l |- ?x <> ?y => apply not_eq_sym; apply (notin_ne y x l F); inb'
  end.
Ltac sepb := first [assumption | ndne | nal].
(* The index is computed from the offset: trying the wrong field would make
   the unifier compare two unfolded composite lookups. *)
Ltac hoff :=
  lazymatch goal with
  | |- envu_field_at _ ?f ?d =>
      let i := eval vm_compute in (Z.to_nat ((d - 16) / 32)) in exact (mt_hash_offsets i f eq_refl)
  end.
Ltac okt :=
  apply item_ok_intro;
    [reflexivity|reflexivity|hoff|clear; lia|apply (proj1 (Z.mod_divide _ 4 ltac:(discriminate))); reflexivity
    |sepb|sepb|sepb|sepb|sepb|sepb|sepb].
Ltac sept :=
  let c0 := fresh "c0" in let Hc0 := fresh "Hc0" in
  intros c0 Hc0; cbn [In] in Hc0;
  repeat (destruct Hc0 as [<-|Hc0];
    [cbn [item_sep ctx_block ctx_out]; split; [sepb|split; [sepb|split; [sepb|clear; lia]]]|]);
  contradiction.
Ltac rng :=
  try change (size_chunk Mint32) with 4; try change (size_chunk Mint64) with 8;
  try change (size_chunk Mptr) with 8; try change (size_chunk Mint8unsigned) with 1; flia.

(** What the allocated transaction holds. *)
Definition tx_built (m : mem) (bA : block) (niv nov ver lt : int) (txb : list int)
    (data : nat -> in_data) (val : nat -> int64) (spb : nat -> list int) : Prop :=
  let ni := Int.unsigned niv in
  let no := Int.unsigned nov in
  let Nn := Z.to_nat ni in
  let Mn := Z.to_nat no in
  let rg := fun (o : Z) (rs : list int) =>
    forall j, (j < 8)%nat -> Mem.load Mint32 m bA (o + 4 * Z.of_nat j) = Some (Vint (nth j rs Int.zero)) in
  let I := in_regsI data Nn in
  let O := out_regsO no val spb in
  let U := in_regsU data Nn in
  Mem.load Mptr m bA 0 = Some (Vptr bA (Ptrofs.repr 488)) /\
  Mem.load Mptr m bA 8 = Some (Vptr bA (Ptrofs.repr (488 + 160 * ni))) /\
  rg 16 (out_regsV no val) /\ rg 48 (out_regsS no spb) /\ rg 80 O /\
  rg 112 (in_regsP data Nn) /\ rg 144 (in_regsV data Nn) /\ rg 176 (in_regsS data Nn) /\ rg 208 U /\
  rg 240 (in_regsQ data Nn) /\ rg 272 (in_regsN data Nn) /\ rg 304 (in_regsG data Nn) /\ rg 336 I /\
  rg 368 (mt_txhash_regs (Int64.repr (Int.unsigned ver)) (Int64.repr (Int.unsigned lt)) I O U) /\
  rg 400 (tm_words txb) /\
  Mem.load Mint64 m bA 432 = Some (Vlong (in_tot data Nn)) /\
  Mem.load Mint64 m bA 440 = Some (Vlong (out_tot val Mn)) /\
  Mem.load Mint64 m bA 448 = Some (Vlong (Int64.repr ni)) /\
  Mem.load Mint64 m bA 456 = Some (Vlong (Int64.repr no)) /\
  Mem.load Mint64 m bA 464 = Some (Vlong (Int64.repr (Int.unsigned ver))) /\
  Mem.load Mint64 m bA 472 = Some (Vlong (Int64.repr (Int.unsigned lt))) /\
  Mem.load Mint8unsigned m bA 480 = Some (Vint (in_final data Nn)) /\
  (forall j, (j < Nn)%nat -> in_rec m bA (488 + 160 * Z.of_nat j) (data j)) /\
  (forall j, (j < Mn)%nat ->
     Mem.load Mint64 m bA (488 + 160 * ni + 40 * Z.of_nat j) = Some (Vlong (val j)) /\
     forall i, (i < 8)%nat ->
       Mem.load Mint32 m bA (488 + 160 * ni + 40 * Z.of_nat j + 8 + 4 * Z.of_nat i) =
         Some (Vint (nth i (hash_buffer_regs (spb j)) Int.zero))).

Theorem eval_mallocTransaction (Hmodel : memcpy_model) m braw oraw btx otx bri ori bro oro
    (niv nov ver lt : int) (txb : list int) (data : nat -> in_data)
    (val : nat -> int64) (bsp : nat -> block) (osp : nat -> ptrofs) (spb : nat -> list int) :
  0 <= oraw /\ oraw + 40 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m braw oraw = Some (Vptr btx otx) ->
  (0 < Int.unsigned niv -> Mem.load Mptr m braw (oraw + 8) = Some (Vptr bri (Ptrofs.repr ori))) ->
  (0 < Int.unsigned nov -> Mem.load Mptr m braw (oraw + 16) = Some (Vptr bro (Ptrofs.repr oro))) ->
  Mem.load Mint32 m braw (oraw + 24) = Some (Vint niv) ->
  Mem.load Mint32 m braw (oraw + 28) = Some (Vint nov) ->
  Mem.load Mint32 m braw (oraw + 32) = Some (Vint ver) ->
  Mem.load Mint32 m braw (oraw + 36) = Some (Vint lt) ->
  Ptrofs.unsigned otx + 32 <= Ptrofs.max_unsigned ->
  (forall i, (i < 32)%nat ->
     Mem.load Mint8unsigned m btx (Ptrofs.unsigned otx + Z.of_nat i) = Some (Vint (nth i txb Int.zero))) ->
  0 <= ori /\ ori + 64 * Int.unsigned niv <= Ptrofs.max_unsigned ->
  (forall j, (j < Z.to_nat (Int.unsigned niv))%nat ->
     raw_in_at (Mem.valid_block m) m bri (ori + 64 * Z.of_nat j) (data j)) ->
  0 <= oro /\ oro + 24 * Int.unsigned nov <= Ptrofs.max_unsigned ->
  (forall j, (j < Z.to_nat (Int.unsigned nov))%nat ->
     Mem.load Mint64 m bro (oro + 24 * Z.of_nat j) = Some (Vlong (val j))) ->
  (forall j, (j < Z.to_nat (Int.unsigned nov))%nat ->
     raw_buffer_at m bro (oro + 24 * Z.of_nat j + 8) (bsp j) (osp j) (spb j)) ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  exists m' bA,
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_bitcoin_mallocTransaction)
      [Vptr braw (Ptrofs.repr oraw)] E0 m' (Vptr bA Ptrofs.zero) /\
    ~ Mem.valid_block m bA /\
    tx_built m' bA niv nov ver lt txb data val spb /\
    (forall ch b ofs, Mem.valid_block m b -> Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b) /\
    Mem.load Mptr m' bA (-8) =
      Some (Vlong (Int64.repr (488 + 160 * Int.unsigned niv + 40 * Int.unsigned nov))) /\
    Mem.range_perm m' bA (-8) (488 + 160 * Int.unsigned niv + 40 * Int.unsigned nov) Cur Freeable.
Proof.
  intros Horaw HTx HInP HOutP HNi HNo HVer HLt Hotx HTxB Hori HRaw Horo HVals HBufs Hdisp HMax.
  set (ni := Int.unsigned niv) in *. set (no := Int.unsigned nov) in *.
  set (Nn := Z.to_nat ni) in *. set (Mn := Z.to_nat no) in *.
  assert (Hni : 0 <= ni <= 4294967295).
  { unfold ni. pose proof (Int.unsigned_range_2 niv) as H. change Int.max_unsigned with 4294967295 in H. exact H. }
  assert (Hno : 0 <= no <= 4294967295).
  { unfold no. pose proof (Int.unsigned_range_2 nov) as H. change Int.max_unsigned with 4294967295 in H. exact H. }
  assert (VG : Mem.valid_block m GC) by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m GM) by (eapply load_valid_block; exact HMax).
  assert (Vraw : Mem.valid_block m braw) by (eapply load_valid_block; exact HTx).
  assert (Vtx : Mem.valid_block m btx) by (eapply load_valid_block; exact (HTxB 0%nat ltac:(lia))).
  assert (Vri : 0 < ni -> Mem.valid_block m bri).
  { intros Hp. destruct (HRaw 0%nat ltac:(unfold Nn; lia)) as (A1 & _). eapply load_valid_block; exact A1. }
  assert (Vro : 0 < no -> Mem.valid_block m bro).
  { intros Hp. eapply load_valid_block. exact (HVals 0%nat ltac:(unfold Mn; lia)). }
  destruct (alloc_list m (488 :: repeat 88 24)) as [m0 bs] eqn:HAL.
  destruct (alloc_list_props _ _ _ _ HAL) as ((XV & XL & XP & XA) & FRh & ND & FA).
  pose proof (Forall2_length FA) as HLen. simpl in HLen.
  destruct bs as [|bCmp bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bP bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bV bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bS bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bU bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bQ bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bN bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bG bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bI bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bOV bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bOS bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bOO bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bT bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bR0 bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bR1 bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bR2 bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bR3 bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bR4 bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bR5 bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bR6 bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bR7 bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bR8 bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bR9 bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bR10 bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs as [|bR11 bs]; [discriminate HLen|]; simpl in HLen; injection HLen as HLen.
  destruct bs; [clear HLen|discriminate HLen].
  pose proof (Forall2_left_all _ (fun b => Mem.valid_block m0 b) _ _ FA (fun a b H => proj2 H)) as VL.
  pose proof (fun b z H => proj1 (Forall2_combine_In _ _ _ FA b z H)) as PL.
  cbn [combine repeat] in PL.
  assert (Fresh : forall b, Mem.valid_block m b -> ~ In b [bCmp; bP; bV; bS; bU; bQ; bN; bG; bI; bOV; bOS; bOO; bT; bR0; bR1; bR2; bR3; bR4; bR5; bR6; bR7; bR8; bR9; bR10; bR11]) by exact FRh.
  pose proof (Fresh GC VG) as FG. pose proof (Fresh GM VM) as FM.
  pose proof (Fresh braw Vraw) as Fraw. pose proof (Fresh btx Vtx) as Ftx.
  set (e := mt_env [bCmp; bP; bV; bS; bU; bQ; bN; bG; bI; bOV; bOS; bOO; bT; bR0; bR1; bR2; bR3; bR4; bR5; bR6; bR7; bR8; bR9; bR10; bR11]).
  (* 1: sizes, malloc *)
  assert (HNi0 : Mem.load Mint32 m0 braw (oraw + 24) = Some (Vint niv)) by (rewrite XL by exact Vraw; exact HNi).
  assert (HNo0 : Mem.load Mint32 m0 braw (oraw + 28) = Some (Vint nov)) by (rewrite XL by exact Vraw; exact HNo).
  assert (HWeak : Mem.weak_valid_pointer m0 braw (Ptrofs.unsigned (Ptrofs.repr oraw)) = true).
  { rewrite Ptrofs.unsigned_repr by lia. unfold Mem.weak_valid_pointer. apply orb_true_iff. left.
    apply Mem.valid_pointer_nonempty_perm.
    assert (HL0 : Mem.load Mptr m0 braw oraw = Some (Vptr btx otx)) by (rewrite XL by exact Vraw; exact HTx).
    apply Mem.load_valid_access in HL0. destruct HL0 as [HR _].
    eapply Mem.perm_implies; [apply HR; change (size_chunk Mptr) with 8; lia|constructor]. }
  destruct (mt_prelude e braw oraw niv nov eq_refl Horaw Hni Hno m0 HNi0 HNo0 HWeak)
    as (m1 & m2 & bA & le1 & HA & HS & Hle1 & K1).
  fold ni no in HA, HS, Hle1.
  assert (NAfresh : ~ Mem.valid_block m0 bA) by (eapply Mem.fresh_block_alloc; exact HA).
  assert (NAold : forall b, Mem.valid_block m0 b -> b <> bA) by (intros b Hb E; apply NAfresh; rewrite <- E; exact Hb).
  assert (NAl : ~ In bA [bCmp; bP; bV; bS; bU; bQ; bN; bG; bI; bOV; bOS; bOO; bT; bR0; bR1; bR2; bR3; bR4; bR5; bR6; bR7; bR8; bR9; bR10; bR11]) by (intros HIn; apply NAfresh, VL, HIn).
  assert (NGA : GC <> bA) by (apply NAold, XV, VG).
  assert (NMA : GM <> bA) by (apply NAold, XV, VM).
  assert (NrA : braw <> bA) by (apply NAold, XV, Vraw).
  assert (NAtx : bA <> btx) by (apply not_eq_sym, NAold, XV, Vtx).
  assert (L2 : forall ch b ofs, Mem.valid_block m0 b -> Mem.load ch m2 b ofs = Mem.load ch m0 b ofs).
  { intros ch b ofs Hb. rewrite (Mem.load_store_other _ _ _ _ _ _ HS) by (left; apply NAold, Hb).
    eapply Mem.load_alloc_unchanged; [exact HA|exact Hb]. }
  assert (P2 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m2 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact HS|]. eapply Mem.perm_alloc_1; [exact HA|exact Hp]. }
  assert (V2 : forall b, Mem.valid_block m0 b -> Mem.valid_block m2 b).
  { intros b Hb. eapply Mem.store_valid_block_1; [exact HS|]. eapply Mem.valid_block_alloc; [exact HA|exact Hb]. }
  assert (PH2 : Mem.range_perm m2 bA (-8) (488 + 160 * ni + 40 * no) Cur Freeable).
  { intros o Ho. eapply Mem.perm_store_1; [exact HS|]. eapply Mem.perm_alloc_2; [exact HA|exact Ho]. }
  assert (PA2 : Mem.range_perm m2 bA 0 (488 + 160 * ni + 40 * no) Cur Freeable).
  { intros o Ho. apply PH2. lia. }
  assert (HH2 : Mem.load Mptr m2 bA (-8) = Some (Vlong (Int64.repr (488 + 160 * ni + 40 * no)))).
  { rewrite (Mem.load_store_same _ _ _ _ _ _ HS). reflexivity. }
  assert (VA2 : Mem.valid_block m2 bA).
  { eapply Mem.store_valid_block_1; [exact HS|]. eapply Mem.valid_new_block; exact HA. }
  assert (Kold2 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m2 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite L2 by (apply XV, Hb). apply XL, Hb. }
  assert (PLoc2 : forall b z, In (b, z) (combine [bCmp; bP; bV; bS; bU; bQ; bN; bG; bI; bOV; bOS; bOO; bT; bR0; bR1; bR2; bR3; bR4; bR5; bR6; bR7; bR8; bR9; bR10; bR11] (488 :: repeat 88 24)) -> Mem.range_perm m2 b 0 z Cur Freeable).
  { intros b z Hbz o Ho. apply P2. exact (PL b z Hbz o Ho). }
  cbn [combine repeat] in PLoc2.
  (* 2: the compound literal *)
  destruct (mt_fill_exec e bCmp bA braw oraw niv nov ver lt eq_refl Horaw ltac:(sepb) ltac:(sepb) le1 m2 Hle1)
    as (m3 & le2 & HFill & Hle2 & L3 & P3 & V3 & K2).
  { rewrite Kold2 by exact Vraw. exact HNi. }
  { rewrite Kold2 by exact Vraw. exact HNo. }
  { rewrite Kold2 by exact Vraw. exact HVer. }
  { rewrite Kold2 by exact Vraw. exact HLt. }
  { intros o Ho. eapply Mem.perm_implies; [eapply (PLoc2 bCmp 488); [inb'|exact Ho]|constructor]. }
  { intros o Ho. eapply Mem.perm_implies; [apply PA2; flia|constructor]. }
  fold ni no in HFill, Hle2.
  destruct HFill as (F0 & F8 & F432 & F440 & F448 & F456 & F464 & F472 & F480).
  assert (Kold3 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m3 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. pose proof (Fresh b Hb) as Fb.
    rewrite L3; [apply Kold2, Hb|sepb|left; apply NAold, XV, Hb]. }
  (* 3: the txid *)
  destruct (mt_txid e bA braw btx oraw otx txb ni eq_refl Horaw NAtx Hotx le2 m3 Hle2)
    as (m4 & le3 & HSt4 & Hle3 & K3).
  { rewrite Kold3 by exact Vraw. exact HTx. }
  { intros i Hi. rewrite Kold3 by exact Vtx. apply HTxB, Hi. }
  { intros o Ho. eapply Mem.perm_implies; [apply P3, PA2; flia|constructor]. }
  assert (L4 : forall ch b ofs, (b <> bA \/ ofs + size_chunk ch <= 400 \/ 432 <= ofs) ->
    Mem.load ch m4 b ofs = Mem.load ch m3 b ofs).
  { intros ch b ofs Hc. apply (store_words_load_other _ _ _ _ _ HSt4).
    destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc|right; left; exact Hc|right; right; exact Hc]. }
  assert (P4 : forall b ofs k p, Mem.perm m3 b ofs k p -> Mem.perm m4 b ofs k p).
  { intros b ofs k p Hp. apply (store_words_perm _ _ _ _ _ HSt4). exact Hp. }
  assert (V4 : forall b, Mem.valid_block m3 b -> Mem.valid_block m4 b).
  { intros b Hb. unfold Mem.valid_block. rewrite (store_words_nextblock _ _ _ _ _ HSt4). exact Hb. }
  assert (HTxid4 : forall j, (j < 8)%nat ->
    Mem.load Mint32 m4 bA (400 + 4 * Z.of_nat j) = Some (Vint (nth j (tm_words txb) Int.zero))).
  { intros j Hj. apply (u32_nth m4 bA 400 (tm_words txb)); [eapply store_words_loads; exact HSt4|exact Hj]. }
  assert (Vold4 : forall b, Mem.valid_block m b -> Mem.valid_block m4 b).
  { intros b Hb. apply V4, V3, V2, XV, Hb. }
  assert (Kold4 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m4 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite L4 by (left; apply NAold, XV, Hb). apply Kold3, Hb. }
  assert (PLoc4 : forall b z, In (b, z) (combine [bCmp; bP; bV; bS; bU; bQ; bN; bG; bI; bOV; bOS; bOO; bT; bR0; bR1; bR2; bR3; bR4; bR5; bR6; bR7; bR8; bR9; bR10; bR11] (488 :: repeat 88 24)) -> Mem.range_perm m4 b 0 z Cur Freeable).
  { intros b z Hbz o Ho. apply P4, P3, P2. exact (PL b z Hbz o Ho). }
  cbn [combine repeat] in PLoc4.
  assert (PA4 : Mem.range_perm m4 bA 0 (488 + 160 * ni + 40 * no) Cur Freeable).
  { intros o Ho. apply P4, P3, PA2, Ho. }
  (* 4: the input block *)
  assert (HWfI : items_wf e bA (mk_items in_specs [(bR11, bP); (bR10, bV); (bR9, bS); (bR8, bU); (bR7, bQ); (bR6, bN); (bR5, bG); (bR4, bI)]) []).
  { cbn [mk_items in_specs combine map items_wf item_entry].
    repeat (split; [okt|split; [sept|]]). exact Logic.I. }
  destruct (mt_inblock_exec Hmodel e bA bR11 bP bR10 bV bR9 bS bR8 bU bR7 bQ bR6 bN bR5 bG bR4 bI braw bri
    oraw ori ni data (Mem.valid_block m) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    Hni Horaw Hori NGA NMA HWfI le3 m4 Hle3)
    as (m5 & le4 & Hle4 & IP & IV & IS & IU & IQ & IN & IG & II & ITot & IFin & IRec & IOld & IFrame & IPerm & IValid & K4).
  { intros it Hit. cbn [mk_items in_specs combine map In] in Hit.
    repeat (destruct Hit as [<-|Hit];
      [cbn [item_perms]; split; [intros o Ho; eapply (PLoc4 _ 88); [inb'|exact Ho]|];
       split; [intros o Ho; eapply (PLoc4 _ 88); [inb'|exact Ho]|];
       intros o Ho; eapply Mem.perm_implies; [apply PA4; flia|constructor]|]).
    contradiction. }
  { unfold sha_dispatch_ok. rewrite Kold4 by exact VG. exact Hdisp. }
  { rewrite Kold4 by exact VM. exact HMax. }
  { intros b Hb. split; [apply Vold4, Hb|]. split; [apply NAold, XV, Hb|].
    intros HIn. apply (Fresh b Hb). cbn [In] in HIn |- *. tauto. }
  { exact Vraw. }
  { exact Vri. }
  { intros Hp. rewrite Kold4 by exact Vraw. exact (HInP Hp). }
  { intros j Hj. eapply raw_in_frame; [exact (HRaw j Hj)|apply Vri; unfold Nn in Hj; clear - Hj; lia
                                      |intros ch b ofs Hb; apply Kold4, Hb|exact Vold4]. }
  { intros o Ho. eapply Mem.perm_implies; [apply PA4; flia|constructor]. }
  { rewrite L4 by (right; right; clear; lia). exact F448. }
  { rewrite L4 by (right; right; clear; lia). exact F432. }
  { rewrite L4 by (right; right; clear; lia). exact F480. }
  destruct Hle4 as (HlRaw4 & HlTx4 & HlIn4 & HlOut4).
  assert (Kold5 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m5 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite IOld by exact Hb. apply Kold4, Hb. }
  assert (Vold5 : forall b, Mem.valid_block m b -> Mem.valid_block m5 b).
  { intros b Hb. apply IValid, Vold4, Hb. }
  (* 5: the output block *)
  assert (HWfO : items_wf e bA (mk_items out_specs [(bR3, bOV); (bR2, bOS); (bR1, bOO)]) []).
  { cbn [mk_items out_specs combine map items_wf item_entry].
    repeat (split; [okt|split; [sept|]]). exact Logic.I. }
  assert (HSepO : ctxs_sep bA (out_cs bOO bOS bOV val spb 0 false false)).
  { eapply ctxs_sep_shape'; [|exact (items_wf_sep e bA _ [] HWfO (ctxs_sep_nil bA NGA NMA))]. reflexivity. }
  destruct (mt_outblock_exec Hmodel e bA bR3 bOV bR2 bOS bR1 bOO braw bro oraw oro ni no val bsp osp spb
    (Mem.valid_block m) eq_refl eq_refl eq_refl eq_refl eq_refl Hni Hno Horaw Horo HWfO HSepO le4 m5
    HlTx4 HlOut4 HlRaw4)
    as (m6 & le5 & HlTx5 & OV & OS & OO & OTot & ORec & OOld & OFrame & OPerm & OValid & K5).
  { intros it Hit. cbn [mk_items out_specs combine map In] in Hit.
    repeat (destruct Hit as [<-|Hit];
      [cbn [item_perms]; split; [intros o Ho; apply IPerm; eapply (PLoc4 _ 88); [inb'|exact Ho]|];
       split; [intros o Ho; apply IPerm; eapply (PLoc4 _ 88); [inb'|exact Ho]|];
       intros o Ho; eapply Mem.perm_implies; [apply IPerm, PA4; flia|constructor]|]).
    contradiction. }
  { unfold sha_dispatch_ok. rewrite Kold5 by exact VG. exact Hdisp. }
  { rewrite Kold5 by exact VM. exact HMax. }
  { intros b Hb. pose proof (Fresh b Hb) as Fb. split; [apply Vold5, Hb|]. split; [apply NAold, XV, Hb|].
    repeat split; sepb. }
  { exact Vraw. }
  { exact Vro. }
  { intros j Hj. destruct (HBufs j Hj) as (len & _ & _ & _ & _ & B5 & _). exact B5. }
  { intros Hp. rewrite Kold5 by exact Vraw. exact (HOutP Hp). }
  { intros j Hj. rewrite Kold5 by (apply Vro; unfold Mn in Hj; clear - Hj; lia). apply HVals, Hj. }
  { intros j Hj. pose proof (HBufs j Hj) as HB. pose proof HB as (len & _ & _ & _ & _ & B5 & _).
    eapply raw_buffer_at_frame; [exact HB| |exact Vold5].
    intros ch b' ofs [->| ->]; apply Kold5; [apply Vro; unfold Mn in Hj; clear - Hj; lia|exact B5]. }
  { intros o Ho. eapply Mem.perm_implies; [apply IPerm, PA4; flia|constructor]. }
  { rewrite IFrame by (right; right; change (size_chunk Mint64) with 8; clear; lia).
    rewrite L4 by (right; right; clear; lia). exact F456. }
  { rewrite IFrame by (right; right; change (size_chunk Mint64) with 8; clear; lia).
    rewrite L4 by (right; right; clear; lia). exact F440. }
  assert (Kold6 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m6 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite OOld by exact Hb. apply Kold5, Hb. }
  assert (VA6 : Mem.valid_block m6 bA) by (apply OValid, IValid, V4, V3, VA2).
  (* 6: the transaction hash, return *)
  assert (HOkT : item_ok e bA (__res, _ctx_txHash, _txHash, 368, bR0, bT)) by okt.
  destruct (mt_txhash Hmodel e bA bR0 bT (Int64.repr (Int.unsigned ver)) (Int64.repr (Int.unsigned lt))
    (in_regsI data Nn) (out_regsO no val spb) (in_regsU data Nn)
    eq_refl eq_refl eq_refl eq_refl NGA NMA HOkT le5 m6 HlTx5)
    as (m7 & le6 & HExec & HTxH & L7 & P7 & V7).
  { cbn [item_perms]. split; [intros o Ho; apply OPerm, IPerm; eapply (PLoc4 _ 88); [inb'|exact Ho]|].
    split; [intros o Ho; apply OPerm, IPerm; eapply (PLoc4 _ 88); [inb'|exact Ho]|].
    intros o Ho. eapply Mem.perm_implies; [apply OPerm, IPerm, PA4; flia|constructor]. }
  { unfold sha_dispatch_ok. rewrite Kold6 by exact VG. exact Hdisp. }
  { rewrite Kold6 by exact VM. exact HMax. }
  { rewrite OFrame by rng. rewrite IFrame by (right; right; change (size_chunk Mint64) with 8; clear; lia).
    rewrite L4 by (right; right; clear; lia). exact F464. }
  { rewrite OFrame by rng. rewrite IFrame by (right; right; change (size_chunk Mint64) with 8; clear; lia).
    rewrite L4 by (right; right; clear; lia). exact F472. }
  { intros j Hj. rewrite OFrame by rng. apply II, Hj. }
  { exact OO. }
  { intros j Hj. rewrite OFrame by rng. apply IU, Hj. }
  assert (T7 : forall ch ofs, (ofs + size_chunk ch <= 368 \/ 400 <= ofs) ->
    Mem.load ch m7 bA ofs = Mem.load ch m6 bA ofs).
  { intros ch ofs Hc. apply L7; [exact VA6|sepb|sepb|right; exact Hc]. }
  assert (Kold7 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m7 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. pose proof (Fresh b Hb) as Fb.
    rewrite L7; [apply Kold6, Hb|apply OValid, Vold5, Hb|sepb|sepb|left; apply NAold, XV, Hb]. }
  assert (Pall7 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m7 b ofs k p).
  { intros b ofs k p Hp. apply P7, OPerm, IPerm, P4, P3, P2, Hp. }
  (* freeing the locals *)
  assert (Hsub : forall x, In x (map (fun y : block * Z * Z => fst (fst y)) (mt_block_list bCmp bP bV bS bU bQ bN bG bI bOV bOS bOO bT bR0 bR1 bR2 bR3 bR4 bR5 bR6 bR7 bR8 bR9 bR10 bR11)) -> In x [bCmp; bP; bV; bS; bU; bQ; bN; bG; bI; bOV; bOS; bOO; bT; bR0; bR1; bR2; bR3; bR4; bR5; bR6; bR7; bR8; bR9; bR10; bR11]).
  { intros x Hx. cbn [mt_block_list map fst In] in Hx.
    repeat (destruct Hx as [<-|Hx]; [inb'|]). contradiction. }
  destruct (free_list_blocks (mt_block_list bCmp bP bV bS bU bQ bN bG bI bOV bOS bOO bT bR0 bR1 bR2 bR3 bR4 bR5 bR6 bR7 bR8 bR9 bR10 bR11) m7) as (mf & HFL & HLf & HPf & HVf).
  { intros b lo hi HIn. cbn [mt_block_list In] in HIn.
    repeat (destruct HIn as [E|HIn];
      [injection E as <- <- <-; intros o Ho; apply Pall7; (eapply PL; [|exact Ho]); inb'|]).
    contradiction. }
  { eapply NoDup_incl_NoDup; [exact ND|apply Nat.le_refl|].
    intros x Hx. cbn [mt_block_list map fst In] in Hx |- *.
    repeat (destruct Hx as [<-|Hx]; [inb'|]). contradiction. }
  assert (LAf : forall ch ofs, Mem.load ch mf bA ofs = Mem.load ch m7 bA ofs).
  { intros ch ofs. apply HLf. intros HIn. exact (NAl (Hsub bA HIn)). }
  exists mf, bA.
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - eapply eval_funcall_internal with (e := e) (m1 := m0) (m2 := m7)
      (out := Out_return (Some (Vptr bA Ptrofs.zero, tptr TX))).
    + apply mt_entry. exact HAL.
    + apply K1, K2, K3, K4, K5. exact HExec.
    + cbn. split; [discriminate|reflexivity].
    + unfold e. rewrite mt_blocks. exact HFL.
  - intros Hv. apply NAfresh, XV, Hv.
  - unfold tx_built. cbv beta zeta. fold ni. fold no. fold Nn. fold Mn.
    split.
    { rewrite LAf, T7 by rng. rewrite OFrame by rng. rewrite IFrame by rng. rewrite L4 by rng. exact F0. }
    split.
    { rewrite LAf, T7 by rng. rewrite OFrame by rng. rewrite IFrame by rng. rewrite L4 by rng. exact F8. }
    split; [intros j Hj; rewrite LAf, T7 by rng; apply OV, Hj|].
    split; [intros j Hj; rewrite LAf, T7 by rng; apply OS, Hj|].
    split; [intros j Hj; rewrite LAf, T7 by rng; apply OO, Hj|].
    split; [intros j Hj; rewrite LAf, T7 by rng; rewrite OFrame by rng; apply IP, Hj|].
    split; [intros j Hj; rewrite LAf, T7 by rng; rewrite OFrame by rng; apply IV, Hj|].
    split; [intros j Hj; rewrite LAf, T7 by rng; rewrite OFrame by rng; apply IS, Hj|].
    split; [intros j Hj; rewrite LAf, T7 by rng; rewrite OFrame by rng; apply IU, Hj|].
    split; [intros j Hj; rewrite LAf, T7 by rng; rewrite OFrame by rng; apply IQ, Hj|].
    split; [intros j Hj; rewrite LAf, T7 by rng; rewrite OFrame by rng; apply IN, Hj|].
    split; [intros j Hj; rewrite LAf, T7 by rng; rewrite OFrame by rng; apply IG, Hj|].
    split; [intros j Hj; rewrite LAf, T7 by rng; rewrite OFrame by rng; apply II, Hj|].
    split; [intros j Hj; rewrite LAf; apply HTxH, Hj|].
    split.
    { intros j Hj. rewrite LAf, T7 by rng. rewrite OFrame by rng. rewrite IFrame by rng. apply HTxid4, Hj. }
    split; [rewrite LAf, T7 by rng; rewrite OFrame by rng; exact ITot|].
    split; [rewrite LAf, T7 by rng; exact OTot|].
    split.
    { rewrite LAf, T7 by rng. rewrite OFrame by rng. rewrite IFrame by rng. rewrite L4 by rng. exact F448. }
    split.
    { rewrite LAf, T7 by rng. rewrite OFrame by rng. rewrite IFrame by rng. rewrite L4 by rng. exact F456. }
    split.
    { rewrite LAf, T7 by rng. rewrite OFrame by rng. rewrite IFrame by rng. rewrite L4 by rng. exact F464. }
    split.
    { rewrite LAf, T7 by rng. rewrite OFrame by rng. rewrite IFrame by rng. rewrite L4 by rng. exact F472. }
    split; [rewrite LAf, T7 by rng; rewrite OFrame by rng; exact IFin|].
    split.
    { intros j Hj. eapply in_rec_frame; [exact (IRec j Hj)|]. intros ch ofs H1 H2.
      assert (Hj' : Z.of_nat j < ni) by (unfold Nn in Hj; clear - Hj Hni; lia).
      rewrite LAf, T7 by (right; clear - H1; lia). apply OFrame; [clear - H2 Hj'; lia|right; right; clear - H1; lia]. }
    intros j Hj. destruct (ORec j Hj) as [HOv HOs]. split.
    + rewrite LAf, T7 by (right; clear - Hni; lia). exact HOv.
    + intros i Hi. rewrite LAf, T7 by (right; clear - Hni; lia). apply HOs, Hi.
  - intros ch b ofs Hb. rewrite HLf; [apply Kold7, Hb|].
    intros HIn. exact (Fresh b Hb (Hsub b HIn)).
  - intros b ofs k p Hp. apply HPf; [|apply Pall7, XP, Hp].
    intros HIn. exact (Fresh b (Mem.perm_valid_block _ _ _ _ _ Hp) (Hsub b HIn)).
  - intros b Hb. apply HVf, V7, OValid, Vold5, Hb.
  - rewrite LAf, T7 by rng. rewrite OFrame by rng. rewrite IFrame by rng. rewrite L4 by rng.
    rewrite L3; [exact HH2|sepb|right; left; cbn; lia].
  - intros o Ho. apply HPf; [intros HIn; exact (NAl (Hsub bA HIn))|].
    apply P7, OPerm, IPerm, P4, P3, PH2, Ho.
Qed.
