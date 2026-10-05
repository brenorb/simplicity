(** Preparation for the tapdata_init jet: sequential local allocation,
    [sha256_init] followed by the struct copy of its result, and the struct
    copy statement itself, in the SHA translation unit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_sha256_init_layout C.jet_struct_copy_loads.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_compress_call C.jet_sha_init_transport C.jet_sha_add_n_init.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Fixpoint alloc_list (m : mem) (zs : list Z) : mem * list block :=
  match zs with
  | [] => (m, [])
  | z :: zs => let (m1, b) := Mem.alloc m 0 z in
               let (m2, bs) := alloc_list m1 zs in (m2, b :: bs)
  end.

Lemma alloc_list_props zs : forall m m' bs, alloc_list m zs = (m', bs) ->
  mext m m' /\ (forall b, Mem.valid_block m b -> ~ In b bs) /\ NoDup bs /\
  Forall2 (fun b z => Mem.range_perm m' b 0 z Cur Freeable /\ Mem.valid_block m' b) bs zs.
Proof.
  induction zs as [|z zs IH]; intros m m' bs H.
  - cbn in H. injection H as <- <-. split; [apply mext_refl|]. split; [intros b _ []|]. split; constructor.
  - cbn [alloc_list] in H. destruct (Mem.alloc m 0 z) as [m1 b] eqn:A.
    destruct (alloc_list m1 zs) as [m2 bs'] eqn:R. injection H as <- <-.
    destruct (IH _ _ _ R) as (X & F & ND & FA).
    pose proof (mext_alloc _ _ _ _ _ A) as X1.
    split; [eapply mext_trans; eassumption|]. split.
    { intros b0 Hv [Heq|Hin].
      - subst b0. exact (Mem.fresh_block_alloc _ _ _ _ _ A Hv).
      - exact (F b0 (proj1 X1 b0 Hv) Hin). }
    split.
    { constructor; [|exact ND]. apply F. eapply Mem.valid_new_block; exact A. }
    constructor; [|exact FA]. split.
    + intros ofs Ho. apply (proj1 (proj2 (proj2 X))). eapply Mem.perm_alloc_2; eauto.
    + apply (proj1 X). eapply Mem.valid_new_block; exact A.
Qed.

Lemma sg_in_init : In (jets._sha256_init, jets.f_sha256_init) sha_init_helpers.
Proof. unfold sha_init_helpers. simpl. tauto. Qed.

Lemma tap_init_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_init) Ptrofs.zero) =
    Some (Internal jets.f_sha256_init).
Proof. vm_compute; reflexivity. Qed.
Lemma tap_init_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_init = Some (sha_symbol_block _sha256_init).
Proof. vm_compute; reflexivity. Qed.

(** Struct copy [dst = src] between two local context variables. *)
Lemma exec_ctx_struct_copy e le m m' (idd ids : ident) bd bs bytes :
  e!idd = Some (bd, CTX) -> e!ids = Some (bs, CTX) -> bd <> bs ->
  Mem.loadbytes m bs 0 88 = Some bytes -> Mem.storebytes m bd 0 bytes = Some m' ->
  Clight2.exec_stmt sha_ge e le m (Sassign (Evar idd CTX) (Evar ids CTX)) E0 le m' Out_normal.
Proof.
  intros Hd Hs Hne HL HS.
  eapply exec_Sassign with (v2 := Vptr bs Ptrofs.zero) (v := Vptr bs Ptrofs.zero).
  - apply eval_Evar_local; exact Hd.
  - eapply eval_Elvalue; [apply eval_Evar_local; exact Hs|apply deref_loc_copy; reflexivity].
  - reflexivity.
  - eapply assign_loc_copy with (bytes := bytes).
    + reflexivity.
    + intros _. exists 0. reflexivity.
    + intros _. exists 0. reflexivity.
    + left. congruence.
    + exact HL.
    + exact HS.
Qed.

Local Opaque sha_ge ge0.

Lemma sha_init_copy m br bc bi input :
  br <> bi -> bc <> bi -> br <> bc ->
  0 <= input -> input + 32 <= Ptrofs.max_unsigned -> (4 | input) ->
  Mem.range_perm m br 0 88 Cur Writable -> Mem.range_perm m bc 0 88 Cur Writable ->
  Mem.range_perm m bi input (input + 32) Cur Writable ->
  exists mi mx bytes,
    Clight2.eval_funcall sha_ge m (Internal jets.f_sha256_init)
      [Vptr br Ptrofs.zero; Vptr bi (Ptrofs.repr input)] E0 mi Vundef /\
    Mem.loadbytes mi br 0 88 = Some bytes /\ Mem.storebytes mi bc 0 bytes = Some mx /\
    Mem.load Mptr mx bc 0 = Some (Vptr bi (Ptrofs.repr input)) /\
    Mem.load Mint64 mx bc 8 = Some (Vlong Int64.zero) /\
    Mem.load Mint8unsigned mx bc 80 = Some (Vint Int.zero) /\
    uint32_array_at mx bi input sha256_iv_words /\
    (forall ch b ofs, Mem.valid_block m b -> b <> br -> b <> bc ->
       (b <> bi \/ ofs + size_chunk ch <= input \/ input + 32 <= ofs) ->
       Mem.load ch mx b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mx b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mx b).
Proof.
  intros Hri Hci Hrc Hi HiM HiA PR PC PI.
  destruct (eval_sha256_init_layout m br bi input Hri Hi HiM HiA PR PI)
    as (mi & HInit & HOutI & HCntI & HOvfI & HArrI & HLoadsI & HPermI & HValidI).
  apply (init_sha_transport_call _ _ sg_in_init) in HInit.
  assert (PRI : Mem.range_perm mi br 0 88 Cur Readable).
  { intros ofs H. apply HPermI. eapply Mem.perm_implies; [apply PR; exact H|constructor]. }
  destruct (Mem.range_perm_loadbytes mi br 0 88 PRI) as (bytes & HB).
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as HBL.
  assert (PCC : Mem.range_perm mi bc 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite HBL. change (Mem.range_perm mi bc 0 88 Cur Writable). intros ofs H. apply HPermI, PC, H. }
  destruct (Mem.range_perm_storebytes mi bc 0 bytes PCC) as (mx & HS).
  assert (HBx : Mem.loadbytes mx bc 0 88 = Some bytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ HS) as H. rewrite HBL in H. exact H. }
  exists mi, mx, bytes. split; [exact HInit|]. split; [exact HB|]. split; [exact HS|].
  split.
  { apply (equal_loadbytes_field Mptr mi mx br bc 0 0 88 0 bytes); [lia|cbn; lia|exact HB|exact HBx|exists 0; reflexivity|exact HOutI]. }
  split.
  { apply (equal_loadbytes_field Mint64 mi mx br bc 0 0 88 8 bytes); [lia|cbn; lia|exact HB|exact HBx|exists 1; reflexivity|exact HCntI]. }
  split.
  { apply (equal_loadbytes_field Mint8unsigned mi mx br bc 0 0 88 80 bytes); [lia|cbn; lia|exact HB|exact HBx|exists 80; reflexivity|exact HOvfI]. }
  split.
  { intros i x Hx. erewrite Mem.load_storebytes_other; [apply HArrI; exact Hx|exact HS|left; congruence]. }
  split.
  { intros ch b ofs Hv Hbr Hbc Hbi. erewrite Mem.load_storebytes_other; [|exact HS|left; exact Hbc].
    apply HLoadsI; [exact Hv|left; exact Hbr|exact Hbi]. }
  split.
  - intros b ofs k p Hp. eapply Mem.perm_storebytes_1; [exact HS|apply HPermI; exact Hp].
  - intros b Hv. eapply Mem.storebytes_valid_block_1; [exact HS|apply HValidI; exact Hv].
Qed.
