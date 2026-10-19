(** Memory invariant of [parseNullData]: the result structure, the two
    allocation cells, the script, and the opcode entries written so far.
    Any change confined to the two local SHA contexts and to the part of the
    opcode array not yet committed preserves it ([pm_change]); committing an
    entry is the increment of [result->len] ([pm_commit]). *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Maps Values Memory.
Require Import C.jet_exec C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_uchars_exec C.jet_sha_ctx_abs.
Require Import C.jet_elements_env_hashbuffer.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.

(** An opcode entry: its code and, for a push, the pushed bytes. *)
Definition pn_ent : Type := (Z * option (list int))%type.

(** [lia] without the block disequalities of the context. *)
Ltac zb :=
  repeat match goal with
         | H : ?a <> ?b |- _ => match type of a with block => clear H end
         end; lia.

Section ParseMem.
Variables (bC bRs : block).
Variables (br : block) (or_ : Z) (ba : block) (oa : Z) (bl : block) (ol : Z) (bop : block) (oop alen : Z).
Variables (bsp : block) (osp : Z) (len : int) (bb : block) (ob : ptrofs) (bs : list int).

Hypothesis Hor : 0 <= or_ /\ or_ + 16 <= Ptrofs.max_unsigned.
Hypothesis Hoop : 0 <= oop /\ oop + 36 * alen <= Ptrofs.max_unsigned.
Hypothesis Halen : 0 <= alen <= 4294967295.
Hypothesis Hsep : br <> bop \/ or_ + 16 <= oop \/ oop + 36 * alen <= or_.
Hypothesis Nba : ba <> bop.
Hypothesis Nbl : bl <> bop.
Hypothesis Nbsp : bsp <> bop.
Hypothesis Nbb : bb <> bop.
Hypothesis NG : GC <> bop.
Hypothesis NM : GM <> bop.
Hypothesis Nbar : ba <> br.
Hypothesis Nblr : bl <> br.
Hypothesis Nbspr : bsp <> br.
Hypothesis Nbbr : bb <> br.
Hypothesis NGr : GC <> br.
Hypothesis NMr : GM <> br.

Definition pn_ent_at (m : mem) (k : Z) (en : pn_ent) : Prop :=
  Mem.load Mint32 m bop (oop + 36 * k + 32) = Some (Vint (Int.repr (fst en))) /\
  match snd en with
  | Some d => forall j, (j < 8)%nat ->
      Mem.load Mint32 m bop (oop + 36 * k + 4 * Z.of_nat j) = Some (Vint (nth j (hash_buffer_regs d) Int.zero))
  | None => True
  end.

Definition pm (m : mem) (n : Z) (ents : list pn_ent) : Prop :=
  Z.of_nat (length ents) = n /\ n <= alen /\
  Mem.load Mptr m br or_ = Some (Vptr bop (Ptrofs.repr oop)) /\
  Mem.load Mint64 m br (or_ + 8) = Some (Vlong (Int64.repr n)) /\
  Mem.load Mptr m ba oa = Some (Vptr bop (Ptrofs.repr oop)) /\
  Mem.load Mint64 m bl ol = Some (Vlong (Int64.repr alen)) /\
  Mem.load Mint32 m bsp (osp + 8) = Some (Vint len) /\
  (0 < Int.unsigned len -> Mem.load Mptr m bsp osp = Some (Vptr bb ob)) /\
  (forall i, 0 <= i < Int.unsigned len ->
     Mem.load Mint8unsigned m bb (Ptrofs.unsigned ob + i) = Some (Vint (nth (Z.to_nat i) bs Int.zero))) /\
  (forall k, (k < length ents)%nat -> pn_ent_at m (Z.of_nat k) (nth k ents (0, None))) /\
  Mem.valid_access m Mptr br or_ Writable /\
  Mem.valid_access m Mint64 br (or_ + 8) Writable /\
  Mem.range_perm m bop oop (oop + 36 * alen) Cur Writable /\
  Mem.range_perm m bC 0 88 Cur Freeable /\ Mem.range_perm m bRs 0 88 Cur Freeable /\
  sha_dispatch_ok m /\ Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter).

(** A change confined to the local contexts and to the uncommitted part of
    the opcode array. *)
Definition pm_change (n : Z) (m m' : mem) : Prop :=
  (forall ch b ofs, Mem.valid_block m b -> b <> bC -> b <> bRs ->
     (b <> bop \/ ofs + size_chunk ch <= oop + 36 * n \/ oop + 36 * alen <= ofs) ->
     Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
  (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
  (forall b, Mem.valid_block m b -> Mem.valid_block m' b).

Lemma pm_change_refl n m : pm_change n m m.
Proof. repeat split; auto. Qed.

Lemma pm_change_trans n m1 m2 m3 : pm_change n m1 m2 -> pm_change n m2 m3 -> pm_change n m1 m3.
Proof.
  intros (L1 & P1 & V1) (L2 & P2 & V2). split; [|split].
  - intros ch b ofs Hb N1 N2 Hr. rewrite L2 by (try (apply V1; exact Hb); assumption). apply L1; assumption.
  - intros b ofs k p Hb Hp. apply P2; [apply V1, Hb|apply P1; assumption].
  - intros b Hb. apply V2, V1, Hb.
Qed.

Hypothesis NCr : br <> bC.
Hypothesis NRr : br <> bRs.
Hypothesis NCa : ba <> bC.
Hypothesis NRa : ba <> bRs.
Hypothesis NCl : bl <> bC.
Hypothesis NRl : bl <> bRs.
Hypothesis NCo : bop <> bC.
Hypothesis NRo : bop <> bRs.
Hypothesis NCs : bsp <> bC.
Hypothesis NRs : bsp <> bRs.
Hypothesis NCb : bb <> bC.
Hypothesis NRb : bb <> bRs.
Hypothesis NCG : GC <> bC.
Hypothesis NRG : GC <> bRs.
Hypothesis NCM : GM <> bC.
Hypothesis NRM : GM <> bRs.

Lemma load_valid m ch b ofs v : Mem.load ch m b ofs = Some v -> Mem.valid_block m b.
Proof.
  intros H. eapply Mem.perm_valid_block. apply (proj1 (Mem.load_valid_access _ _ _ _ _ H) ofs).
  pose proof (size_chunk_pos ch). lia.
Qed.

Lemma pm_change_keeps n ents m m' : pm m n ents -> pm_change n m m' -> pm m' n ents.
Proof.
  intros (HN & HNa & Hop & Hlen & Ha & Hl & HSl & HSb & HSs & HE & VA1 & VA2 & PO & PC & PR & Hd & HMx)
    (LC & PCh & VCh).
  assert (Vr : Mem.valid_block m br) by (eapply load_valid; exact Hop).
  assert (LR : forall ch ofs, or_ <= ofs -> ofs + size_chunk ch <= or_ + 16 ->
    Mem.load ch m' br ofs = Mem.load ch m br ofs).
  { intros ch ofs H1 H2. apply LC; [exact Vr|exact NCr|exact NRr|].
    destruct Hsep as [H|[H|H]]; [left; exact H|right; left; zb|right; right; zb]. }
  split; [exact HN|]. split; [exact HNa|].
  split; [rewrite LR by (change (size_chunk Mptr) with 8; zb); exact Hop|].
  split; [rewrite LR by (change (size_chunk Mint64) with 8; zb); exact Hlen|].
  split; [rewrite LC by (try (eapply load_valid; exact Ha); try assumption; left; exact Nba); exact Ha|].
  split; [rewrite LC by (try (eapply load_valid; exact Hl); try assumption; left; exact Nbl); exact Hl|].
  split; [rewrite LC by (try (eapply load_valid; exact HSl); try assumption; left; exact Nbsp); exact HSl|].
  split.
  { intros HL. rewrite LC by (try (eapply load_valid; exact (HSb HL)); try assumption; left; exact Nbsp).
    exact (HSb HL). }
  split.
  { intros i Hi. rewrite LC by (try (eapply load_valid; exact (HSs i Hi)); try assumption; left; exact Nbb).
    exact (HSs i Hi). }
  split.
  { intros k Hk. destruct (HE k Hk) as [HCd HHs].
    assert (Vop : Mem.valid_block m bop) by (eapply load_valid; exact HCd).
    assert (Hkn : Z.of_nat k < n) by zb.
    split.
    - rewrite LC by (try exact Vop; try assumption; right; left; change (size_chunk Mint32) with 4; zb).
      exact HCd.
    - destruct (snd (nth k ents (0, None))) as [d|]; [|exact I].
      intros j Hj. rewrite LC by (try exact Vop; try assumption; right; left; change (size_chunk Mint32) with 4; zb).
      exact (HHs j Hj). }
  split; [destruct VA1 as [P A]; split; [intros o Ho; apply PCh; [exact Vr|apply P, Ho]|exact A]|].
  split; [destruct VA2 as [P A]; split; [intros o Ho; apply PCh; [exact Vr|apply P, Ho]|exact A]|].
  split.
  { intros o Ho. apply PCh; [eapply Mem.perm_valid_block; apply PO, Ho|apply PO, Ho]. }
  split; [intros o Ho; apply PCh; [eapply Mem.perm_valid_block; apply PC, Ho|apply PC, Ho]|].
  split; [intros o Ho; apply PCh; [eapply Mem.perm_valid_block; apply PR, Ho|apply PR, Ho]|].
  split.
  - unfold sha_dispatch_ok in *. rewrite LC by (try (eapply load_valid; exact Hd); try assumption; left; exact NG).
    exact Hd.
  - rewrite LC by (try (eapply load_valid; exact HMx); try assumption; left; exact NM). exact HMx.
Qed.

(** [++result->len] commits the entry written at index [n]. *)
Lemma pm_commit n ents (en : pn_ent) m m' :
  pm m n ents -> n < alen -> pn_ent_at m n en ->
  Mem.store Mint64 m br (or_ + 8) (Vlong (Int64.repr (n + 1))) = Some m' ->
  pm m' (n + 1) (ents ++ [en]).
Proof.
  intros (HN & HNa & Hop & Hlen & Ha & Hl & HSl & HSb & HSs & HE & VA1 & VA2 & PO & PC & PR & Hd & HMx)
    Hlt HEn HS.
  assert (LO : forall ch b ofs, (b <> br \/ ofs + size_chunk ch <= or_ + 8 \/ or_ + 16 <= ofs) ->
    Mem.load ch m' b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hc. apply (Mem.load_store_other _ _ _ _ _ _ HS).
    change (size_chunk Mint64) with 8. destruct Hc as [H|[H|H]]; [left; exact H|right; left; exact H|right; right; zb]. }
  assert (LOp : forall ch ofs, oop <= ofs -> ofs + size_chunk ch <= oop + 36 * alen ->
    Mem.load ch m' bop ofs = Mem.load ch m bop ofs).
  { intros ch ofs H1 H2. apply LO.
    destruct Hsep as [H|[H|H]]; [left; apply not_eq_sym; exact H|right; right; zb|right; left; zb]. }
  assert (PP : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact HS|exact Hp]. }
  split; [rewrite app_length; cbn [length]; zb|]. split; [zb|].
  split; [rewrite LO by (right; left; change (size_chunk Mptr) with 8; zb); exact Hop|].
  split; [rewrite (Mem.load_store_same _ _ _ _ _ _ HS); reflexivity|].
  split; [rewrite LO by (left; exact Nbar); exact Ha|].
  split; [rewrite LO by (left; exact Nblr); exact Hl|].
  split; [rewrite LO by (left; exact Nbspr); exact HSl|].
  split; [intros HL; rewrite LO by (left; exact Nbspr); exact (HSb HL)|].
  split; [intros i Hi; rewrite LO by (left; exact Nbbr); exact (HSs i Hi)|].
  split.
  { intros k Hk. rewrite app_length in Hk. cbn [length] in Hk.
    assert (HT : forall en' kz, 0 <= kz < alen -> pn_ent_at m kz en' -> pn_ent_at m' kz en').
    { intros en' kz Hkz [HCd HHs]. split.
      - rewrite LOp by (change (size_chunk Mint32) with 4; zb). exact HCd.
      - destruct (snd en') as [d|]; [|exact I]. intros j Hj.
        rewrite LOp by (change (size_chunk Mint32) with 4; zb). exact (HHs j Hj). }
    destruct (lt_dec k (length ents)) as [Hlk|Hge].
    - rewrite app_nth1 by exact Hlk. apply HT; [zb|exact (HE k Hlk)].
    - assert (k = length ents) by zb. subst k. rewrite app_nth2 by zb. rewrite Nat.sub_diag. cbn [nth].
      rewrite HN. apply HT; [zb|exact HEn]. }
  split; [destruct VA1 as [P A]; split; [intros o Ho; apply PP, P, Ho|exact A]|].
  split; [destruct VA2 as [P A]; split; [intros o Ho; apply PP, P, Ho|exact A]|].
  split; [intros o Ho; apply PP, PO, Ho|].
  split; [intros o Ho; apply PP, PC, Ho|].
  split; [intros o Ho; apply PP, PR, Ho|].
  split.
  - unfold sha_dispatch_ok in *. rewrite LO by (left; exact NGr). exact Hd.
  - rewrite LO by (left; exact NMr). exact HMx.
Qed.
End ParseMem.
