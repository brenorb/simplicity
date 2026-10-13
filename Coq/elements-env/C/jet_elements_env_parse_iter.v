(** One iteration of the loop of [parseNullData] against the functional
    step [pn_step]: either the function takes a failure exit
    ([result->op = NULL]) or one more opcode entry is committed. *)
From Coq Require Import ZArith List Lia PeanoNat Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_be32_exec C.jet_sha_block_local C.jet_sha_uchars_exec.
Require Import C.jet_sha_add_n_init C.jet_sha_ctx_abs.
Require Import C.jet_elements_env_field_eval C.jet_elements_env_hashbuffer C.jet_elements_env_nulldata_count.
Require Import C.jet_elements_env_parse_defs C.jet_elements_env_parse_mem C.jet_elements_env_parse_ops.
Require Import C.jet_elements_env_parse_hash.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 300.

Ltac zi :=
  repeat match goal with
         | H : ?a <> ?b |- _ => match type of a with block => clear H end
         end; lia.

Section ParseIter.
Variable Hmodel : memcpy_model.
Variables (e : env) (bC bRs : block).
Hypothesis HeC : e!_ctx = Some (bC, CTX).
Hypothesis HeR : e!__res = Some (bRs, CTX).
Hypothesis Hg1 : e!_sha256_init = None.
Hypothesis Hg3 : e!_sha256_uchars = None.
Hypothesis Hg5 : e!_sha256_finalize = None.
Variables (br : block) (or_ : Z) (ba : block) (oa : Z) (bl : block) (ol : Z) (bop : block) (oop alen : Z).
Variables (bsp : block) (osp : Z) (len : int) (bb : block) (ob : ptrofs) (bs : list int).

Hypothesis Hor : 0 <= or_ /\ or_ + 16 <= Ptrofs.max_unsigned.
Hypothesis HorA : (8 | or_).
Hypothesis Hoa : 0 <= oa /\ oa + 8 <= Ptrofs.max_unsigned.
Hypothesis Hol : 0 <= ol /\ ol + 8 <= Ptrofs.max_unsigned.
Hypothesis Hoop : 0 <= oop /\ oop + 36 * alen <= Ptrofs.max_unsigned.
Hypothesis HoopA : (4 | oop).
Hypothesis Halen : 0 <= alen <= 4294967295.
Hypothesis Hosp : 0 <= osp /\ osp + 16 <= Ptrofs.max_unsigned.
Hypothesis HobM : Ptrofs.unsigned ob + Int.unsigned len <= Ptrofs.max_unsigned.
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
Hypothesis NRC : bRs <> bC.

Let L : Z := Int.unsigned len.
Let PM := pm bC bRs br or_ ba oa bl ol bop oop alen bsp osp len bb ob bs.
Let PL := pl br or_ ba oa bl ol bsp osp.
Let PLS := pls br or_ ba oa bl ol bsp osp.

(** The functional step. *)
Definition pn_op (i : Z) : option (Z * pn_ent) :=
  let c := nd_byte bs i in
  if 96 <? c then None
  else if 79 <=? c then Some (i + 1, (4 + (c - 79), None))
  else match nd_skip len bs c (i + 1) with
       | None => None
       | Some (i', sk) =>
           if L - i' <? sk then None else Some (i' + sk, (pn_kindv c, Some (pn_data bs i' sk)))
       end.

Definition pn_step (n i : Z) : option (Z * pn_ent) :=
  if alen <=? n then None else pn_op i.

(** What the function may change of the memory it was given: the result
    structure and the opcode array (and its two local contexts). *)
Definition pn_fr (m m' : mem) : Prop :=
  (forall ch b ofs, Mem.valid_block m b -> b <> bC -> b <> bRs ->
     (b <> br \/ ofs + size_chunk ch <= or_ \/ or_ + 16 <= ofs) ->
     (b <> bop \/ ofs + size_chunk ch <= oop \/ oop + 36 * alen <= ofs) ->
     Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
  (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
  (forall b, Mem.valid_block m b -> Mem.valid_block m' b).

Lemma pn_fr_refl m : pn_fr m m.
Proof. repeat split; auto. Qed.

Lemma pn_fr_trans m1 m2 m3 : pn_fr m1 m2 -> pn_fr m2 m3 -> pn_fr m1 m3.
Proof.
  intros (L1 & P1 & V1) (L2 & P2 & V2). split; [|split].
  - intros ch b ofs Hb N1 N2 H1 H2. rewrite L2 by (try (apply V1; exact Hb); assumption). apply L1; assumption.
  - intros b ofs k p Hb Hp. apply P2; [apply V1, Hb|apply P1; assumption].
  - intros b Hb. apply V2, V1, Hb.
Qed.

Lemma pn_fr_change n m m' : 0 <= n -> pm_change bC bRs bop oop alen n m m' -> pn_fr m m'.
Proof.
  intros Hn (LC & PC & VC). split; [|split; assumption].
  intros ch b ofs Hb N1 N2 H1 H2. apply LC; try assumption.
  destruct H2 as [H|[H|H]]; [left; exact H|right; left; zi|right; right; exact H].
Qed.

Lemma pn_fr_store_res m ch ofs v m' :
  Mem.store ch m br ofs v = Some m' -> or_ <= ofs -> ofs + size_chunk ch <= or_ + 16 -> pn_fr m m'.
Proof.
  intros HS H1 H2. split; [|split].
  - intros ch' b o Hb _ _ Hr _. apply (Mem.load_store_other _ _ _ _ _ _ HS).
    destruct Hr as [H|[H|H]]; [left; exact H|right; left; zi|right; right; zi].
  - intros b o k p _ Hp. eapply Mem.perm_store_1; [exact HS|exact Hp].
  - intros b Hb. eapply Mem.store_valid_block_1; [exact HS|exact Hb].
Qed.

Lemma pm_change_store_op n m ch ofs v m' :
  Mem.store ch m bop ofs v = Some m' -> oop + 36 * n <= ofs -> ofs + size_chunk ch <= oop + 36 * alen ->
  pm_change bC bRs bop oop alen n m m'.
Proof.
  intros HS H1 H2. split; [|split].
  - intros ch' b o Hb _ _ Hr. apply (Mem.load_store_other _ _ _ _ _ _ HS).
    destruct Hr as [H|[H|H]]; [left; exact H|right; left; zi|right; right; zi].
  - intros b o k p _ Hp. eapply Mem.perm_store_1; [exact HS|exact Hp].
  - intros b Hb. eapply Mem.store_valid_block_1; [exact HS|exact Hb].
Qed.

Lemma pm_keeps n ents m m' : PM m n ents -> pm_change bC bRs bop oop alen n m m' -> PM m' n ents.
Proof.
  exact (pm_change_keeps bC bRs br or_ ba oa bl ol bop oop alen bsp osp len bb ob bs Halen Hsep
    Nba Nbl Nbsp Nbb NG NM Nbar Nblr Nbspr Nbbr NGr NMr NCr NRr NCa NRa NCl NRl NCo NRo NCs NRs NCb NRb
    NCG NRG NCM NRM n ents m m').
Qed.

(** [++result->len]: the entry written at index [n] is committed. *)
Lemma pn_s2_exec le m n ents (en : pn_ent) i :
  PM m n ents -> PL le i -> n < alen -> pn_ent_at bop oop m n en ->
  exists le' m',
    Clight2.exec_stmt sha_ge e le m pn_s2 E0 le' m' Out_normal /\
    PM m' (n + 1) (ents ++ [en]) /\ PL le' i /\ pn_fr m m'.
Proof.
  intros HM HP Hlt HEn. pose proof HM as (HN & HNa & Hop & Hlen & _ & _ & _ & _ & _ & _ & _ & VA2 & _).
  pose proof HP as (Hli & Hr & _).
  destruct (Mem.valid_access_store m Mint64 br (or_ + 8) (Vlong (Int64.repr (n + 1))) VA2) as [m' HS].
  set (le1 := PTree.set _t'12 (Vlong (Int64.repr n)) le).
  assert (K12 : pn_keeps _t'12) by pn_keeps_tac.
  assert (HP1 : PL le1 i) by (apply pl_set; assumption).
  exists le1, m'. split; [|split; [|split; [exact HP1|]]].
  - unfold pn_s2.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
    { apply exec_Sset. exact (pn_len_value e br or_ len Hor le m _ Hr Hlen). }
    eapply exec_Sassign with (v2 := Vlong (Int64.repr (n + 1))) (v := Vlong (Int64.repr (n + 1))).
    + exact (pn_len_lvalue e br or_ len Hor le1 m (proj1 (proj2 HP1))).
    + eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|apply eval_Econst_int|].
      rewrite <- (nd_i64_add n 1) by zi. reflexivity.
    + reflexivity.
    + eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
      rewrite Ptrofs.unsigned_repr by zi. exact HS.
  - exact (pm_commit bC bRs br or_ ba oa bl ol bop oop alen bsp osp len bb ob bs Hsep Nbar Nblr Nbspr Nbbr
      NGr NMr n ents en m m' HM Hlt HEn HS).
  - eapply pn_fr_store_res; [exact HS|zi|change (size_chunk Mint64) with 8; zi].
Qed.
End ParseIter.
