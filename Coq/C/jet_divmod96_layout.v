(** Total execution of the actual LP64 div_mod_96_64 helper from writable,
    nonoverlapping eight-byte output slots. Not a public jet specification. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_writeBit C.jet_divmod96_value C.jet_divmod96_init.
Require Import C.jet_divmod96_expr C.jet_divmod96_init_exec C.jet_divmod96_init_layout.
Require Import C.jet_divmod96_loop C.jet_divmod96_loop_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition divmod96_final_stmt :=
  Sassign (Ederef (Etempvar _r (tptr tulong)) tulong) divmod96_final_expr.
Definition divmod96_debug_first :=
  match f_div_mod_96_64.(fn_body) with Ssequence s _ => s | _ => Sskip end.
Definition divmod96_debug_second :=
  match f_div_mod_96_64.(fn_body) with
  | Ssequence _ (Ssequence s _) => s | _ => Sskip end.

Lemma divmod96_body : f_div_mod_96_64.(fn_body) =
  Ssequence divmod96_debug_first (Ssequence divmod96_debug_second
    (divmod96_work (Ssequence divmod96_loop_stmt divmod96_final_stmt))).
Proof. reflexivity. Qed.

Lemma exec_divmod96_body e le m bq qo br ro ah al b :
  le!_q = Some (Vptr bq qo) -> le!_r = Some (Vptr br ro) ->
  le!_ah = Some (Vlong ah) -> le!_al = Some (Vlong al) -> le!_b = Some (Vlong b) ->
  Int64.modulus <= 2 * Int64.unsigned b -> Int64.unsigned ah < Int64.unsigned b ->
  Int64.unsigned al < divmod96_radix ->
  Mem.valid_access m Mint64 bq (Ptrofs.unsigned qo) Writable ->
  Mem.valid_access m Mint64 br (Ptrofs.unsigned ro) Writable ->
  (bq <> br \/ Ptrofs.unsigned qo + 8 <= Ptrofs.unsigned ro \/
    Ptrofs.unsigned ro + 8 <= Ptrofs.unsigned qo) ->
  exists mf lef qf rf,
    Clight2.exec_stmt ge0 e le m f_div_mod_96_64.(fn_body) E0 lef mf Out_normal /\
    Mem.load Mint64 mf bq (Ptrofs.unsigned qo) = Some (Vlong qf) /\
    Mem.load Mint64 mf br (Ptrofs.unsigned ro) = Some (Vlong rf) /\
    0 <= Int64.unsigned qf < divmod96_radix /\
    0 <= Int64.unsigned rf < Int64.unsigned b /\
    Int64.unsigned ah * divmod96_radix + Int64.unsigned al =
      Int64.unsigned qf * Int64.unsigned b + Int64.unsigned rf /\
    (forall chunk bb addr,
      (bb <> bq \/ addr + size_chunk chunk <= Ptrofs.unsigned qo \/ Ptrofs.unsigned qo + 8 <= addr) ->
      (bb <> br \/ addr + size_chunk chunk <= Ptrofs.unsigned ro \/ Ptrofs.unsigned ro + 8 <= addr) ->
      Mem.load chunk mf bb addr = Mem.load chunk m bb addr) /\
    (forall bb addr kind p, Mem.perm m bb addr kind p -> Mem.perm mf bb addr kind p) /\
    Mem.nextblock mf = Mem.nextblock m.
Proof.
  intros HQ HR HA HAL HB Hnorm Hah Hal HPQ HPR Hsep.
  destruct (divmod96_denominator_parts b Hnorm) as [Hbh [Hbl Hparts]].
  assert (HNZ : Int64.eq (divmod96_high b) Int64.zero = Datatypes.false).
  { apply Int64.eq_false. intros HE. rewrite HE in Hbh. change (0 < 0 < divmod96_radix) in Hbh. lia. }
  set (q0 := divmod96_clamp ah (divmod96_high b)).
  destruct (Mem.valid_access_store m Mint64 bq (Ptrofs.unsigned qo) (Vlong q0) HPQ) as [mi HstoreQ].
  assert (HLQ : Mem.load Mint64 mi bq (Ptrofs.unsigned qo) = Some (Vlong q0)).
  { rewrite (Mem.load_store_same Mint64 m bq (Ptrofs.unsigned qo) (Vlong q0) mi HstoreQ). reflexivity. }
  assert (HPQi : Mem.valid_access mi Mint64 bq (Ptrofs.unsigned qo) Writable).
  { eapply Mem.store_valid_access_1; eauto. }
  destruct (divmod96_initial_invariant ah al b Hnorm Hah Hal) as [Hinv Hlower].
  pose proof (divmod96_initial_loop_env le bq qo ah al b HQ HAL) as Henv.
  destruct (eval_divmod96_loop_layout 2 e (divmod96_init_env le ah b) mi bq qo
    (Int64.unsigned ah) al (divmod96_high b) (divmod96_low b) q0
    (divmod96_initial_rh ah b) (divmod96_initial_d ah b)
    (proj2 (Int64.unsigned_range ah)) Hbh (proj2 Hbl) Hal Henv HLQ HPQi Hinv Hlower)
    as (ml & lel & qf & rhf & df & Hloop & HenvFinal & HloadQ & HinvFinal & Hnonneg &
      Htemps & Hloads & Hperms & Hnext).
  destruct HenvFinal as (HQf & HRHf & HBHf & HALf & HDf & HBLf).
  destruct HinvFinal as (Hqf & Hbalance & Hdf & Hupper).
  assert (HD : divmod96_denominator (divmod96_high b) (divmod96_low b) = Int64.unsigned b).
  { unfold divmod96_denominator. symmetry; exact Hparts. }
  rewrite HD in Hupper.
  pose proof (Int64.unsigned_range b) as HBrange.
  set (delta := divmod96_delta rhf al df).
  assert (Hdrange : 0 <= delta <= Int64.max_unsigned).
  { unfold delta. change Int64.modulus with (Int64.max_unsigned + 1) in HBrange. lia. }
  set (rf := Int64.repr delta).
  assert (HRvalue : Int64.unsigned rf = delta) by (unfold rf; apply Int64.unsigned_repr; exact Hdrange).
  assert (HRptr : lel!_r = Some (Vptr br ro)).
  { rewrite Htemps by discriminate. rewrite divmod96_initial_r_pointer. exact HR. }
  assert (HPRi : Mem.valid_access mi Mint64 br (Ptrofs.unsigned ro) Writable).
  { eapply Mem.store_valid_access_1; eauto. }
  assert (HPRl : Mem.valid_access ml Mint64 br (Ptrofs.unsigned ro) Writable).
  { destruct HPRi as [HP Halign]. split; [|exact Halign].
    intros addr Haddr. apply Hperms. apply HP. exact Haddr. }
  destruct (Mem.valid_access_store ml Mint64 br (Ptrofs.unsigned ro) (Vlong rf) HPRl) as [mf HstoreR].
  assert (Hfinal : Clight2.exec_stmt ge0 e lel ml divmod96_final_stmt E0 lel mf Out_normal).
  { eapply exec_Sassign with (loc := br) (ofs := ro) (bf := Full) (v2 := Vlong rf) (v := Vlong rf).
    - apply eval_Ederef. apply eval_Etempvar; exact HRptr.
    - apply eval_divmod96_final_expr; assumption.
    - reflexivity.
    - apply assign_loc_value with (chunk := Mint64); [reflexivity|exact HstoreR]. }
  exists mf, lel, qf, rf. split.
  - rewrite divmod96_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m).
    + apply exec_writeBit_debug_loop.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m).
      * apply exec_writeBit_debug_loop.
      * eapply exec_divmod96_initialization; try eassumption.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eassumption.
  - split.
    + erewrite Mem.load_store_other; [exact HloadQ|exact HstoreR|exact Hsep].
    + split.
      * rewrite (Mem.load_store_same Mint64 ml br (Ptrofs.unsigned ro) (Vlong rf) mf HstoreR). reflexivity.
      * split; [exact Hqf|]. split; [rewrite HRvalue; unfold delta; lia|].
        split.
        -- rewrite HRvalue. unfold delta, divmod96_delta. rewrite <- HD.
           unfold divmod96_denominator. nia.
        -- split.
           ++ intros chunk bb addr HoutQ HoutR.
              erewrite Mem.load_store_other; [|exact HstoreR|exact HoutR].
              rewrite Hloads by exact HoutQ.
              erewrite Mem.load_store_other; [reflexivity|exact HstoreQ|exact HoutQ].
           ++ split.
              ** intros bb addr kind p HP. eapply Mem.perm_store_1; [exact HstoreR|].
                 apply Hperms. eapply Mem.perm_store_1; eauto.
              ** rewrite (Mem.nextblock_store _ _ _ _ _ _ HstoreR), Hnext.
                 eapply Mem.nextblock_store; exact HstoreQ.
Qed.

Definition divmod96_entry_env bq qo br ro ah al b :=
  PTree.set _b (Vlong b) (PTree.set _al (Vlong al) (PTree.set _ah (Vlong ah)
    (PTree.set _r (Vptr br ro) (PTree.set _q (Vptr bq qo)
      (create_undef_temps f_div_mod_96_64.(fn_temps)))))).

Lemma divmod96_entry m bq qo br ro ah al b :
  function_entry2 ge0 f_div_mod_96_64 [Vptr bq qo; Vptr br ro; Vlong ah; Vlong al; Vlong b]
    m empty_env (divmod96_entry_env bq qo br ro ah al b) m.
Proof.
  constructor.
  - constructor.
  - vm_compute. repeat (apply list_norepet_cons; [simpl; intuition discriminate|]). constructor.
  - intros id1 id2 H1 H2 Heq. cbn in H1, H2. subst id2.
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
      vm_compute in *; congruence.
  - constructor.
  - reflexivity.
Qed.

Theorem eval_divmod96_layout m bq qo br ro ah al b :
  Int64.modulus <= 2 * Int64.unsigned b -> Int64.unsigned ah < Int64.unsigned b ->
  Int64.unsigned al < divmod96_radix ->
  Mem.valid_access m Mint64 bq (Ptrofs.unsigned qo) Writable ->
  Mem.valid_access m Mint64 br (Ptrofs.unsigned ro) Writable ->
  (bq <> br \/ Ptrofs.unsigned qo + 8 <= Ptrofs.unsigned ro \/
    Ptrofs.unsigned ro + 8 <= Ptrofs.unsigned qo) ->
  exists mf qf rf,
    Clight2.eval_funcall ge0 m (Internal f_div_mod_96_64)
      [Vptr bq qo; Vptr br ro; Vlong ah; Vlong al; Vlong b] E0 mf Vundef /\
    Mem.load Mint64 mf bq (Ptrofs.unsigned qo) = Some (Vlong qf) /\
    Mem.load Mint64 mf br (Ptrofs.unsigned ro) = Some (Vlong rf) /\
    0 <= Int64.unsigned qf < divmod96_radix /\
    0 <= Int64.unsigned rf < Int64.unsigned b /\
    Int64.unsigned ah * divmod96_radix + Int64.unsigned al =
      Int64.unsigned qf * Int64.unsigned b + Int64.unsigned rf /\
    (forall chunk bb addr,
      (bb <> bq \/ addr + size_chunk chunk <= Ptrofs.unsigned qo \/ Ptrofs.unsigned qo + 8 <= addr) ->
      (bb <> br \/ addr + size_chunk chunk <= Ptrofs.unsigned ro \/ Ptrofs.unsigned ro + 8 <= addr) ->
      Mem.load chunk mf bb addr = Mem.load chunk m bb addr) /\
    (forall bb addr kind p, Mem.perm m bb addr kind p -> Mem.perm mf bb addr kind p) /\
    Mem.nextblock mf = Mem.nextblock m.
Proof.
  intros Hnorm Hah Hal HPQ HPR Hsep.
  destruct (exec_divmod96_body empty_env (divmod96_entry_env bq qo br ro ah al b) m
    bq qo br ro ah al b ltac:(unfold divmod96_entry_env; rewrite !PTree.gso by discriminate; apply PTree.gss)
    ltac:(unfold divmod96_entry_env; rewrite !PTree.gso by discriminate; apply PTree.gss)
    ltac:(unfold divmod96_entry_env; rewrite !PTree.gso by discriminate; apply PTree.gss)
    ltac:(unfold divmod96_entry_env; rewrite !PTree.gso by discriminate; apply PTree.gss)
    ltac:(unfold divmod96_entry_env; apply PTree.gss) Hnorm Hah Hal HPQ HPR Hsep)
    as (mf & lef & qf & rf & Hbody & HQ & HR & Hq & Hr & Hbalance & Hloads & Hperms & Hnext).
  exists mf, qf, rf. split.
  - eapply eval_funcall_internal with (e := empty_env)
      (le1 := divmod96_entry_env bq qo br ro ah al b) (le2 := lef)
      (m1 := m) (m2 := mf) (out := Out_normal).
    + apply divmod96_entry.
    + exact Hbody.
    + reflexivity.
    + reflexivity.
  - tauto.
Qed.
