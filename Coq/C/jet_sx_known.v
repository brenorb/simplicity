(** Constant-condition pruning justified against the original Clight statements. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition known_truth c : option bool := match c with
 | XIc i=>Some (negb (Int.eq i Int.zero))
 | XLnz (XLc l)=>Some (negb (Int64.eq l Int64.zero))
 | _=>None end.
Lemma known_truth_sound c b : known_truth c=Some b -> forall rho beta,truth rho beta c=b.
Proof.
 destruct c;cbn [known_truth];try discriminate.
 - intro E;injection E as <-;reflexivity.
 - destruct c;cbn [known_truth];try discriminate.
   intro E;injection E as <-;intros;unfold truth;cbn [den il ii b2i];
   destruct (Int64.eq l Int64.zero);reflexivity.
Qed.

Section COMPUTE.
Variable ce : composite_env.
Variable gv : venv.
Variable fns : list (ident*fentry).
Variable fuel : nat.
Fixpoint known_stmt (ve : venv) (st : sstate) (s : statement) {struct s} : option res :=
 match s with
 | Ssequence a b=>match known_stmt ve st a with
    | Some r=>tbind r (fun st' out=>match out with
       | ONormal=>known_stmt ve st' b | _=>Some (RDone st' out) end)
    | None=>None end
 | Sifthenelse a b c=>match xexpr ce ve gv st a with
    | Some x=>match xbool x (typeof a) with
       | Some cond=>match known_truth cond with
          | Some choose=>if choose then known_stmt ve st b else known_stmt ve st c
          | None=>xstmt ce gv fns fuel ve st s end
       | None=>None end
    | None=>None end
 | _=>xstmt ce gv fns fuel ve st s end.

Lemma known_stmt_lext s : forall ve st rr,known_stmt ve st s=Some rr ->
 forall rho beta,lext rho beta (slog st) rr.
Proof.
 induction s;intros ve st rr H rho beta;cbn [known_stmt] in H;
 try solve [eapply xstmt_lext;exact H].
 - destruct (known_stmt ve st s1) as [r1|] eqn:E1;[|discriminate].
   destruct (tbind_sel rho beta _ _ _ H) as (rk & Hk & Hsel).
   pose proof (IHs1 _ _ _ E1 rho beta) as H1.
   eapply lext_sel;[exact Hsel|].
   destruct (rsel rho beta r1) as [st1 out1] eqn:Es;cbn [fst snd] in Hk.
   assert (Keep : forall out,lext rho beta (slog st) (RDone st1 out)).
   { intro out;unfold lext in *;cbn [rsel fst];rewrite Es in H1;exact H1. }
   destruct out1;try (inversion Hk;subst rk;apply Keep).
   eapply lext_trans;[exact H1|];rewrite Es;exact (IHs2 _ _ _ Hk rho beta).
 - destruct (xexpr ce ve gv st e) as [x|];[|discriminate].
   destruct (xbool x (typeof e)) as [c|];[|discriminate].
   destruct (known_truth c) as [b|];[destruct b;[eapply IHs1|eapply IHs2];exact H|].
   eapply xstmt_lext;exact H.
Qed.
End COMPUTE.

Section SOUND.
Variable ge : genv.
Variable gv : venv.
Variable fns : list (ident*fentry).
Variable ev_ok : (nat->int64)->event->Prop.
Variable inv : (nat->int64)->list event->mem->Prop.
Variable ext : block->Prop.
Hypothesis Stable : forall rho log m m',inv rho log m -> lframe (fun b _=>ext b) m m' -> inv rho log m'.
Hypothesis Valid : forall rho log m b,inv rho log m -> ext b -> Mem.valid_block m b.
Hypothesis Linked : forall id ent,flookup fns id=Some ent ->
 (exists b,Genv.find_symbol ge id=Some b /\ Genv.find_funct_ptr ge b=Some (Internal (fentry_fd ent))) /\
 match ent with FInt _=>True | FOra fd o=>oracle_ok ge ev_ok inv ext fd o end.
Notation ce := (genv_cenv ge).
Local Ltac known_outinv Hom out := destruct out as [| | |[[? ?]|]];cbn [outmatch] in Hom;try contradiction.

Theorem known_stmt_sound fuel : sound_rec ge gv ev_ok inv ext (known_stmt ce gv fns fuel).
Proof.
 intros ve st s;revert ve st.
 induction s;intros ve st rr H rho beta env0 le m Rep Temps Env Globals Sep Inv Sol;
 cbn [known_stmt] in H;
 try solve [eapply (xstmt_sound ge gv fns ev_ok inv ext Stable Valid Linked fuel);eauto].
 - destruct (known_stmt ce gv fns fuel ve st s1) as [r1|] eqn:E1;[|discriminate].
   destruct (tbind_sel rho (lay beta) _ _ _ H) as (rk & Hk & Hsel);rewrite Hsel in Sol.
   assert (Sol1 : solves ev_ok rho (slog (fst (rsel rho (lay beta) r1)))).
   { destruct (rsel rho (lay beta) r1) as [st1 out1];cbn [fst snd] in *.
     destruct out1;try (inversion Hk;subst rk;exact Sol).
     destruct (known_stmt_lext ce gv fns fuel s2 _ _ _ Hk rho (lay beta)) as (suffix & Log).
     cbn [fst] in Log;rewrite Log in Sol;exact (proj1 (solves_app _ _ _ _ Sol)). }
   destruct (IHs1 _ _ _ E1 rho beta env0 le m Rep Temps Env Globals Sep Inv Sol1)
    as (l1 & m1 & out1 & Exec1 & Post1).
   pose proof Post1 as (R1 & T1 & O1 & S1 & I1 & F1).
   destruct (rsel rho (lay beta) r1) as [st1 o1] eqn:Es;cbn [fst snd] in Hk,R1,T1,O1,S1,I1.
   destruct o1.
   + known_outinv O1 out1.
     destruct (IHs2 _ _ _ Hk rho beta env0 l1 m1 R1 T1 Env Globals Sep I1 Sol)
      as (l2 & m2 & out2 & Exec2 & Post2).
     exists l2,m2,out2;split.
     * change E0 with (E0 ** E0);eapply exec_Sseq_1;eauto.
     * eapply post_sel;[exact Hsel|];eapply post_trans;[exact Post1|];rewrite Es;exact Post2.
   + inversion Hk;subst rk;exists l1,m1,out1;split.
     * eapply exec_Sseq_2;[exact Exec1|];known_outinv O1 out1;discriminate.
     * eapply post_sel;[rewrite Hsel;cbn [rsel fst snd];symmetry;exact Es|exact Post1].
   + inversion Hk;subst rk;exists l1,m1,out1;split.
     * eapply exec_Sseq_2;[exact Exec1|];known_outinv O1 out1;discriminate.
     * eapply post_sel;[rewrite Hsel;cbn [rsel fst snd];symmetry;exact Es|exact Post1].
   + inversion Hk;subst rk;exists l1,m1,out1;split.
     * eapply exec_Sseq_2;[exact Exec1|];destruct v as [[? ?]|];known_outinv O1 out1;discriminate.
     * eapply post_sel;[rewrite Hsel;cbn [rsel fst snd];symmetry;exact Es|exact Post1].
 - destruct (xexpr ce ve gv st e) as [x|] eqn:Expr;[|discriminate].
   destruct (xbool x (typeof e)) as [c|] eqn:Bool;[|discriminate].
   destruct (known_truth c) as [b|] eqn:Known.
   2:{ eapply (xstmt_sound ge gv fns ev_ok inv ext Stable Valid Linked fuel);exact H || assumption. }
   pose proof (known_truth_sound c b Known rho (lay beta)) as Choice.
   assert (ExprC : eval_expr ge env0 le m e (den rho (lay beta) x)).
   { eapply xexpr_sound;eauto;exact (proj1 Globals). }
   pose proof (xbool_sound rho (lay beta) x (typeof e) c m Bool) as BoolC;rewrite Choice in BoolC.
   destruct b.
   + destruct (IHs1 _ _ _ H rho beta env0 le m Rep Temps Env Globals Sep Inv Sol)
      as (lf & mf & out & Exec & Post).
     exists lf,mf,out;split;[eapply exec_Sifthenelse;[exact ExprC|exact BoolC|exact Exec]|exact Post].
   + destruct (IHs2 _ _ _ H rho beta env0 le m Rep Temps Env Globals Sep Inv Sol)
      as (lf & mf & out & Exec & Post).
     exists lf,mf,out;split;[eapply exec_Sifthenelse;[exact ExprC|exact BoolC|exact Exec]|exact Post].
Qed.
End SOUND.

Definition known_fun ce gv fns fuel fd xs regs log nv :=
 xfun_with ce (known_stmt ce gv fns fuel) fd xs regs log nv
  (xcall_ret (Some 1%positive) (PTree.empty sx) (length regs) (fn_return fd)).

Theorem known_fun_sound (ge : genv) fns
 (Linked : forall id ent,flookup fns id=Some ent ->
  (exists b,Genv.find_symbol ge id=Some b /\ Genv.find_funct_ptr ge b=Some (Internal (fentry_fd ent))) /\
  match ent with FInt _=>True | FOra fd o=>oracle_ok ge (fun _ _=>True) (fun _ _ _=>True) (fun _=>False) fd o end)
 fuel fd xs regs nv rr : known_fun (genv_cenv ge) [] fns fuel fd xs regs [] nv=Some rr ->
 forall rho beta m,rep rho beta regs m -> exists mf vres,
 Clight2.eval_funcall ge m (Internal fd) (map (den rho (lay beta)) xs) E0 mf vres /\
 rep rho beta (sregs (fst (rsel rho (lay beta) rr))) mf /\
 match (stemps (fst (rsel rho (lay beta) rr)))!1%positive with
 | Some x=>vres=den rho (lay beta) x | None=>vres=Vundef end /\
 map rshape (sregs (fst (rsel rho (lay beta) rr)))=map rshape regs /\
 lframe (fun b ofs=>~foot beta (map rshape regs) b ofs) m mf.
Proof.
 intros Run rho beta m Rep.
 assert (Stable : forall (r : nat->int64) (log : list event) (ma mb : mem),
  True -> lframe (fun (_ : block) (_ : Z)=>False) ma mb -> True) by auto.
 assert (Valid : forall (r : nat->int64) (log : list event) (ma : mem) b,
  True -> False -> Mem.valid_block ma b) by contradiction.
 destruct (xfun_sound ge [] (fun _ _=>True) (fun _ _ _=>True) (fun _=>False) Stable Valid _
  (known_stmt_sound ge [] fns (fun _ _=>True) (fun _ _ _=>True) (fun _=>False) Stable Valid Linked fuel)
  fd xs regs [] nv (PTree.empty sx) (Some 1%positive) rr Run rho beta m Rep)
  as (mf & vres & Call & Out & (value & Temps & Return) & Normal & Shape & Inv & Frame).
 - split;intros;discriminate.
 - intros r Hr [].
 - exact I.
 - apply Forall_forall;intros;exact I.
 - exists mf,vres;split;[exact Call|];split;[exact Out|];split.
   + rewrite Temps;destruct value as [x|];unfold set_opt;
     [rewrite PTree.gss;exact Return|rewrite PTree.grs;exact Return].
   + split;[exact Shape|];eapply lframe_implies;[exact Frame|];
     intros b ofs Outside ValidBlock;split;[exact ValidBlock|];split;[exact Outside|tauto].
Qed.
