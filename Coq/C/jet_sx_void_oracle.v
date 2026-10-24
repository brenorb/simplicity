(** A checked summary of an actual internal void call. Every symbolic branch
    must return the same regions, no event and no value; otherwise it fails.
    This does not assume helper behavior or change any generated C body. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values Globalenvs.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem.
Require Import C.jet_secp_u128_word_sx.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint pv_list_beq {A} (eqb : A -> A -> bool) (xs ys : list A) : bool :=
 match xs,ys with [],[]=>true | x::xs,y::ys=>eqb x y && pv_list_beq eqb xs ys | _,_=>false end.
Lemma pv_list_beq_true A (eqb : A -> A -> bool) :
 (forall x y,eqb x y=true -> x=y) -> forall xs ys,pv_list_beq eqb xs ys=true -> xs=ys.
Proof.
 intros Equal xs;induction xs as [|x xs IH];intros [|y ys] E;try discriminate;[reflexivity|].
 cbn [pv_list_beq] in E;apply andb_true_iff in E as (H & T).
 rewrite (Equal x y H),(IH ys T);reflexivity.
Qed.
Definition pv_option_sx_beq a b := match a,b with
 | None,None=>true | Some x,Some y=>sx_beq x y | _,_=>false end.
Lemma pv_option_sx_beq_true a b : pv_option_sx_beq a b=true -> a=b.
Proof.
 destruct a,b;cbn [pv_option_sx_beq];try discriminate;[|reflexivity].
 intro E;apply sx_beq_true in E;subst;reflexivity.
Qed.
Definition pv_option_z_beq a b := match a,b with
 | None,None=>true | Some x,Some y=>Z.eqb x y | _,_=>false end.
Lemma pv_option_z_beq_true a b : pv_option_z_beq a b=true -> a=b.
Proof.
 destruct a,b;cbn [pv_option_z_beq];try discriminate;[|reflexivity].
 intro E;apply Z.eqb_eq in E;subst;reflexivity.
Qed.
Definition pv_cell_beq a b := Z.eqb (cofs a) (cofs b) && chunk_eqb (cchunk a) (cchunk b) &&
 pv_option_sx_beq (cval a) (cval b).
Lemma pv_cell_beq_true a b : pv_cell_beq a b=true -> a=b.
Proof.
 destruct a as [off ch value],b as [off' ch' value'];unfold pv_cell_beq;cbn [cofs cchunk cval];intro E.
 apply andb_true_iff in E as (E & V);apply andb_true_iff in E as (O & C).
 apply Z.eqb_eq in O;apply chunk_eqb_eq in C;apply pv_option_sx_beq_true in V;subst;reflexivity.
Qed.
Definition pv_region_beq a b := pv_list_beq pv_cell_beq (rcells a) (rcells b) &&
 Bool.eqb (rw a) (rw b) && pv_option_z_beq (rfree a) (rfree b).
Lemma pv_region_beq_true a b : pv_region_beq a b=true -> a=b.
Proof.
 destruct a as [cells write owned],b as [cells' write' owned'];
 unfold pv_region_beq;cbn [rcells rw rfree];intro E.
 apply andb_true_iff in E as (E & F);apply andb_true_iff in E as (C & W).
 apply (pv_list_beq_true _ _ pv_cell_beq_true) in C.
 apply Bool.eqb_prop in W;apply pv_option_z_beq_true in F;subst;reflexivity.
Qed.

Fixpoint pv_first_regs tree := match tree with
 | RDone st _=>sregs st | RIf _ a _=>pv_first_regs a end.
Fixpoint pv_tree_ok regs tree : bool := match tree with
 | RDone st ONormal=>pv_list_beq pv_region_beq (sregs st) regs &&
    match slog st,(stemps st)!1%positive with [],None=>true | _,_=>false end
 | RDone _ _=>false | RIf _ a b=>pv_tree_ok regs a && pv_tree_ok regs b end.
Lemma pv_tree_ok_sound regs tree : pv_tree_ok regs tree=true -> forall rho beta,
 sregs (fst (rsel rho beta tree))=regs /\ slog (fst (rsel rho beta tree))=[] /\
 (stemps (fst (rsel rho beta tree)))!1%positive=None /\ snd (rsel rho beta tree)=ONormal.
Proof.
 induction tree as [st out|c a IHa b IHb];cbn [pv_tree_ok];intro E.
 - destruct out;try discriminate.
   apply andb_true_iff in E as (Regs & Empty).
   apply (pv_list_beq_true _ _ pv_region_beq_true) in Regs.
   destruct (slog st) eqn:Log;destruct ((stemps st)!1%positive) eqn:Return;try discriminate.
   intros;cbn [rsel fst snd];repeat split;assumption || reflexivity.
 - apply andb_true_iff in E as (A & B);intros rho beta;cbn [rsel].
   destruct (truth rho beta c);[apply IHa|apply IHb];assumption.
Qed.

Lemma pv_tree_no_log regs tree : pv_tree_ok regs tree=true -> leaves_log_nil tree=true.
Proof.
 induction tree as [st out|c a IHa b IHb];cbn [pv_tree_ok leaves_log_nil];intro Check.
 - destruct out;try discriminate;apply andb_true_iff in Check as (_ & E).
   destruct (slog st);[reflexivity|discriminate].
 - apply andb_true_iff in Check as (A & B);rewrite (IHa A),(IHb B);reflexivity.
Qed.

Definition pure_void_oracle (ge : genv) functions fuel fd : oracle := fun base log args regs=>
 match xfun (genv_cenv ge) [] (int_table functions) fuel fd args regs [] 0 with
 | Some tree=>let out:=pv_first_regs tree in
   if pv_tree_ok out tree then Some (out,None,0%nat,0%nat,[]) else None
 | None=>None end.

Theorem pure_void_oracle_correct (ge : genv) (functions : list (ident * function))
 (Linked : forall id fd,In (id,fd) functions -> exists b,
  Genv.find_symbol ge id=Some b /\ Genv.find_funct_ptr ge b=Some (Internal fd)) fuel fd :
 oracle_ok ge (fun _ _=>True) (fun _ _ _=>True) (fun _=>False) fd
  (pure_void_oracle ge functions fuel fd).
Proof.
 unfold oracle_ok,pure_void_oracle.
 intros base args regs regs' v tag cnt ea log rho beta m Run Rep Sep Inv Sol Event.
 destruct (xfun (genv_cenv ge) [] (int_table functions) fuel fd args regs [] 0) as [tree|] eqn:Exec;
  [|discriminate].
 destruct (pv_tree_ok (pv_first_regs tree) tree) eqn:Check;[|discriminate].
 inversion Run;subst regs' v tag cnt ea.
 destruct (pv_tree_ok_sound _ _ Check rho (lay beta)) as (Regs & Empty & Ret & Normal).
 pose proof (pv_tree_no_log _ _ Check) as NoLog.
 destruct (xfun_pure ge functions Linked fuel fd args regs 0 tree Exec NoLog rho beta m Rep)
  as (mf & value & Call & Out & Return & Shape & Frame).
 rewrite Ret in Return;subst value;rewrite Regs in Out,Shape.
 exists mf,Vundef;split;[exact Call|];split;[exact Out|];split;[exact I|];
 split;[exact Shape|];split;[reflexivity|].
 eapply lframe_implies;[exact Frame|];intros b ofs (_ & Outside & _) _;exact Outside.
Qed.
