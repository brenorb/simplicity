(** Compose the ten actual copy/square/multiply stages, preserving all local
    fields needed by subsequent stages. No intermediate execution is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_curve_statements
 C.jet_secp_curve_frame C.jet_secp_root_square_loop C.jet_secp_root_stage.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge root_stage_words.

Definition root_private_ids := [_x2;_x3;_x6;_x9;_x11;_x22;_x44;_x88;_x176;_x220;_x223;_t1].
Definition root_locals_owned (e : env) m := forall id, In id root_private_ids ->
 exists b, e!id=Some (b,curve_fe_type) /\ Mem.range_perm m b 0 40 Cur Freeable.
Definition root_locals_separated (e : env) := forall i j bi bj,
 In i root_private_ids -> In j root_private_ids ->
 e!i=Some (bi,curve_fe_type) -> e!j=Some (bj,curve_fe_type) -> i<>j -> bi<>bj.
Definition root_values_at (e : env) m (s : PTree.t (nat -> int64)) := forall id w,
 s!id=Some w -> In id root_private_ids /\ square_input_bounds w /\
 exists b, e!id=Some (b,curve_fe_type) /\ fe_at m b 0 (words5 w).
Definition root_chain_frame (e : env) b (_ : Z) := forall id,
 In id root_private_ids -> e!id<>Some (b,curve_fe_type).

Theorem exec_root_stage_preserves n dst src rhs e le m s w v :
 Z.of_nat n<=88 -> In dst root_private_ids -> dst<>src -> dst<>rhs ->
 e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> root_locals_separated e ->
 root_locals_owned e m -> root_values_at e m s -> s!src=Some w -> s!rhs=Some v ->
 exists mf lef,
 Clight2.exec_stmt secp_ge e le m (root_stage n dst src rhs) E0 lef mf Out_normal /\
 root_locals_owned e mf /\ root_values_at e mf (PTree.set dst (root_stage_words n w v) s) /\
 (forall k,k<>_j -> lef!k=le!k) /\ lframe (root_chain_frame e) m mf.
Proof.
 intros HN ID DS DV EQ EM Sep Owned Store SW SV.
 destruct (Store src w SW) as (IS & BW & bs & ES & W).
 destruct (Store rhs v SV) as (IV & BV & bv & EV & V).
 destruct (Owned dst ID) as (bd & ED & FD).
 destruct (Owned src IS) as (bs' & ES' & FS);rewrite ES in ES';injection ES' as <-.
 destruct (Owned rhs IV) as (bv' & EV' & FV);rewrite EV in EV';injection EV' as <-.
 assert (DBS : bd<>bs) by (exact (Sep dst src bd bs ID IS ED ES DS)).
 assert (DBV : bd<>bv) by (exact (Sep dst rhs bd bv ID IV ED EV DV)).
 destruct (exec_root_stage_owned n dst src rhs e le m bd bs bv w v
   HN ED ES EV EQ EM DBS DBV BW BV W V FD FS FV)
   as (mf & lef & Run & WF & WSF & VF & FDF & FSF & FVF & BF & Value & JF & Temps & Frame).
 assert (KeepOwned : root_locals_owned e mf).
 { intros id HI;destruct (Pos.eq_dec id dst) as [->|ND].
   - exists bd;split;assumption.
   - destruct (Pos.eq_dec id rhs) as [->|NV].
     + exists bv;split;assumption.
     + destruct (Owned id HI) as (b & EB & FB);exists b;split;[exact EB|].
       eapply curve_keep_free;[lia|exact FB|exact Frame|];intro pos;split;
       [exact (Sep id dst b bd HI ID EB ED ND)|exact (Sep id rhs b bv HI IV EB EV NV)]. }
 assert (KeepStore : root_values_at e mf (PTree.set dst (root_stage_words n w v) s)).
 { intros id u HU;destruct (Pos.eq_dec id dst) as [->|ND].
   - rewrite PTree.gss in HU;injection HU as <-;split;[exact ID|];split;[exact BF|].
     exists bd;split;assumption.
   - rewrite PTree.gso in HU by exact ND.
     destruct (Store id u HU) as (HI & BU & b & EB & U);split;[exact HI|];split;[exact BU|].
     destruct (Pos.eq_dec id rhs) as [->|NV].
     + rewrite SV in HU;injection HU as <-;rewrite EV in EB;injection EB as <-.
       exists bv;split;assumption.
     + exists b;split;[exact EB|].
       eapply curve_keep_field_range;[reflexivity|exact U|exact Frame|];intros;split;
       [exact (Sep id dst b bd HI ID EB ED ND)|exact (Sep id rhs b bv HI IV EB EV NV)]. }
 exists mf,lef;split;[exact Run|];split;[exact KeepOwned|];split;[exact KeepStore|];split;[exact Temps|].
 eapply lframe_implies;[exact Frame|];intros b pos HO _;split;intro HE;subst b;
   [apply (HO dst ID);exact ED|apply (HO rhs IV);exact EV].
Qed.

Definition root_chain_steps : list (nat*ident*ident*ident) :=
 [(3%nat,_x6,_x3,_x3);(3%nat,_x9,_x6,_x3);(2%nat,_x11,_x9,_x2);
  (11%nat,_x22,_x11,_x11);(22%nat,_x44,_x22,_x22);(44%nat,_x88,_x44,_x44);
  (88%nat,_x176,_x88,_x88);(44%nat,_x220,_x176,_x44);(3%nat,_x223,_x220,_x3);
  (23%nat,_t1,_x223,_x22)].
Definition root_chain_step_valid (i : nat*ident*ident*ident) :=
 let '(n,d,s,r) := i in Z.of_nat n<=88 /\ In d root_private_ids /\ d<>s /\ d<>r.
Definition root_chain_update (i : nat*ident*ident*ident) (s : PTree.t (nat -> int64)) :=
 let '(n,d,a,b) := i in match s!a,s!b with
 | Some w,Some v => Some (PTree.set d (root_stage_words n w v) s)
 | _,_ => None end.
Fixpoint root_chain_run steps s := match steps with
 | [] => Some s
 | i::tail => match root_chain_update i s with Some next => root_chain_run tail next | None => None end
 end.
Fixpoint root_chain_body steps last := match steps with
 | [] => last
 | (n,d,s,r)::tail => Ssequence (root_stage_copy d s)
    (Ssequence (root_square_for d (Z.of_nat n)) (Ssequence (root_stage_mul d r) (root_chain_body tail last)))
 end.

Lemma root_sequence_normal_inv e le m a b lef mf :
 Clight2.exec_stmt secp_ge e le m (Ssequence a b) E0 lef mf Out_normal ->
 exists lei mi, Clight2.exec_stmt secp_ge e le m a E0 lei mi Out_normal /\
 Clight2.exec_stmt secp_ge e lei mi b E0 lef mf Out_normal.
Proof.
 intro HS;inversion HS;subst;try contradiction.
 match goal with HTrace : ?t1 ** ?t2=E0 |- _ =>
   apply app_eq_nil in HTrace;destruct HTrace;subst end.
 eauto.
Qed.

Lemma exec_root_stage_then n dst src rhs e le m lei mi lef mf last out :
 Clight2.exec_stmt secp_ge e le m (root_stage n dst src rhs) E0 lei mi Out_normal ->
 Clight2.exec_stmt secp_ge e lei mi last E0 lef mf out ->
 Clight2.exec_stmt secp_ge e le m
  (Ssequence (root_stage_copy dst src) (Ssequence (root_square_for dst (Z.of_nat n))
    (Ssequence (root_stage_mul dst rhs) last))) E0 lef mf out.
Proof.
 intros HS HT;unfold root_stage in HS.
 destruct (root_sequence_normal_inv _ _ _ _ _ _ _ HS) as (le1 & m1 & Copy & Rest).
 destruct (root_sequence_normal_inv _ _ _ _ _ _ _ Rest) as (le2 & m2 & Loop & Mul).
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Copy|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Loop|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);eassumption.
Qed.

Theorem exec_root_chain_run steps : forall e le m s sf,
 Forall root_chain_step_valid steps -> e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None ->
 root_locals_separated e -> root_locals_owned e m -> root_values_at e m s ->
 root_chain_run steps s=Some sf -> exists mf lef,
 Clight2.exec_stmt secp_ge e le m (root_chain_body steps Sskip) E0 lef mf Out_normal /\
 root_locals_owned e mf /\ root_values_at e mf sf /\
 (forall k,k<>_j -> lef!k=le!k) /\ lframe (root_chain_frame e) m mf.
Proof.
 induction steps as [|[[[n d] src] rhs] tail IH];intros e le m s sf Valid EQ EM Sep Owned Store Run.
 - cbn [root_chain_run] in Run;injection Run as <-;exists m,le;split;[constructor|].
   split;[exact Owned|];split;[exact Store|];split;[intros;reflexivity|apply lframe_refl].
 - inversion Valid as [|ins rest Head Tail];subst ins rest.
   destruct Head as (HN & ID & DS & DV).
   cbn [root_chain_run root_chain_update] in Run.
   destruct (s!src) as [w|] eqn:SW;[|discriminate].
   destruct (s!rhs) as [v|] eqn:SV;[|discriminate].
   destruct (exec_root_stage_preserves n d src rhs e le m s w v HN ID DS DV EQ EM Sep Owned Store SW SV)
     as (mi & lei & Stage & OwnedI & StoreI & TempsI & FrameI).
   destruct (IH e lei mi _ sf Tail EQ EM Sep OwnedI StoreI Run)
     as (mf & lef & Rest & OwnedF & StoreF & TempsF & FrameF).
   exists mf,lef;split.
   + cbn [root_chain_body];eapply exec_root_stage_then;eassumption.
   + split;[exact OwnedF|];split;[exact StoreF|];split.
     * intros k HK;rewrite TempsF,TempsI by exact HK;reflexivity.
     * eapply lframe_trans;eassumption.
Qed.

Lemma root_chain_steps_valid : Forall root_chain_step_valid root_chain_steps.
Proof.
 apply Forall_forall;intros ins HI;cbn [root_chain_steps In] in HI.
 repeat destruct HI as [<-|HI];try contradiction.
 all: cbn [root_chain_step_valid];split;[lia|];split.
 all: try (unfold root_private_ids;repeat (first [left;reflexivity|right])).
 all: split;discriminate.
Qed.
Definition root_chain_initial (w2 w3 : nat -> int64) :=
 PTree.set _x2 w2 (PTree.set _x3 w3 (PTree.empty (nat -> int64))).
Definition root_chain_final w2 w3 :=
 match root_chain_run root_chain_steps (root_chain_initial w2 w3) with
 | Some sf => sf | None => PTree.empty (nat -> int64) end.
Lemma root_chain_runs w2 w3 :
 root_chain_run root_chain_steps (root_chain_initial w2 w3)=Some (root_chain_final w2 w3).
Proof.
 assert (Ready : match root_chain_run root_chain_steps (root_chain_initial w2 w3) with
   Some _ => true | None => false end=true) by reflexivity.
 unfold root_chain_final;destruct (root_chain_run root_chain_steps (root_chain_initial w2 w3));
   [reflexivity|discriminate].
Qed.

Theorem exec_root_chain_owned e le m w2 w3 :
 e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> root_locals_separated e ->
 root_locals_owned e m -> root_values_at e m (root_chain_initial w2 w3) -> exists mf lef,
 Clight2.exec_stmt secp_ge e le m (root_chain_body root_chain_steps Sskip) E0 lef mf Out_normal /\
 root_locals_owned e mf /\ root_values_at e mf (root_chain_final w2 w3) /\
 (forall k,k<>_j -> lef!k=le!k) /\ lframe (root_chain_frame e) m mf.
Proof.
 intros EQ EM Sep Owned Store;eapply exec_root_chain_run;
   [exact root_chain_steps_valid|exact EQ|exact EM|exact Sep|exact Owned|exact Store|apply root_chain_runs].
Qed.

Fixpoint root_drop_statements (n : nat) (s : statement) := match n with
 | O => s | S k => match s with Ssequence _ rest => root_drop_statements k rest | _ => Sskip end end.
Definition root_after_chain := root_drop_statements 35 (fn_body f_secp256k1_fe_sqrt_var).
Lemma root_chain_body_source : root_drop_statements 5 (fn_body f_secp256k1_fe_sqrt_var)=
 root_chain_body root_chain_steps root_after_chain.
Proof. reflexivity. Qed.
