(** Old permissions of a checked closed set of original internal functions. *)
From Coq Require Import ZArith List Bool Lia.
From compcert Require Import Coqlib AST Ctypes Cop Clight ClightBigstep Maps Integers Values Memory Events.
Require Import C.jet_clight_internal_frame.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition keeps_permissions (m mf : mem) :=
 forall b ofs k p,Mem.perm m b ofs k p -> Mem.perm mf b ofs k p.
Lemma keeps_permissions_refl m : keeps_permissions m m.
Proof. intros b ofs k p H;exact H. Qed.
Lemma keeps_permissions_trans m mi mf : keeps_permissions m mi -> keeps_permissions mi mf -> keeps_permissions m mf.
Proof. intros First Second b ofs k p H;apply Second,First;exact H. Qed.
Lemma alloc_keeps_permissions m lo hi mf b : Mem.alloc m lo hi=(mf,b) -> keeps_permissions m mf.
Proof. intros Alloc bb ofs k p Perm;eapply Mem.perm_alloc_1;eassumption. Qed.
Lemma assign_keeps_permissions ce ty m b ofs bf v mf : assign_loc ce ty m b ofs bf v mf -> keeps_permissions m mf.
Proof.
 intro Assign;inversion Assign;subst.
 - intros bb oo k p P;eapply Mem.perm_store_1;cbn [Mem.storev] in *;eassumption.
 - intros bb oo k p P;eapply Mem.perm_storebytes_1;eassumption.
 - match goal with Bits : store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ => inversion Bits;subst end.
   intros bb oo k p P;eapply Mem.perm_store_1;cbn [Mem.storev] in *;eassumption.
Qed.
Lemma alloc_variables_keeps_permissions ge e m vars ef mf :
 alloc_variables ge e m vars ef mf -> keeps_permissions m mf.
Proof. intro Alloc;induction Alloc;eauto using keeps_permissions_refl,keeps_permissions_trans,alloc_keeps_permissions. Qed.
Lemma entry_keeps_permissions ge fd args m e le mf : function_entry2 ge fd args m e le mf -> keeps_permissions m mf.
Proof. intro Entry;inversion Entry;subst;eapply alloc_variables_keeps_permissions;eassumption. Qed.

Lemma alloc_variables_avoids ge e m vars ef mf b : alloc_variables ge e m vars ef mf ->
 Mem.valid_block m b -> (forall id ty,e!id<>Some (b,ty)) -> forall id ty,ef!id<>Some (b,ty).
Proof.
 intro Alloc;induction Alloc;intros Valid Avoid;[exact Avoid|].
 apply IHAlloc.
 - eapply Mem.valid_block_alloc;eassumption.
 - intros key ty' Get;rewrite PTree.gsspec in Get;destruct (peq key id).
   + assert (Different : b1<>b).
     { intro Same;subst b1;exact (Mem.fresh_block_alloc _ _ _ _ _ H Valid). }
     injection Get;congruence.
   + exact (Avoid key ty' Get).
Qed.
Lemma entry_blocks_avoid ge fd args m e le mf b : function_entry2 ge fd args m e le mf ->
 Mem.valid_block m b -> forall lo hi,~In (b,lo,hi) (blocks_of_env ge e).
Proof.
 intros Entry Valid.
 assert (Avoid : forall id ty,e!id<>Some (b,ty)).
 { inversion Entry;subst;eapply alloc_variables_avoids;[eassumption|exact Valid|].
   intros id ty Get;rewrite PTree.gempty in Get;discriminate. }
 intros lo hi Member;unfold blocks_of_env in Member.
 apply in_map_iff in Member as ([id [bb ty]] & Eq & Member).
 cbn [block_of_binding] in Eq;injection Eq as Same _ _;subst bb.
 exact (Avoid id ty (PTree.elements_complete _ _ _ Member)).
Qed.
Lemma free_list_avoids blocks mi mf b ofs k p : Mem.free_list mi blocks=Some mf ->
 (forall lo hi,~In (b,lo,hi) blocks) -> Mem.perm mi b ofs k p -> Mem.perm mf b ofs k p.
Proof.
 revert mi;induction blocks as [|[[bb lo] hi] rest IH];intros mi Free Avoid Perm.
 - cbn in Free;injection Free as <-;exact Perm.
 - cbn in Free;destruct (Mem.free mi bb lo hi) as [mm|] eqn:F;[|discriminate].
   eapply IH;[exact Free| |].
   + intros l h InRest;apply (Avoid l h);right;exact InRest.
   + eapply Mem.perm_free_1;[exact F| |exact Perm].
     left;intro Same;subst bb;apply (Avoid lo hi);left;reflexivity.
Qed.

Theorem internal_exec_keeps_permissions ge table : internal_table_ok ge table ->
 (forall e le m stmt t lef mf out,
  Clight2.exec_stmt ge e le m stmt t lef mf out ->
  plain_env e -> closed_stmtb table stmt=true -> keeps_permissions m mf) /\
 (forall m f args t mf result,
  Clight2.eval_funcall ge m f args t mf result -> allowed_call table f -> keeps_permissions m mf).
Proof.
 intro HT.
 apply (exec_stmt_funcall_ind function_entry2 ge
  (fun e le m stmt t lef mf out=>plain_env e -> closed_stmtb table stmt=true -> keeps_permissions m mf)
  (fun m f args t mf result=>allowed_call table f -> keeps_permissions m mf)).
 all: intros.
 all: try solve [apply keeps_permissions_refl].
 all: try solve [eapply assign_keeps_permissions;eassumption].
 all: try solve [discriminate].
 all: try match goal with Closed : closed_stmtb _ (Ssequence _ _)=true |- _=>
  apply andb_true_iff in Closed;destruct Closed as [C1 C2] end.
 all: try solve [eauto 6 using keeps_permissions_trans].
 - match goal with IH : allowed_call _ _ -> keeps_permissions _ _ |- _=>apply IH end.
   eapply direct_internal_call;eassumption.
 - match goal with Closed : closed_stmtb _ (Sifthenelse _ _ _)=true |- _=>
   apply andb_true_iff in Closed;destruct Closed as [C1 C2] end;destruct b;eauto.
 - match goal with Closed : closed_stmtb _ (Sloop _ _)=true |- _=>
   apply andb_true_iff in Closed;destruct Closed as [C1 C2] end;eauto 8 using keeps_permissions_trans.
 - match goal with Closed : closed_stmtb _ (Sloop _ _)=true |- _=>
   apply andb_true_iff in Closed;destruct Closed as [C1 C2] end;eauto 8 using keeps_permissions_trans.
 - match goal with Closed : closed_stmtb _ (Sloop _ _)=true |- _=>
   pose proof Closed as Loop;apply andb_true_iff in Closed;destruct Closed as [C1 C2] end.
   eapply keeps_permissions_trans;[apply H0;assumption|].
   eapply keeps_permissions_trans;[apply H3;assumption|apply H5;assumption].
 - match goal with Allowed : allowed_call _ (Internal _) |- _=>
   destruct Allowed as (id & fd & Lookup & Eq);injection Eq as Eq;subst fd end.
   destruct (HT _ _ Lookup) as (_ & Closed & Vars).
   match goal with Entry : function_entry2 ge _ _ ?m ?e _ ?mi,
    Free : Mem.free_list ?mm (blocks_of_env ge ?e)=Some ?mf |- _=>
    pose proof (entry_keeps_permissions _ _ _ _ _ _ _ Entry) as EntryP;
    assert (BodyP : keeps_permissions mi mm) by (eauto using entry_plain);
    intros bb ofs k p Perm;eapply free_list_avoids;[exact Free| |apply BodyP,EntryP;exact Perm];
    eapply entry_blocks_avoid;[exact Entry|eapply Mem.perm_valid_block;exact Perm]
   end.
 - match goal with Allowed : allowed_call _ (External _ _ _ _) |- _=>
   destruct Allowed as (id & fd & Lookup & Eq);discriminate Eq end.
Qed.
