(** Original zero-length global-Z call: entry, real locals and release. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque secp_ge.
Set Default Timeout 10.

Definition globalz_empty_env bz bt := PTree.set _tmpa (bt,Tstruct __6123 noattr)
 (PTree.set _zs (bz,Tstruct __5467 noattr) empty_env).
Definition globalz_empty_temps a zr :=
 PTree.set _zr zr (PTree.set _a a (PTree.set _len (Vlong Int64.zero)
  (create_undef_temps (fn_temps f_secp256k1_ge_table_set_globalz)))).
Definition globalz_nonempty_branch := match fn_body f_secp256k1_ge_table_set_globalz with
 | Ssequence _ (Sifthenelse _ body _)=>body | _=>Sskip end.
Lemma globalz_empty_body_source : fn_body f_secp256k1_ge_table_set_globalz=
 Ssequence (Sset _i (Ebinop Osub (Etempvar _len tulong) (Econst_int Int.one tint) tulong))
  (Sifthenelse (Ebinop Ogt (Etempvar _len tulong) (Econst_int Int.zero tint) tint)
    globalz_nonempty_branch Sskip).
Proof. reflexivity. Qed.
Lemma globalz_empty_blocks bz bt : blocks_of_env secp_ge (globalz_empty_env bz bt)=
 [(bt,0,128);(bz,0,40)].
Proof. reflexivity. Qed.

Lemma globalz_empty_body e le m : le!_len=Some (Vlong Int64.zero) ->
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_ge_table_set_globalz) E0
 (PTree.set _i (Vlong (Int64.sub Int64.zero Int64.one)) le) m Out_normal.
Proof.
 intro Length;rewrite globalz_empty_body_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
  (le1:=PTree.set _i (Vlong (Int64.sub Int64.zero Int64.one)) le).
 - apply exec_Sset;eapply eval_Ebinop;[apply eval_Etempvar;exact Length|constructor|reflexivity].
 - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
   eapply eval_Ebinop.
   + apply eval_Etempvar;rewrite PTree.gso by discriminate;exact Length.
   + constructor.
   + reflexivity.
Qed.

Theorem eval_ge_table_set_globalz_empty m (a zr : val) : exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_table_set_globalz)
  [Vlong Int64.zero;a;zr] E0 mf Vundef /\ Mem.unchanged_on (fun _ _=>True) m mf.
Proof.
 destruct (Mem.alloc m 0 40) as [ma bz] eqn:AZ.
 destruct (Mem.alloc ma 0 128) as [mb bt] eqn:AT.
 assert (Different:bz<>bt).
 { intro Equal;apply (Mem.fresh_block_alloc _ _ _ _ _ AT);rewrite <-Equal.
   eapply Mem.valid_new_block;exact AZ. }
 assert (Old:forall b,Mem.valid_block m b -> b<>bz /\ b<>bt).
 { intros b Valid;split;intro Equal;subst b.
   - exact (Mem.fresh_block_alloc _ _ _ _ _ AZ Valid).
   - apply (Mem.fresh_block_alloc _ _ _ _ _ AT);eapply Mem.valid_block_alloc;[exact AZ|exact Valid]. }
 assert (FZ:Mem.range_perm mb bz 0 40 Cur Freeable).
 { intros pos Range;eapply Mem.perm_alloc_1;[exact AT|];eapply Mem.perm_alloc_2;[exact AZ|exact Range]. }
 assert (FT:Mem.range_perm mb bt 0 128 Cur Freeable).
 { intros pos Range;eapply Mem.perm_alloc_2;[exact AT|exact Range]. }
 destruct (free_list_exists [(bt,0,128);(bz,0,40)] mb) as (mf & Free & Unchanged).
 - repeat constructor;cbn;intuition congruence.
 - intros b lo hi [Eq | [Eq | Eq]];try contradiction;inversion Eq;subst;assumption.
 - exists mf;split.
   + eapply eval_funcall_internal with (e:=globalz_empty_env bz bt) (le1:=globalz_empty_temps a zr)
      (le2:=PTree.set _i (Vlong (Int64.sub Int64.zero Int64.one)) (globalz_empty_temps a zr))
      (m1:=mb) (m2:=mb) (out:=Out_normal).
     * assert (OK:fn_okb f_secp256k1_ge_table_set_globalz=true) by reflexivity.
       destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
       constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
       eapply alloc_variables_cons with (m1:=ma) (b1:=bz).
       -- exact AZ.
       -- eapply alloc_variables_cons with (m1:=mb) (b1:=bt);[exact AT|constructor].
     * apply globalz_empty_body;unfold globalz_empty_temps.
       rewrite PTree.gso by discriminate;rewrite PTree.gso by discriminate;apply PTree.gss.
     * reflexivity.
     * rewrite globalz_empty_blocks;exact Free.
   + assert (AllocFrame:Mem.unchanged_on (fun _ _=>True) m mb).
     { eapply Mem.unchanged_on_trans.
       - eapply Mem.alloc_unchanged_on;exact AZ.
       - eapply Mem.alloc_unchanged_on;exact AT. }
     assert (FreeFrame:Mem.unchanged_on (fun b _=>Mem.valid_block m b) mb mf).
     { eapply Mem.unchanged_on_implies;[exact Unchanged|].
       intros b pos Valid _;destruct (Old b Valid) as [NZ NT];cbn;intuition congruence. }
     eapply Mem.unchanged_on_implies with (P:=fun b _=>Mem.valid_block m b).
     * eapply Mem.unchanged_on_trans;[|exact FreeFrame].
       eapply Mem.unchanged_on_implies;[exact AllocFrame|];intros;exact I.
     * intros b pos _ Valid;exact Valid.
Qed.
