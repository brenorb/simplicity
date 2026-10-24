(** Execute the original f/g copies for the modulus-parametric initializer.
    The checked signed62 By_copy proof is reused; no libc model is involved. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_secp_modinv_entry_modulus C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_copies
 C.jet_secp_signed62_assign C.jet_secp_modinv_fg_index C.jet_secp_fe_nv
 C.jet_secp_local_regions C.jet_secp_u128_shift64_rep C.jet_secp_statement_prefix C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_modinv_var_shorten C.jet_sx_u64_transport C.jet_secp_modinfo_fe_copy.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition inv_mod_copy_exprs (mu : nat->int64) (g : bool) := if g then inv_input_exprs else map XLc [mu 0%nat;mu 1%nat;mu 2%nat;mu 3%nat;mu 4%nat].
Definition inv_mod_f_regs mu := upd (sregs(inv_mod_init_state mu)) 4
 (mkreg(u64_cells 0 (inv_mod_copy_exprs mu false)) true (Some 40)).
Definition inv_mod_fg_regs mu := upd (inv_mod_f_regs mu) 5
 (mkreg(u64_cells 0 inv_input_exprs) true (Some 40)).
Definition inv_mod_copy_regs mu (g : bool) := if g then inv_mod_f_regs mu else sregs(inv_mod_init_state mu).
Definition inv_mod_copy_word (mu rho : nat->int64) (g : bool) i := if g then rho i else mu i.
Definition inv_mod_copy_expr mu (g : bool) i := if g then XLv i else XLc(mu i).

Lemma inv_mod_copy_load mu (g : bool) i : (i<5)%nat ->
 xload (inv_mod_copy_regs mu g) (inv_copy_source g) (8*Z.of_nat i) tulong=Some(inv_mod_copy_expr mu g i).
Proof. destruct g;destruct i as [|[|[|[|[|i]]]]];intro I;try lia;reflexivity. Qed.
Lemma inv_mod_copy_values mu rho beta g i x : nth_error(inv_mod_copy_exprs mu g) i=Some x ->
 den rho beta x=Vlong(inv_mod_copy_word mu rho g i) /\ xp_le (inv_copy_target g) x=true.
Proof.
 destruct g;destruct i as [|[|[|[|[|i]]]]];cbn [inv_mod_copy_exprs inv_input_exprs map nth_error];
 intro At;try(destruct i;discriminate At);injection At as <-;split;reflexivity.
Qed.

Lemma inv_mod_field_fg : inv_mod_fg_regs modinfo_fe_limb=inv_fg_regs.
Proof. reflexivity. Qed.
Lemma inv_mod_copy_owned mu g : rfree(nth (inv_copy_target g) (inv_mod_copy_regs mu g) (mkreg [] true None))=Some 40.
Proof. destruct g;reflexivity. Qed.
Lemma inv_mod_copy_lengths mu g : length(inv_mod_copy_regs mu g)=7%nat /\ length(inv_mod_copy_exprs mu g)=5%nat.
Proof. destruct g;split;reflexivity. Qed.
Lemma inv_mod_copy_separate mu rho beta m g : rep rho beta (inv_mod_copy_regs mu g) m ->
 blk beta (inv_copy_target g)<>blk beta (inv_copy_source g).
Proof.
 intros(_ & Sep & _).
 assert(Different:inv_copy_target g<>inv_copy_source g) by(destruct g;discriminate).
 pose proof(nth_error_nth' (inv_mod_copy_regs mu g) (mkreg [] true None) (n:=inv_copy_target g)
  ltac:(rewrite(proj1(inv_mod_copy_lengths mu g));destruct g;cbn [inv_copy_target];lia)) as Target.
 pose proof(nth_error_nth' (inv_mod_copy_regs mu g) (mkreg [] true None) (n:=inv_copy_source g)
  ltac:(rewrite(proj1(inv_mod_copy_lengths mu g));destruct g;cbn [inv_copy_source];lia)) as Source.
 destruct(Sep _ _ _ _ Different Target Source) as[Separate | [NoOwner _]];[exact Separate|].
 rewrite inv_mod_copy_owned in NoOwner;discriminate.
Qed.
Lemma inv_mod_copy_result mu g : upd (inv_mod_copy_regs mu g) (inv_copy_target g)
 (mkreg(u64_cells 0 (inv_mod_copy_exprs mu g)) true (Some 40))=
 if g then inv_mod_fg_regs mu else inv_mod_f_regs mu.
Proof. destruct g;reflexivity. Qed.
Lemma inv_mod_copy_shape mu g :
 rshape(mkreg(u64_cells 0 (inv_mod_copy_exprs mu g)) true (Some 40))=
 rshape(nth (inv_copy_target g) (inv_mod_copy_regs mu g) (mkreg [] true None)).
Proof. destruct g;reflexivity. Qed.

Local Opaque inv_mod_init_state secp_ge.
Theorem exec_inv_mod_copy mu rho beta e le m g : rep rho beta (inv_mod_copy_regs mu g) m ->
 tmatch rho beta inv_start_temps le -> ematch beta (snd inv_start_alloc) e ->
 bas beta (inv_copy_source g)=0 -> exists mf,
 Clight2.exec_stmt secp_ge e le m (inv_copy_stmt g) E0 le mf Out_normal /\
 rep rho beta (if g then inv_mod_fg_regs mu else inv_mod_f_regs mu) mf /\
 lframe (fun b _=>b<>blk beta (inv_copy_target g)) m mf.
Proof.
 intros Rep Temps Env Base.
 assert(At:nth_error(inv_mod_copy_regs mu g) (inv_copy_target g)=
  Some(nth (inv_copy_target g) (inv_mod_copy_regs mu g) (mkreg [] true None))).
 { apply nth_error_nth';rewrite(proj1(inv_mod_copy_lengths mu g));destruct g;cbn [inv_copy_target];lia. }
 destruct(rep_free_region rho beta (inv_mod_copy_regs mu g) m (inv_copy_target g) 40 Rep
  ltac:(rewrite(proj1(inv_mod_copy_lengths mu g));destruct g;cbn [inv_copy_target];lia) (inv_mod_copy_owned mu g))
  as(DestBase & DestFree).
 assert(Loads:forall i,(i<5)%nat -> Mem.load Mint64 m (blk beta (inv_copy_source g)) (8*Z.of_nat i)=
  Some(Vlong(inv_mod_copy_word mu rho g i))).
 { intros i I;pose proof(xload_u64_defined_sound rho beta _ m _ _ _ Rep (inv_mod_copy_load mu g i I)) as Load.
   rewrite Base,Z.add_0_l in Load;destruct g;exact Load. }
 assert(ByIndex:forall i v,nth_error(words5(inv_mod_copy_word mu rho g)) i=Some v ->
  Mem.load Mint64 m (blk beta (inv_copy_source g)) (8*Z.of_nat i)=Some(Vlong v)).
 { intros i v Entry;assert(I:(i<5)%nat).
   { change(i<length(words5(inv_mod_copy_word mu rho g)))%nat;apply nth_error_Some;rewrite Entry;discriminate. }
   destruct i as [|[|[|[|[|i]]]]];try lia;injection Entry as <-;apply Loads;lia. }
 destruct(eval_signed62_assign_readable (inv_mod_copy_word mu rho g) m
  (blk beta (inv_copy_target g)) (blk beta (inv_copy_source g))
  (inv_mod_copy_separate mu rho beta m g Rep) DestFree (inv_five_readable _ _ _ Loads) ByIndex)
  as(mf & Call & Out & Free & Frame).
 assert(New:region_ok rho beta mf (inv_copy_target g)
  (mkreg(u64_cells 0 (inv_mod_copy_exprs mu g)) true (Some 40))).
 { apply(inv_copy_region rho beta mf (inv_copy_target g) (inv_mod_copy_exprs mu g) (inv_mod_copy_word mu rho g));
   [exact DestBase|exact(proj2(inv_mod_copy_lengths mu g))|
    intros i x AtX;exact(inv_mod_copy_values mu rho (lay beta) g i x AtX)|exact Out|exact Free]. }
 assert(Post:rep rho beta (if g then inv_mod_fg_regs mu else inv_mod_f_regs mu) mf).
 { rewrite <-inv_mod_copy_result;eapply inv_rep_replace_owned;
   [exact Rep|exact At|rewrite inv_mod_copy_owned;discriminate|apply inv_mod_copy_shape|exact New|exact Frame]. }
 exists mf;split;[|split;assumption].
 assert(Linked:In(_secp256k1_modinv64_signed62_assign,f_secp256k1_modinv64_signed62_assign) secp_pure).
 { unfold secp_pure;repeat(first[left;reflexivity|right]). }
 assert(NotLocal:e!_secp256k1_modinv64_signed62_assign=None) by exact(proj1(Env _secp256k1_modinv64_signed62_assign)).
 pose proof(inv_copy_arguments rho e le m beta g Env Temps Base) as Args.
 destruct g;[rewrite inv_copy_g_source|rewrite inv_copy_f_source];
 eapply exec_curve_call with(result:=None) (v:=Vundef);eassumption.
Qed.

Theorem exec_inv_mod_copies mu rho beta e le m : rep rho beta (sregs(inv_mod_init_state mu)) m ->
 tmatch rho beta inv_start_temps le -> ematch beta (snd inv_start_alloc) e -> bas beta 1=0 -> exists mf,
 Clight2.exec_stmt secp_ge e le m inv_copies E0 le mf Out_normal /\
 rep rho beta (inv_mod_fg_regs mu) mf /\ lframe(fun b _=>b<>blk beta 4 /\ b<>blk beta 5) m mf.
Proof.
 intros Rep Temps Env Base.
 destruct(exec_inv_mod_copy mu rho beta e le m false Rep Temps Env Base) as(m1 & F & RepF & FrameF).
 assert(BaseX:bas beta 0=0) by(eapply rep_owned_region_base_zero;[exact RepF|reflexivity|reflexivity]).
 destruct(exec_inv_mod_copy mu rho beta e le m1 true RepF Temps Env BaseX) as(mf & G & RepG & FrameG).
 exists mf;split.
 - unfold inv_copies;eapply exec_Sseq_1 with(t1:=E0) (t2:=E0) (le1:=le) (m1:=m1);[exact F|].
   eapply exec_Sseq_1 with(t1:=E0) (t2:=E0) (le1:=le) (m1:=mf);[exact G|constructor].
 - split;[exact RepG|]. eapply lframe_trans;
   [eapply lframe_implies;[exact FrameF|]|eapply lframe_implies;[exact FrameG|]];
   intros b pos [Fout Gout] Valid;assumption.
Qed.

Theorem inv_mod_entry_to_loop mu rho beta m : rep rho beta (inv_mod_start_regs mu) m -> bas beta 1=0 ->
 exists betaN e le mi lef mf,
 function_entry2 secp_ge f_secp256k1_modinv64_var (map(den rho(lay beta)) inv_start_args) m e le mi /\
 Clight2.exec_stmt secp_ge e le mi inv_ready_prefix E0 lef mf Out_normal /\
 rep rho (beta++betaN) (inv_mod_fg_regs mu) mf /\
 tmatch rho (beta++betaN) inv_loop_start_temps lef /\ ematch (beta++betaN) (snd inv_start_alloc) e /\
 lef!_len=Some(Vint(Int.repr 5)) /\ lef!_eta=Some(Vlong(Int64.repr(-1))) /\
 Forall(fun p=>~Mem.valid_block m (fst p)) betaN /\
 lframe(fun b ofs=>~foot (beta++betaN) (map rshape(sregs(inv_mod_start_state mu))) b ofs) m mf.
Proof.
 intros Rep Base;assert(Len:length beta=2%nat) by exact(proj1 Rep).
 destruct(inv_mod_entry_and_initializers mu rho beta m Rep)
  as(betaN & e & le & mi & lc & m1 & Entry & Init & Rep1 & Temps & Env & Fresh & Frame1).
 assert(BaseN:bas(beta++betaN) 1=0) by(unfold bas;rewrite lay_app_l by lia;exact Base).
 destruct(exec_inv_mod_copies mu rho (beta++betaN) e lc m1 Rep1 Temps Env BaseN)
  as(mf & Copies & RepF & Frame2).
 assert(LocalLen:length betaN=5%nat).
 { pose proof(proj1 Rep1) as L;rewrite app_length in L.
   assert(Count:length(sregs(inv_mod_init_state mu))=7%nat) by reflexivity.
   rewrite Count,Len in L;lia. }
 assert(CallerCopies:lframe(fun b pos=>Mem.valid_block m b /\
  ~foot (beta++betaN) (map rshape(sregs(inv_mod_start_state mu))) b pos) m1 mf).
 { eapply lframe_implies;[exact Frame2|]. intros b pos [Valid Outside] V;split;intro Same;subst b;
   [exact(inv_copy_fresh beta betaN m Len LocalLen Fresh 4%nat ltac:(lia) Valid)|
    exact(inv_copy_fresh beta betaN m Len LocalLen Fresh 5%nat ltac:(lia) Valid)]. }
 destruct(exec_inv_loop_setup rho (beta++betaN) e lc mf Temps) as(Setup & TFinal).
 assert(Copied:Clight2.exec_stmt secp_ge e le mi inv_copied_prefix E0 lc mf Out_normal).
 { rewrite inv_copied_prefix_source;eapply exec_statement_prefix_then_last;[exact Init|exact Copies]. }
 exists betaN,e,le,mi,(inv_loop_start_env lc),mf;split;[exact Entry|];split.
 - rewrite inv_ready_prefix_source;eapply exec_statement_prefix_then_last;[exact Copied|exact Setup].
 - split;[exact RepF|];split;[exact TFinal|];split;[exact Env|];split.
   + unfold inv_loop_start_env;rewrite PTree.gso by discriminate;apply PTree.gss.
   + split;[apply PTree.gss|];split;[exact Fresh|].
     eapply lframe_implies with(P:=fun b pos=>Mem.valid_block m b /\
       ~foot (beta++betaN) (map rshape(sregs(inv_mod_start_state mu))) b pos).
     * eapply lframe_trans;[|exact CallerCopies].
       eapply lframe_implies;[exact Frame1|];intros b pos [Valid Outside] V;exact Outside.
     * intros b pos Outside Valid;split;assumption.
Qed.
