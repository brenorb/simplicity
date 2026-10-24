(** The actual variable-inverse entry/initializers with arbitrary six-word
    modulus metadata. No modulus arithmetic or external call is needed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_modinv_var_entry
 C.jet_secp_modinv_var_copies C.jet_secp_modinfo_fe_global C.jet_secp_modinfo_fe_copy.
Require Import C.jet_secp_u128_shift64_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition inv_mod_words (mu : nat->int64) := map mu [0;1;2;3;4;5]%nat.
Definition inv_mod_start_regs mu :=
 [mkreg (u64_cells 0 [XLv 0;XLv 1;XLv 2;XLv 3;XLv 4]) true (Some 40);
  mkreg (u64_cells 0 (map XLc (inv_mod_words mu))) false None].
Definition inv_mod_start_state mu := mkst inv_start_temps (inv_mod_start_regs mu++fst inv_start_alloc) [] 5.
Definition inv_mod_init_run mu := xstmt (genv_cenv secp_ge) [] [] 80
 (snd inv_start_alloc) (inv_mod_start_state mu) inv_initializers.
Definition inv_mod_init_state mu := match inv_mod_init_run mu with
 | Some(RDone st _)=>st | _=>inv_mod_start_state mu end.
Lemma inv_mod_init_run_eq mu : inv_mod_init_run mu=Some(RDone(inv_mod_init_state mu) ONormal).
Proof. reflexivity. Qed.
Lemma inv_mod_init_temps mu : stemps(inv_mod_init_state mu)=inv_start_temps.
Proof. reflexivity. Qed.
Lemma inv_mod_init_shape mu : map rshape(sregs(inv_mod_init_state mu))=map rshape(sregs inv_init_state).
Proof. reflexivity. Qed.
Lemma inv_mod_init_load mu (high : bool) i : (i<5)%nat ->
 xload (sregs(inv_mod_init_state mu)) (if high then 3 else 2) (8*Z.of_nat i) tulong=Some(inv_init_sx high i).
Proof. destruct high;destruct i as [|[|[|[|[|i]]]]];intro I;try lia;reflexivity. Qed.
Lemma inv_mod_init_storage mu rho beta m : rep rho beta (sregs(inv_mod_init_state mu)) m ->
 forall (high : bool) i,(i<5)%nat ->
 Mem.load Mint64 m (blk beta (if high then 3 else 2))
 (bas beta (if high then 3 else 2)+8*Z.of_nat i)=Some(Vlong(inv_init_word high i)).
Proof.
 intros Rep high i I.
 pose proof(xload_u64_defined_sound rho beta _ m _ _ _ Rep (inv_mod_init_load mu high i I)) as Load.
 rewrite inv_init_den in Load;exact Load.
Qed.

Local Opaque xstmt inv_mod_init_state inv_mod_start_state inv_initializers secp_ge.
Theorem exec_inv_mod_initializers mu rho beta e le m :
 rep rho beta (sregs(inv_mod_start_state mu)) m ->
 tmatch rho beta (stemps(inv_mod_start_state mu)) le -> ematch beta (snd inv_start_alloc) e -> exists lef mf,
 Clight2.exec_stmt secp_ge e le m inv_initializers E0 lef mf Out_normal /\
 rep rho beta (sregs(inv_mod_init_state mu)) mf /\ tmatch rho beta inv_start_temps lef /\
 (forall (high : bool) i,(i<5)%nat ->
  Mem.load Mint64 mf (blk beta (if high then 3 else 2))
  (bas beta (if high then 3 else 2)+8*Z.of_nat i)=Some(Vlong(inv_init_word high i))) /\
 lframe (fun b ofs=>~foot beta (map rshape(sregs(inv_mod_start_state mu))) b ofs) m mf.
Proof.
 intros Rep Temps Env.
 pose proof(xstmt_sound secp_ge [] [] (fun _ _=>True) (fun _ _ _=>True) (fun _=>False)
  ltac:(auto) ltac:(intros;contradiction) ltac:(intros id ent Lookup;discriminate Lookup) 80) as Sound.
 specialize(Sound (snd inv_start_alloc) (inv_mod_start_state mu) inv_initializers
  (RDone(inv_mod_init_state mu) ONormal) (inv_mod_init_run_eq mu) rho beta e le m Rep Temps Env).
 destruct Sound as(lef & mf & out & Exec & Post).
 - split;intros;discriminate.
 - intros r _ [].
 - exact I.
 - apply Forall_forall;intros;exact I.
 - destruct Post as(Out & Match & Normal & Shape & Inv & Frame).
   cbn [rsel fst snd outmatch] in Out,Match,Normal;destruct out;cbn [outmatch] in Normal;try contradiction.
   rewrite inv_mod_init_temps in Match.
   exists lef,mf;split;[exact Exec|];split;[exact Out|];split;[exact Match|];split.
   + exact(inv_mod_init_storage mu rho beta mf Out).
   + eapply lframe_implies;[exact Frame|];intros b ofs Outside Valid;split;[exact Valid|];split;[exact Outside|tauto].
Qed.

Theorem inv_mod_entry_and_initializers mu rho beta m : rep rho beta (inv_mod_start_regs mu) m ->
 exists betaN e le mi lef mf,
 function_entry2 secp_ge f_secp256k1_modinv64_var (map(den rho(lay beta)) inv_start_args) m e le mi /\
 Clight2.exec_stmt secp_ge e le mi inv_initializers E0 lef mf Out_normal /\
 rep rho (beta++betaN) (sregs(inv_mod_init_state mu)) mf /\
 tmatch rho (beta++betaN) inv_start_temps lef /\ ematch (beta++betaN) (snd inv_start_alloc) e /\
 Forall(fun p=>~Mem.valid_block m (fst p)) betaN /\
 lframe (fun b ofs=>~foot (beta++betaN) (map rshape(sregs(inv_mod_start_state mu))) b ofs) m mf.
Proof.
 intro Rep;destruct(fn_okb_true _ inv_start_fn_ok) as(Vars & Params & Disjoint).
 assert(Len:length beta=length(inv_mod_start_regs mu)) by exact(proj1 Rep).
 destruct(xalloc_sound secp_ge rho (std_cells(genv_cenv secp_ge))
  (fn_vars f_secp256k1_modinv64_var) (length(inv_mod_start_regs mu))
  (fst inv_start_alloc) (snd inv_start_alloc) beta (inv_mod_start_regs mu) m empty_env inv_start_alloc_ok Rep Len Vars)
  as(e & mi & betaN & Alloc & Start & NewLen & Env & Index & Injective & Fresh & Unchanged).
 assert(Arguments:map(den rho(lay(beta++betaN))) inv_start_args=map(den rho(lay beta)) inv_start_args).
 { apply map_den_ext with(n:=length(inv_mod_start_regs mu));[|reflexivity].
   intros r R;apply lay_app_l;lia. }
 destruct(xbind_sound rho (beta++betaN) (fn_params f_secp256k1_modinv64_var) inv_start_args
  (PTree.empty sx) inv_start_temps (create_undef_temps(fn_temps f_secp256k1_modinv64_var)) inv_start_bind_ok)
  as(le & Bind & Temps).
 { intros id x Eq;rewrite PTree.gempty in Eq;discriminate. }
 rewrite Arguments in Bind.
 assert(Match:ematch (beta++betaN) (snd inv_start_alloc) e).
 { intro id;split.
   - rewrite Env;destruct(vlookup (snd inv_start_alloc) id) as [[r ty] | ];[reflexivity|apply PTree.gempty].
   - intros r ty Lookup;exact(proj1(proj2(proj2(Index id r ty Lookup)))). }
 destruct(exec_inv_mod_initializers mu rho (beta++betaN) e le mi Start Temps Match)
  as(lef & mf & Exec & Out & TFinal & Words & Frame).
 exists betaN,e,le,mi,lef,mf;split.
 - constructor;[exact Vars|exact Params|exact Disjoint|exact Alloc|exact Bind].
 - split;[exact Exec|];split;[exact Out|];split;[exact TFinal|];split;[exact Match|];split;[exact Fresh|].
   eapply lframe_trans;[|exact Frame].
   eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|];intros;exact I.
Qed.

(** The shared result also specializes to the existing field initializer. *)
Lemma inv_mod_field_start : inv_mod_start_regs modinfo_fe_limb=inv_start_regs.
Proof. reflexivity. Qed.
Lemma inv_mod_field_init : inv_mod_init_state modinfo_fe_limb=inv_init_state.
Proof. reflexivity. Qed.
