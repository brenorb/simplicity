(** Original variable inverse: real entry and d/e initializer statements. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_statement_prefix C.jet_secp_linkage C.jets_secp C.jet_secp_modinfo_fe_global.
Require Import C.jet_secp_u128_shift64_rep.
Require Import C.jet_secp_modinv_de_numeric C.jet_secp_modinv_normalize62_numeric C.jet_secp_modinv_normalize62_words C.jet_secp_fe_math.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition inv_start_regs :=
 [mkreg (u64_cells 0 [XLv 0;XLv 1;XLv 2;XLv 3;XLv 4]) true (Some 40);
  mkreg (u64_cells 0 (map XLc modinfo_fe_words)) false None].
Definition inv_start_args := [XP 0 0;XP 1 0].
Definition inv_start_alloc := Eval vm_compute in
 match xalloc (std_cells (genv_cenv secp_ge)) (genv_cenv secp_ge)
  (fn_vars f_secp256k1_modinv64_var) 2 with Some p=>p | None=>([],[]) end.
Definition inv_start_temps := PTree.set _modinfo (XP 1 0) (PTree.set _x (XP 0 0) (PTree.empty sx)).
Definition inv_start_state := mkst inv_start_temps (inv_start_regs++fst inv_start_alloc) [] 5.
Definition inv_start_parts := split_statement_last (fn_body f_secp256k1_modinv64_var).
Definition inv_initializers := statement_sequence (firstn 10 (fst inv_start_parts)) Sskip.
Definition inv_after_initializers := statement_sequence (skipn 10 (fst inv_start_parts)) (snd inv_start_parts).
Definition inv_init_run := xstmt (genv_cenv secp_ge) [] [] 80 (snd inv_start_alloc) inv_start_state inv_initializers.
Definition inv_init_state := match inv_init_run with Some (RDone st _)=>st | _=>inv_start_state end.
Lemma inv_initializers_source : fn_body f_secp256k1_modinv64_var=
 statement_sequence (firstn 10 (fst inv_start_parts)) inv_after_initializers.
Proof. reflexivity. Qed.
Lemma inv_init_run_eq : inv_init_run=Some (RDone inv_init_state ONormal).
Proof. vm_compute;reflexivity. Qed.

Definition inv_init_word (high : bool) i := if high && Nat.eqb i 0 then Int64.one else Int64.zero.
Definition inv_init_sx high i := XI2L Signed (XIc (if high && Nat.eqb i 0 then Int.one else Int.zero)).
Lemma inv_init_load (high : bool) i : (i<5)%nat ->
 xload (sregs inv_init_state) (if high then 3 else 2) (8*Z.of_nat i) tulong=Some (inv_init_sx high i).
Proof. destruct high;destruct i as [|[|[|[|[|i]]]]];intro I;try lia;vm_compute;reflexivity. Qed.
Lemma inv_init_den rho beta high i : den rho beta (inv_init_sx high i)=Vlong (inv_init_word high i).
Proof. unfold inv_init_sx,inv_init_word;destruct (high && Nat.eqb i 0);reflexivity. Qed.
Lemma inv_initializers_storage rho beta m : rep rho beta (sregs inv_init_state) m ->
 forall (high : bool) i,(i<5)%nat ->
 Mem.load Mint64 m (blk beta (if high then 3 else 2))
  (bas beta (if high then 3 else 2)+8*Z.of_nat i)=Some (Vlong (inv_init_word high i)).
Proof.
 intros Rep high i I.
 pose proof (xload_u64_defined_sound rho beta _ m _ _ _ Rep (inv_init_load high i I)) as Load.
 rewrite inv_init_den in Load;exact Load.
Qed.

Definition inv_initial_de_rho (later : nat->int64) n :=
 if (n <? 10)%nat then if Nat.eqb n 5 then Int64.one else Int64.zero else later n.
Lemma inv_initial_de_word later high i : (i<5)%nat ->
 de62_array (inv_initial_de_rho later) high i=inv_init_word high i.
Proof. destruct high;destruct i as [|[|[|[|[|i]]]]];intro I;try lia;reflexivity. Qed.
Lemma inv_initial_de_value later high : de62_input_value (inv_initial_de_rho later) high=if high then 1 else 0.
Proof. destruct high;reflexivity. Qed.
Lemma inv_initial_de_bounds later : de62_state_bounds (inv_initial_de_rho later).
Proof.
 split.
 - intros high i I;rewrite inv_initial_de_word by exact I.
   unfold inv_init_word;destruct (high && Nat.eqb i 0).
   + change (-(2^62-1)<=1<=2^62-1);lia.
   + change (-(2^62-1)<=0<=2^62-1);lia.
 - intro high;rewrite inv_initial_de_value;destruct high;unfold feP,feR;lia.
Qed.

Lemma inv_start_state_regs : sregs inv_start_state=inv_start_regs++fst inv_start_alloc.
Proof. reflexivity. Qed.
Lemma inv_start_state_temps : stemps inv_start_state=inv_start_temps.
Proof. reflexivity. Qed.
Lemma inv_start_fn_ok : fn_okb f_secp256k1_modinv64_var=true.
Proof. reflexivity. Qed.
Lemma inv_start_alloc_ok : xalloc (std_cells (genv_cenv secp_ge)) (genv_cenv secp_ge)
 (fn_vars f_secp256k1_modinv64_var) (length inv_start_regs)=Some (fst inv_start_alloc,snd inv_start_alloc).
Proof. reflexivity. Qed.
Lemma inv_start_bind_ok : xbind (fn_params f_secp256k1_modinv64_var) inv_start_args (PTree.empty sx)=Some inv_start_temps.
Proof. reflexivity. Qed.

Local Opaque xstmt inv_init_state inv_start_state inv_initializers secp_ge.
Theorem exec_inv_initializers rho beta e le m : rep rho beta (sregs inv_start_state) m ->
 tmatch rho beta (stemps inv_start_state) le -> ematch beta (snd inv_start_alloc) e -> exists lef mf,
 Clight2.exec_stmt secp_ge e le m inv_initializers E0 lef mf Out_normal /\
 rep rho beta (sregs inv_init_state) mf /\ tmatch rho beta (stemps inv_init_state) lef /\
 (forall (high : bool) i,(i<5)%nat ->
  Mem.load Mint64 mf (blk beta (if high then 3 else 2))
   (bas beta (if high then 3 else 2)+8*Z.of_nat i)=Some (Vlong (inv_init_word high i))) /\
 lframe (fun b ofs=>~foot beta (map rshape (sregs inv_start_state)) b ofs) m mf.
Proof.
 intros Rep Temps Env.
 pose proof (xstmt_sound secp_ge [] [] (fun _ _=>True) (fun _ _ _=>True) (fun _=>False)
  ltac:(auto) ltac:(intros;contradiction) ltac:(intros id ent Lookup;discriminate Lookup) 80) as Sound.
 specialize (Sound (snd inv_start_alloc) inv_start_state inv_initializers
  (RDone inv_init_state ONormal) inv_init_run_eq rho beta e le m Rep Temps Env).
 destruct Sound as (lef & mf & out & Exec & Post).
 - split;intros;discriminate.
 - intros r _ [].
 - exact I.
 - apply Forall_forall;intros;exact I.
 - destruct Post as (Out & Match & Normal & Shape & Inv & Frame).
   cbn [rsel fst snd outmatch] in Out,Match,Normal;destruct out;cbn [outmatch] in Normal;try contradiction.
   exists lef,mf;split;[exact Exec|];split;[exact Out|];split;[exact Match|];split.
   + exact (inv_initializers_storage rho beta mf Out).
   + eapply lframe_implies;[exact Frame|];intros b ofs Outside Valid;split;[exact Valid|];split;[exact Outside|tauto].
Qed.

(** Allocate the actual five local objects and bind the real parameters.
    The following two struct copies and the divstep loop are not executed
    or assumed by this prefix theorem. *)
Theorem inv_entry_and_initializers rho beta m : rep rho beta inv_start_regs m ->
 exists betaN e le mi lef mf,
 function_entry2 secp_ge f_secp256k1_modinv64_var (map (den rho (lay beta)) inv_start_args) m e le mi /\
 Clight2.exec_stmt secp_ge e le mi inv_initializers E0 lef mf Out_normal /\
 rep rho (beta++betaN) (sregs inv_init_state) mf /\
 tmatch rho (beta++betaN) (stemps inv_init_state) lef /\
 ematch (beta++betaN) (snd inv_start_alloc) e /\
 (forall later,de62_state_bounds (inv_initial_de_rho later) /\
  forall (high : bool) i,(i<5)%nat ->
   Mem.load Mint64 mf (blk (beta++betaN) (if high then 3 else 2))
    (bas (beta++betaN) (if high then 3 else 2)+8*Z.of_nat i)=
    Some (Vlong (de62_array (inv_initial_de_rho later) high i))) /\
 Forall (fun p=>~Mem.valid_block m (fst p)) betaN /\
 lframe (fun b ofs=>~foot (beta++betaN) (map rshape (sregs inv_start_state)) b ofs) m mf.
Proof.
 intro Rep;destruct (fn_okb_true _ inv_start_fn_ok) as (Vars & Params & Disjoint).
 assert (Len : length beta=length inv_start_regs) by exact (proj1 Rep).
 destruct (xalloc_sound secp_ge rho (std_cells (genv_cenv secp_ge))
  (fn_vars f_secp256k1_modinv64_var) (length inv_start_regs)
  (fst inv_start_alloc) (snd inv_start_alloc) beta inv_start_regs m empty_env inv_start_alloc_ok Rep Len Vars)
  as (e & mi & betaN & Alloc & Start & NewLen & Env & Index & Injective & Fresh & Unchanged).
 assert (Arguments : map (den rho (lay (beta++betaN))) inv_start_args=map (den rho (lay beta)) inv_start_args).
 { apply map_den_ext with (n:=length inv_start_regs);[|reflexivity].
   intros r R;apply lay_app_l;lia. }
 destruct (xbind_sound rho (beta++betaN) (fn_params f_secp256k1_modinv64_var) inv_start_args
  (PTree.empty sx) inv_start_temps (create_undef_temps (fn_temps f_secp256k1_modinv64_var)) inv_start_bind_ok)
  as (le & Bind & Temps).
 { intros id x Eq;rewrite PTree.gempty in Eq;discriminate. }
 rewrite Arguments in Bind.
 assert (Match : ematch (beta++betaN) (snd inv_start_alloc) e).
 { intro id;split.
   - rewrite Env;destruct (vlookup (snd inv_start_alloc) id) as [[r ty]|];[reflexivity|apply PTree.gempty].
   - intros r ty Lookup;exact (proj1 (proj2 (proj2 (Index id r ty Lookup)))). }
 assert (RStart : rep rho (beta++betaN) (sregs inv_start_state) mi) by (rewrite inv_start_state_regs;exact Start).
 assert (TStart : tmatch rho (beta++betaN) (stemps inv_start_state) le) by (rewrite inv_start_state_temps;exact Temps).
 destruct (exec_inv_initializers rho (beta++betaN) e le mi RStart TStart Match)
  as (lef & mf & Exec & Out & TFinal & Words & Frame).
 exists betaN,e,le,mi,lef,mf;split.
 - constructor;[exact Vars|exact Params|exact Disjoint|exact Alloc|exact Bind].
 - split;[exact Exec|];split;[exact Out|];split;[exact TFinal|];split;[exact Match|];
   split.
   + intro later;split;[apply inv_initial_de_bounds|].
     intros high i I;rewrite inv_initial_de_word by exact I;apply Words;exact I.
   + split;[exact Fresh|]. eapply lframe_trans;[|exact Frame].
     eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|];intros;exact I.
Qed.
