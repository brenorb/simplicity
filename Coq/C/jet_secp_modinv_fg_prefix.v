(** Original variable-length inverse transition: initialization through the
    two signed accumulator shifts. This is a statement-prefix proof, not a
    whole inverse or public-jet theorem. The remaining loop, function entry
    and cleanup must be composed separately. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_eval C.jet_sx_pure C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix.
Require Import C.jet_secp_i128_shift62_oracle.
Require Import C.jet_secp_symbolic_substitution C.jet_secp_i128_mul_exec C.jet_secp_i128_shift62_rep.
Require Import C.jet_secp_i128_shift62.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition fg_regs :=
 [mkreg (u64_cells 0 [XLv 0;XLv 1;XLv 2;XLv 3;XLv 4]) true (Some 40);
  mkreg (u64_cells 0 [XLv 5;XLv 6;XLv 7;XLv 8;XLv 9]) true (Some 40);
  mkreg (u64_cells 0 [XLv 10;XLv 11;XLv 12;XLv 13]) false None].
Definition fg_alloc := Eval vm_compute in
 match xalloc (std_cells (genv_cenv secp_ge)) (genv_cenv secp_ge)
 (fn_vars f_secp256k1_modinv64_update_fg_62_var) 3 with
 | Some p=>p | None=>([],[]) end.
Definition fg_temps := PTree.set _len (XL2I (XLv 14)) (PTree.set _t (XP 2 0)
 (PTree.set _g (XP 1 0) (PTree.set _f (XP 0 0) (PTree.empty sx)))).
Definition fg_initial := mkst fg_temps (fg_regs++fst fg_alloc) [] 15.
Definition fg_source_parts := split_statement_last (fn_body f_secp256k1_modinv64_update_fg_62_var).
Definition fg_prefix := statement_sequence (firstn 16 (fst fg_source_parts)) Sskip.
Definition fg_rest := statement_sequence (skipn 16 (fst fg_source_parts)) (snd fg_source_parts).
Definition fg_table := (_secp256k1_i128_rshift,FOra f_secp256k1_i128_rshift i128_shift62_oracle)::
 int_table secp_pure.
Definition fg_prefix_run := xstmt (genv_cenv secp_ge) [] fg_table 900 (snd fg_alloc) fg_initial fg_prefix.

Definition fg_prefix_tree := match fg_prefix_run with
 | Some tree=>tree | None=>RDone fg_initial ONormal end.
Local Definition fg_computed_tree := Eval vm_compute in fg_prefix_tree.
Local Lemma fg_prefix_tree_compute : fg_prefix_tree=fg_computed_tree.
Proof. reflexivity. Qed.
Lemma fg_prefix_run_eq : fg_prefix_run=Some fg_prefix_tree.
Proof. rewrite fg_prefix_tree_compute;vm_compute;reflexivity. Qed.
Lemma fg_source_split : fn_body f_secp256k1_modinv64_update_fg_62_var=
 statement_sequence (firstn 16 (fst fg_source_parts)) fg_rest.
Proof. reflexivity. Qed.
Lemma fg_table_correct id ent : flookup fg_table id=Some ent ->
 (exists b, Genv.find_symbol secp_ge id=Some b /\
 Genv.find_funct_ptr secp_ge b=Some (Internal (fentry_fd ent))) /\
 match ent with FInt _=>True | FOra fd o=>
 oracle_ok secp_ge (fun _ _=>True) (fun _ _ _=>True) (fun _=>False) fd o end.
Proof.
 unfold fg_table;cbn [flookup].
 destruct (Pos.eqb _secp256k1_i128_rshift id) eqn:E.
 - apply Pos.eqb_eq in E;subst id;intro H;inversion H;subst ent;split.
   + apply secp_pure_ok;unfold secp_pure;repeat first [left;reflexivity|right].
   + apply i128_shift62_oracle_correct.
 - intro H;destruct (int_table_lookup secp_pure id ent H) as (fd & -> & Member).
   split;[exact (secp_pure_ok id fd Member)|exact I].
Qed.
Lemma fg_prefix_normal rho beta : snd (rsel rho beta fg_prefix_tree)=ONormal.
Proof.
 rewrite fg_prefix_tree_compute;cbn [fg_computed_tree rsel].
 repeat match goal with |- context [if ?c then _ else _]=>destruct c end;reflexivity.
Qed.

Definition fg_product_sigma (a b : sx) (n : nat) :=
 match n with O=>a | S O=>b | _=>XLc Int64.zero end.
Definition fg_product_lo a b := sx_subst (fg_product_sigma a b) smul128_lo.
Definition fg_product_hi a b := sx_subst (fg_product_sigma a b) smul128_hi.
Definition fg_row_lo u v := XLb Badd (fg_product_lo u (XLv 0)) (fg_product_lo v (XLv 5)).
Definition fg_row_hi u v := XLb Badd (fg_product_hi u (XLv 0))
 (XLb Badd (fg_product_hi v (XLv 5))
  (XI2L Signed (XLcmp Clt Unsigned (fg_row_lo u v) (fg_product_lo v (XLv 5))))).
Definition fg_shifted_row u v :=
 [i128_shift62_lo_sx (fg_row_lo u v) (fg_row_hi u v);i128_shift62_hi_sx (fg_row_hi u v)].
Definition fg_prefix_out := fg_regs++
 [mkreg (u64_cells 0 (fg_shifted_row (XLv 10) (XLv 11))) true (Some 16);
  mkreg (u64_cells 0 (fg_shifted_row (XLv 12) (XLv 13))) true (Some 16)].
Lemma fg_prefix_regs_eq rho beta : sregs (fst (rsel rho beta fg_prefix_tree))=fg_prefix_out.
Proof.
 rewrite fg_prefix_tree_compute;cbn [fg_computed_tree rsel].
 repeat match goal with |- context [if ?c then _ else _]=>destruct c end;reflexivity.
Qed.

Local Opaque fg_prefix_tree fg_initial fg_table fg_prefix fg_alloc secp_ge xstmt.
Lemma fg_sound fuel : sound_rec secp_ge [] (fun _ _=>True) (fun _ _ _=>True) (fun _=>False)
 (xstmt (genv_cenv secp_ge) [] fg_table fuel).
Proof.
 apply xstmt_sound.
 - intros;exact I.
 - intros;contradiction.
 - exact fg_table_correct.
Qed.
Theorem exec_fg_prefix rho beta e le m :
 rep rho beta (sregs fg_initial) m -> tmatch rho beta (stemps fg_initial) le ->
 ematch beta (snd fg_alloc) e -> exists le' mf,
 Clight2.exec_stmt secp_ge e le m fg_prefix E0 le' mf Out_normal /\
 rep rho beta fg_prefix_out mf /\
 tmatch rho beta (stemps (fst (rsel rho (lay beta) fg_prefix_tree))) le' /\
 lframe (fun b ofs=>~foot beta (map rshape (sregs fg_initial)) b ofs) m mf.
Proof.
 intros Rep Temps Env.
 pose proof (fg_sound 900) as Sound.
 specialize (Sound (snd fg_alloc) fg_initial fg_prefix fg_prefix_tree fg_prefix_run_eq).
 destruct (Sound rho beta e le m Rep Temps Env)
  as (le' & mf & out & Exec & Post).
 - split;intros;discriminate.
 - intros r _ [].
 - exact I.
 - apply Forall_forall;intros;exact I.
 - destruct Post as (Out & Match & Normal & Shape & Inv & Frame).
   rewrite fg_prefix_normal in Normal;destruct out;cbn [outmatch] in Normal;try contradiction.
   rewrite fg_prefix_regs_eq in Out.
   exists le',mf;split;[exact Exec|];split;[exact Out|];split;[exact Match|].
   eapply lframe_implies;[exact Frame|].
   intros b ofs Outside Valid;split;[exact Valid|];split;[exact Outside|tauto].
Qed.
