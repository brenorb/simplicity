(** Symbolic checkpoints of the unchanged scalar_cadd_bit body. The four
    selector calls are executed separately with their proved C arguments;
    all intervening statements retain the existing executor and shift oracle. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep C.jet_sx_pure
 C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_scalar_cadd_control
 C.jet_secp_u128_mul_exec C.jet_secp_u128_shift64_oracle.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition cadd_table : list (ident*fentry) :=
 [(_secp256k1_u128_from_u64,FInt f_secp256k1_u128_from_u64);
  (_secp256k1_u128_accum_u64,FInt f_secp256k1_u128_accum_u64);
  (_secp256k1_u128_to_u64,FInt f_secp256k1_u128_to_u64);
  (_secp256k1_u128_rshift,FOra f_secp256k1_u128_rshift u128_shift64_oracle)].

Lemma cadd_table_ok id ent : flookup cadd_table id=Some ent ->
 (exists b,Genv.find_symbol secp_ge id=Some b /\ Genv.find_funct_ptr secp_ge b=Some (Internal (fentry_fd ent))) /\
 match ent with FInt _=>True | FOra fd o=>oracle_ok secp_ge (fun _ _=>True)
  (fun _ _ _=>True) (fun _=>False) fd o end.
Proof.
 intro H;cbn [cadd_table flookup] in H.
 repeat match type of H with
 | (if Pos.eqb ?a id then _ else _)=_ =>
   let E:=fresh in destruct (Pos.eqb a id) eqn:E;
   [apply Pos.eqb_eq in E;subst id;inversion H;subst ent;clear H|]
 end;try discriminate.
 all:split;[apply secp_pure_ok;unfold secp_pure;repeat (first [left;reflexivity|right])|].
 all:first [exact I|exact u128_shift64_oracle_correct].
Qed.

Definition cadd_initial_regs := [mkreg (u64_cells 0 [XLv 0;XLv 1;XLv 2;XLv 3]) true (Some 32)].
Definition cadd_args (flag:bool) := [XP 0 0;XIc Int.zero;XIc (if flag then Int.one else Int.zero)].
Definition cadd_allocated := Eval vm_compute in
 match xalloc (std_cells (genv_cenv secp_ge)) (genv_cenv secp_ge)
  (fn_vars f_secp256k1_scalar_cadd_bit) 1 with Some p=>p |None=>([],[]) end.
Definition cadd_initial_temps (flag:bool) := PTree.set _flag (XIc (if flag then Int.one else Int.zero))
 (PTree.set _bit (XIc Int.zero) (PTree.set _r (XP 0 0) (PTree.empty sx))).
Definition cadd_initial_state flag := mkst (cadd_initial_temps flag) (cadd_initial_regs++fst cadd_allocated) [] 4.
Definition cadd_prefix_run flag := xstmt (genv_cenv secp_ge) [] cadd_table 200
 (snd cadd_allocated) (cadd_initial_state flag) cadd_prefix_statement.
Definition cadd_prefix_tree := Eval vm_compute in fun flag=>cadd_prefix_run flag.
Definition cadd_prefix_state flag := match cadd_prefix_tree flag with Some (RDone st _)=>st | _=>cadd_initial_state flag end.
Lemma cadd_prefix_run_eq flag : cadd_prefix_run flag=Some (RDone (cadd_prefix_state flag) ONormal).
Proof. destruct flag;reflexivity. Qed.

Definition cadd_selector_run flag j st := xfun (genv_cenv secp_ge) [] (int_table u128_mul_functions) 100
 f_secp256k1_u128_accum_u64 [XP 1 0;XLc (cadd_selector_value flag j)] (sregs st) [] 0.
Definition cadd_selector_next st result := mkst (stemps st) (sregs result) (slog st) (snv st).
Definition cadd_gap_run j st := xstmt (genv_cenv secp_ge) [] cadd_table 200 (snd cadd_allocated) st
 (if Nat.ltb j 3 then cadd_gap_statement j else cadd_tail).
Fixpoint cadd_walk flag n : option sstate :=
 match n with
 | O=>Some (cadd_prefix_state flag)
 | S j=>match cadd_walk flag j with
   | Some st=>match cadd_selector_run flag j st with
     | Some (RDone called ONormal)=>match cadd_gap_run j (cadd_selector_next st called) with
       | Some (RDone result ONormal)=>Some result | _=>None end
     | _=>None end
   | None=>None end
 end.
Definition cadd_walk_tree := Eval vm_compute in fun flag=>cadd_walk flag 4.
Definition cadd_final_state flag := match cadd_walk_tree flag with Some st=>st |None=>cadd_initial_state flag end.
Lemma cadd_walk_complete flag : cadd_walk flag 4=Some (cadd_final_state flag).
Proof. destruct flag;reflexivity. Qed.

Definition cadd_checkpoint flag j := match cadd_walk flag j with Some st=>st |None=>cadd_initial_state flag end.
Definition cadd_called_state flag j := match cadd_selector_run flag j (cadd_checkpoint flag j) with
 Some (RDone st _)=>st | _=>cadd_initial_state flag end.
Definition cadd_selected_state flag j := cadd_selector_next (cadd_checkpoint flag j) (cadd_called_state flag j).

Lemma cadd_checkpoint_present flag j : (j<=4)%nat -> cadd_walk flag j=Some (cadd_checkpoint flag j).
Proof. intro J;destruct j as [|[|[|[|[|j]]]]];try lia;destruct flag;timeout 10 (vm_compute;reflexivity). Qed.
Lemma cadd_selector_run_eq flag j : (j<4)%nat -> cadd_selector_run flag j (cadd_checkpoint flag j)=
 Some (RDone (cadd_called_state flag j) ONormal).
Proof. intro J;destruct j as [|[|[|[|j]]]];try lia;destruct flag;timeout 10 (vm_compute;reflexivity). Qed.
Lemma cadd_selector_log_nil flag j : (j<4)%nat -> slog (cadd_called_state flag j)=[].
Proof. intro J;destruct j as [|[|[|[|j]]]];try lia;destruct flag;timeout 10 (vm_compute;reflexivity). Qed.
Lemma cadd_selector_return flag j : (j<4)%nat -> (stemps (cadd_called_state flag j))!1%positive=None.
Proof. intro J;destruct j as [|[|[|[|j]]]];try lia;destruct flag;timeout 10 (vm_compute;reflexivity). Qed.
Lemma cadd_gap_run_eq flag j : (j<4)%nat -> cadd_gap_run j (cadd_selected_state flag j)=
 Some (RDone (cadd_checkpoint flag (S j)) ONormal).
Proof. intro J;destruct j as [|[|[|[|j]]]];try lia;destruct flag;timeout 10 (vm_compute;reflexivity). Qed.

Definition cadd_bit_expression flag := match (stemps (cadd_prefix_state flag))!_bit with
 | Some x=>x | None=>XIc Int.zero end.
Lemma cadd_checkpoint_bit flag j : (j<=4)%nat ->
 (stemps (cadd_checkpoint flag j))!_bit=Some (cadd_bit_expression flag).
Proof. intro J;destruct j as [|[|[|[|[|j]]]]];try lia;destruct flag;timeout 10 (vm_compute;reflexivity). Qed.
Lemma cadd_bit_expression_value rho layout flag :
 den rho layout (cadd_bit_expression flag)=Vint (cadd_bit_setting flag).
Proof. destruct flag;timeout 10 (vm_compute;reflexivity). Qed.
Lemma cadd_checkpoint_shape flag j : (j<=4)%nat ->
 map rshape (sregs (cadd_checkpoint flag j))=map rshape (cadd_initial_regs++fst cadd_allocated).
Proof. intro J;destruct j as [|[|[|[|[|j]]]]];try lia;destruct flag;timeout 10 (vm_compute;reflexivity). Qed.
Lemma cadd_selected_shape flag j : (j<4)%nat ->
 map rshape (sregs (cadd_selected_state flag j))=map rshape (cadd_initial_regs++fst cadd_allocated).
Proof. intro J;destruct j as [|[|[|[|j]]]];try lia;destruct flag;timeout 10 (vm_compute;reflexivity). Qed.
Lemma cadd_selected_temps flag j : stemps (cadd_selected_state flag j)=stemps (cadd_checkpoint flag j).
Proof. reflexivity. Qed.
Lemma cadd_checkpoint_first flag : cadd_checkpoint flag 0=cadd_prefix_state flag.
Proof. reflexivity. Qed.
Lemma cadd_checkpoint_last flag : cadd_checkpoint flag 4=cadd_final_state flag.
Proof. unfold cadd_checkpoint;rewrite cadd_walk_complete;reflexivity. Qed.
Lemma cadd_allocation :
 xalloc (std_cells (genv_cenv secp_ge)) (genv_cenv secp_ge)
  (fn_vars f_secp256k1_scalar_cadd_bit) 1=Some cadd_allocated.
Proof. reflexivity. Qed.
Lemma cadd_binding flag : xbind (fn_params f_secp256k1_scalar_cadd_bit)
 (cadd_args flag) (PTree.empty sx)=Some (cadd_initial_temps flag).
Proof. destruct flag;reflexivity. Qed.
Lemma cadd_local_lookup id : vlookup (snd cadd_allocated) id=
 if Pos.eqb id _t then Some (1%nat,Tstruct _secp256k1_uint128 noattr) else None.
Proof.
 change ((if Pos.eqb _t id then Some (1%nat,Tstruct _secp256k1_uint128 noattr) else None)=
  (if Pos.eqb id _t then Some (1%nat,Tstruct _secp256k1_uint128 noattr) else None)).
 rewrite Pos.eqb_sym;reflexivity.
Qed.

Local Opaque cadd_prefix_state cadd_final_state cadd_checkpoint cadd_called_state cadd_selected_state.
