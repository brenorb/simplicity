(** Actual fe_set_int(0/1) at any aligned writable field slice, including
    uninitialized ratio-array entries. This executes set_int itself. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep C.jet_sx_pure
 C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_secp_b32_exec
 C.jet_secp_point_set_bit C.jet_secp_fe_set_owned C.jet_secp_field_slice_product
 C.jet_secp_multiply_normalize_bridge C.jet_secp_slice_permissions C.jet_clight_internal_permissions
 C.jet_secp_closed_helpers C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition field_slice_set_regs := [fe_undef].
Definition field_slice_set_run (bit:bool) := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 100
 f_secp256k1_fe_set_int [XP 0 0;XI (if bit then Int.one else Int.zero)] field_slice_set_regs [] 0.
Definition field_slice_set_tree := Eval vm_compute in fun bit=>match bit with
 | true=>field_slice_set_run true | false=>field_slice_set_run false end.
Definition field_slice_set_state bit := match field_slice_set_tree bit with
 | Some (RIf _ (RDone st _) _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end.
Lemma field_slice_set_run_eq bit : field_slice_set_run bit=Some
 (RIf (point_set_bit_cond bit) (RDone (field_slice_set_state bit) ONormal) (RDone (field_slice_set_state bit) ONormal)).
Proof. destruct bit;reflexivity. Qed.
Lemma field_slice_set_selected bit rho beta : rsel rho (lay beta)
 (RIf (point_set_bit_cond bit) (RDone (field_slice_set_state bit) ONormal) (RDone (field_slice_set_state bit) ONormal))=
 (field_slice_set_state bit,ONormal).
Proof. cbn [rsel];destruct (truth rho (lay beta) (point_set_bit_cond bit));reflexivity. Qed.
Lemma field_slice_set_return bit : (stemps (field_slice_set_state bit))!1%positive=None.
Proof. destruct bit;reflexivity. Qed.
Lemma field_slice_set_output bit : sregs (field_slice_set_state bit)=
 [mkreg (u64_cells 0 (fe_set_out bit)) true None].
Proof. destruct bit;reflexivity. Qed.
Lemma field_slice_set_log_nil bit : leaves_log_nil
 (RIf (point_set_bit_cond bit) (RDone (field_slice_set_state bit) ONormal) (RDone (field_slice_set_state bit) ONormal))=true.
Proof. destruct bit;reflexivity. Qed.
Local Opaque field_slice_set_state.

Theorem eval_field_slice_set (bit:bool) m b base :
 0<=base -> (8|base) -> base+40<=Ptrofs.max_unsigned ->
 Mem.range_perm m b base (base+40) Cur Writable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_set_int)
  [Vptr b (Ptrofs.repr base);Vint (if bit then Int.one else Int.zero)] E0 mf Vundef /\
 fe_at mf b base (words5 (point_set_bit_words bit)) /\ keeps_permissions m mf /\
 lframe (fun bx pos=>bx<>b \/ pos<base \/ base+40<=pos) m mf /\ readonly_preserved m mf.
Proof.
 intros Base Align Max Space;set (rho:=fun _ : nat=>Int64.zero).
 assert (Initial:rep rho [(b,base)] field_slice_set_regs m).
 { apply (rep_add _ [] [] m b base);[apply rep_nil|cbn;tauto|].
   apply region_fe_undefined_from_storage;assumption. }
 destruct (xfun_pure secp_ge secp_pure secp_pure_ok 100 f_secp256k1_fe_set_int
   [XP 0 0;XI (if bit then Int.one else Int.zero)] field_slice_set_regs 0 _
   (field_slice_set_run_eq bit) (field_slice_set_log_nil bit) rho [(b,base)] m Initial)
  as (mf & result & Call & Rep & Ret & Shape & Frame).
 rewrite field_slice_set_selected in Rep,Ret;cbn [fst] in Rep,Ret;
  rewrite field_slice_set_return in Ret;subst result;rewrite field_slice_set_output in Rep.
 change (map (den rho (lay [(b,base)])) [XP 0 0;XI (if bit then Int.one else Int.zero)]) with
  [Vptr b (Ptrofs.repr (base+0));Vint (if bit then Int.one else Int.zero)] in Call.
 rewrite Z.add_0_r in Call.
 exists mf;split;[exact Call|];split.
 - apply (field_slice_region_words rho [(b,base)] mf 0 (fe_set_out bit) (point_set_bit_words bit));
    [exact (rep_region _ _ _ mf 0 _ Rep eq_refl)|destruct bit;reflexivity|destruct bit;reflexivity].
 - split.
   + eapply (secp_internal_keeps_permissions f_secp256k1_fe_set_int);[reflexivity|reflexivity|exact Call].
   + split.
     * eapply lframe_implies;[exact Frame|].
       intros bx pos Outside Valid (r & sh & d & ch & Nth & Cell & Same & Range).
       destruct r as [|r];[|destruct r;discriminate Nth].
       cbn [field_slice_set_regs map nth_error rshape rcells rw rfree] in Nth;injection Nth as <-.
       cbn [blk bas lay nth fst snd] in Same,Range;subst bx.
       cbn [fe_undef rshape rcells rw rfree fst map cshape cofs cchunk In] in Cell;
        repeat match type of Cell with _ \/ _=>destruct Cell as [Cell|Cell] end;
        try contradiction;inversion Cell;subst d ch;change (size_chunk Mint64) with 8 in Range;
        destruct Outside;intuition lia.
     * eapply (secp_closed_function_preserved f_secp256k1_fe_set_int);[reflexivity|reflexivity|exact Call].
Qed.
