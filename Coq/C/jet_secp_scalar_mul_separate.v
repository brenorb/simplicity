(** Complete original scalar_mul into a distinct uninitialized destination.
    The second operand may be a readonly global. Both operands survive the
    product, reduction and actual stack free; no intermediate call is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_add_reader_support
 C.jet_secp_scalar_mul512_borrowed C.jet_secp_scalar_mul512_low
 C.jet_secp_scalar_borrowed_inputs C.jet_secp_scalar_mul_reader_bridge
 C.jet_secp_scalar_mul_borrowed_alloc C.jet_secp_scalar_mul_borrowed_function
 C.jet_secp_scalar_mul_caller_alloc C.jet_secp_scalar_mul_caller_body C.jet_secp_scalar_mul_caller_function
 C.jet_secp_scalar_shift384_function C.jet_secp_product_reduce_bridge C.jet_secp_scalar_reduce512_run
 C.jet_secp_reduce512_fresh_runs C.jet_secp_reduce512_fresh_function
 C.jet_secp_reduce512_body_numeric C.jet_secp_scalar_mul_separate_support
 C.jet_secp_slice_permissions C.jet_secp_closed_helpers C.jet_clight_internal_frame
 C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem eval_scalar_mul_borrowed_separate rho beta m br :
 rep rho beta scalar_mul_borrowed_inputs m -> Mem.range_perm m br 0 32 Cur Freeable ->
 (forall r,(r<2)%nat -> br<>blk beta r) ->
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul)
 [Vptr br Ptrofs.zero;Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
  Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
 scalar_at mf br 0 (map Int64.repr (scalar_limbs_of
  ((scalar_mul512_input_value rho 0*scalar_mul512_input_value rho 4) mod canonical_group_order))) /\
 rep rho beta scalar_mul_borrowed_inputs mf /\ Mem.range_perm mf br 0 32 Cur Freeable /\
 keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun b ofs=>b<>br /\ ~foot beta (map rshape scalar_mul_borrowed_inputs) b ofs) m mf.
Proof.
 intros Inputs Free Separate;destruct (Mem.alloc m 0 64) as [ma bl] eqn:Alloc.
 pose proof (scalar_mul_borrowed_allocates rho beta m ma bl Inputs Alloc) as Initial.
 destruct (eval_scalar_mul512_borrowed_product rho (scalar_mul_stack_layout beta bl) ma Initial)
  as (mp & ProductCall & Loads & ProductValue & ProductRep & ProductFrame).
 assert (KeepP:keeps_permissions ma mp) by
  (eapply secp_internal_keeps_permissions;[exact shift384_product_closed|reflexivity|exact ProductCall]).
 assert (FreeP:Mem.range_perm mp br 0 32 Cur Freeable).
 { intros pos Range;apply KeepP;eapply Mem.perm_alloc_1;[exact Alloc|apply Free;exact Range]. }
 assert (Fresh:~Mem.valid_block m bl) by (eapply Mem.fresh_block_alloc;exact Alloc).
 assert (Different:br<>bl).
 { intro Eq;apply Fresh;rewrite <-Eq;eapply Mem.perm_valid_block;apply (Free 0);lia. }
 pose proof (fresh_product_reduce_rep rho (scalar_mul_stack_layout beta bl) br mp ProductRep FreeP Different) as ReduceInput.
 change (rep (product_reduce_rho rho) [(br,0);(bl,0)] reduce512_fresh_initial_regs mp) in ReduceInput.
 destruct (eval_reduce512_fresh_storage (product_reduce_rho rho) br bl mp ReduceInput)
  as (mb & ReduceCall & Output & Reduced & FreeB & FreeL & KeepR & PreserveR & ReduceFrame).
 rewrite product_reduce_integer in Output.
 assert (RF:lframe (fun b _=>b<>br /\ b<>bl) mp mb).
 { eapply lframe_implies;[exact ReduceFrame|];intros b ofs [NotR NotL] Valid.
   intros (r & sh & d & ch & Nth & Cell & Eq & Bytes);destruct r as [|[|r]].
   - apply NotR;exact Eq.
   - apply NotL;exact Eq.
   - cbn [reduce512_fresh_initial_regs reduce512_forget_destination scalar_reduce512_initial_regs map nth_error] in Nth;
     destruct r;discriminate. }
 assert (InputsP:rep rho beta scalar_mul_borrowed_inputs mp) by
  exact (shift384_inputs_after_product rho beta bl m mp Inputs ProductRep).
 assert (InputValid:forall r,(r<2)%nat -> Mem.valid_block m (blk beta r)).
 { intros r Range;apply (scalar_mul_borrowed_inputs_valid rho beta m Inputs);apply blk_in.
   destruct Inputs as (Length & _);rewrite Length;exact Range. }
 assert (NotLocal:forall r,(r<2)%nat -> blk beta r<>bl).
 { intros r Range Eq;apply Fresh;rewrite <-Eq;apply InputValid;exact Range. }
 assert (InputsB:rep rho beta scalar_mul_borrowed_inputs mb).
 { eapply shift384_inputs_lframe;[exact InputsP|exact RF|].
   intros r pos Range;split;[intro Eq;apply (Separate r Range);symmetry;exact Eq|apply NotLocal;exact Range]. }
 destruct (free_list_exists [(bl,0,64)] mb) as (mf & Freed & Unchanged).
 { constructor;[cbn;tauto|constructor]. }
 { intros b lo hi [Eq|[]];injection Eq as <- <- <-;exact FreeL. }
 assert (FreeFrame:lframe (fun b _=>b<>bl) mb mf).
 { apply lframe_unchanged;eapply Mem.unchanged_on_implies;[exact Unchanged|].
   intros b pos Away Valid;change (~(bl=b \/ False));intros [Eq|[]];congruence. }
 assert (InputsF:rep rho beta scalar_mul_borrowed_inputs mf).
 { eapply shift384_inputs_lframe;[exact InputsB|exact FreeFrame|];intros r pos Range;apply NotLocal;exact Range. }
 change (Clight2.eval_funcall secp_ge ma (Internal f_secp256k1_scalar_mul_512)
  [Vptr bl Ptrofs.zero;Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mp Vundef) in ProductCall.
 assert (Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul)
  [Vptr br Ptrofs.zero;Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef).
 { eapply eval_funcall_internal with (e:=scalar_mul_caller_env (scalar_mul_stack_layout beta bl))
   (le1:=scalar_mul_separate_temps beta br) (le2:=scalar_mul_separate_temps beta br)
   (m1:=ma) (m2:=mb) (out:=Out_normal).
   - apply scalar_mul_separate_entry;exact Alloc.
   - apply exec_scalar_mul_separate_calls with (mp:=mp);assumption.
   - constructor.
   - rewrite scalar_mul_caller_env_blocks;exact Freed. }
 exists mf;split;[exact Call|];split.
 - eapply scalar_at_lframe;[exact Output|exact FreeFrame|intros;exact Different].
 - split;[exact InputsF|];split.
   + intros pos Range;apply (proj1 (proj2 FreeFrame)) with (b:=br);
     [eapply Mem.perm_valid_block;apply (FreeB 0);lia|exact Different|apply FreeB;exact Range].
   + split.
     * eapply secp_internal_keeps_permissions;[exact scalar_mul_separate_closed|reflexivity|exact Call].
     * split.
       { eapply (secp_closed_function_preserved f_secp256k1_scalar_mul);
         [exact scalar_mul_separate_closed|reflexivity|exact Call]. }
       set (P:=fun b ofs=>Mem.valid_block m b /\ b<>br /\
        ~foot beta (map rshape scalar_mul_borrowed_inputs) b ofs).
       assert (Frame:lframe P m mf).
       { eapply lframe_trans with (m2:=ma).
         - apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc.
         - eapply lframe_trans with (m2:=mp).
           + eapply lframe_implies;[exact ProductFrame|];intros b ofs (Valid & NotR & Outside) ValidA Foot.
             destruct (borrowed_stack_foot_cases beta bl b ofs Foot) as [Eq|Inside];
             [subst b;contradiction|contradiction].
           + eapply lframe_trans with (m2:=mb).
             * eapply lframe_implies;[exact RF|];intros b ofs (Valid & NotR & Outside) ValidP.
               split;[exact NotR|intro Eq;subst b;contradiction].
             * eapply lframe_implies;[exact FreeFrame|];intros b ofs (Valid & NotR & Outside) ValidB Eq;
               subst b;contradiction. }
       eapply lframe_implies;[exact Frame|];intros b ofs Outside Valid;split;[exact Valid|exact Outside].
Qed.

Theorem eval_scalar_mul_separate_values a b m br ba bb :
 0<=a<2^256 -> 0<=b<2^256 -> br<>ba -> br<>bb -> ba<>bb ->
 scalar_at m ba 0 (map Int64.repr (scalar_limbs_of a)) ->
 scalar_at m bb 0 (map Int64.repr (scalar_limbs_of b)) ->
 Mem.range_perm m ba 0 32 Cur Freeable -> Mem.range_perm m br 0 32 Cur Freeable ->
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul)
 [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf br 0 (map Int64.repr (scalar_limbs_of ((a*b) mod canonical_group_order))) /\
 rep (scalar_mul_reader_rho a b) [(ba,0);(bb,0)] scalar_mul_borrowed_inputs mf /\
 Mem.range_perm mf br 0 32 Cur Freeable /\ keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun block _=>block<>br /\ block<>ba /\ block<>bb) m mf.
Proof.
 intros A B RA RB AB StoredA StoredB FA FR.
 pose proof (scalar_borrowed_inputs_from_storage a b m ba bb StoredA StoredB FA AB) as Inputs.
 destruct (eval_scalar_mul_borrowed_separate (scalar_mul_reader_rho a b) [(ba,0);(bb,0)] m br
  Inputs FR ltac:(intros [|[|r]] Range;[exact RA|exact RB|lia]))
  as (mf & Call & Output & InputsF & Free & Keep & Preserve & Frame).
 destruct (scalar_mul_reader_input_values a b A B) as [VA VB];rewrite VA,VB in Output.
 exists mf;split;[exact Call|];split;[exact Output|];split;[exact InputsF|];split;[exact Free|];
 split;[exact Keep|];split;[exact Preserve|].
 eapply lframe_implies;[exact Frame|];intros block ofs (NotR & NotA & NotB) Valid;split;[exact NotR|].
 intros (r & sh & d & ch & Nth & Cell & Eq & Bytes);destruct r as [|[|r]].
 - apply NotA;exact Eq.
 - apply NotB;exact Eq.
 - cbn [scalar_mul_borrowed_inputs map nth_error] in Nth;destruct r;discriminate.
Qed.
