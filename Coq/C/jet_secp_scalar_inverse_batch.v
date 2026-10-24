(** One complete original scalar inverse loop body. The sole execution
    boundary left as a premise is the original CTZ helper, at this memory.
    No public registration or new external semantics follows from this file. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.extraMath C.divstep C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_modinv_entry_modulus C.jet_secp_modinv_loop_modulus
 C.jet_secp_modinv_seed_modulus C.jet_secp_modinv_batch_modulus
 C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_de C.jet_secp_modinv_var_fg
 C.jet_secp_modinv_var_zero C.jet_secp_modinv_var_shorten C.jet_secp_modinv_var_post
 C.jet_secp_modinv_var_tail C.jet_secp_modinv_var_invariant C.jet_secp_modinv_var_ranges
 C.jet_secp_modinv_var_batch_exit C.jet_secp_modinv_var_batch_update
 C.jet_secp_scalar_inverse_iteration C.jet_secp_scalar_de_ranges C.jet_secp_scalar_de_invariant
 C.jet_secp_scalar_de_exec C.jet_secp_scalar_de_numeric C.jet_secp_scalar_normalize62
 C.jet_secp_modinv_de_numeric C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_body C.jet_secp_modinv_fg_loop_numeric
 C.jet_secp_canonical_scalar C.jet_secp_modinv_normalize62_words.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma scalar_inv_batch_body_source : inv_caller_loop_body=Ssequence Sskip
 (Ssequence (Ssequence inv_divstep_batch inv_return_eta) inv_after_divsteps).
Proof. reflexivity. Qed.
Lemma scalar_inv_batch_de_bounds st rho : scalar_de62_state_bounds(inv_de_rho rho) ->
 scalar_de62_state_bounds(inv_de_rho(inv_batch_result_rho st rho)).
Proof.
 intros(Limbs & Values);split.
 - intros high i I;rewrite inv_batch_de_word by exact I;apply Limbs;exact I.
 - intro high;rewrite inv_batch_de_value;apply Values.
Qed.
Lemma scalar_inv_batch_link st rho value : scalar_de62_coefficient_link value (inv_de_rho rho) st ->
 scalar_de62_coefficient_link value (inv_de_rho(inv_batch_result_rho st rho)) st.
Proof. intros Link high;unfold scalar_de62_coefficient_link in *;rewrite inv_batch_de_value;apply Link. Qed.

Definition scalar_inv_batch_rho len st rho := scalar_inv_iteration_rho len (inv_batch_result_rho st rho).
Definition scalar_inv_batch_length len st rho := scalar_inv_iteration_length len (inv_batch_result_rho st rho).
Definition scalar_inv_batch_frame beta b ofs := b<>blk beta 6 /\
 ~foot (inv_de_layout beta) (map rshape scalar_de62_regs) b ofs /\
 ~foot (inv_fg_layout beta) (map rshape fg_regs) b ofs /\ b<>blk beta 4 /\ b<>blk beta 5.

Theorem exec_scalar_inv_batch value len rho st beta e le m :
 (forall x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 m (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 -683<=eta st<683 -> (0<len<=5)%nat -> rep rho beta (inv_mod_seed_regs modinfo_scalar_limb) m ->
 ematch beta (snd inv_start_alloc) e -> le!_eta=Some(Vlong(Int64.repr(eta st))) ->
 le!_modinfo=Some(Vptr(blk beta 1)(Ptrofs.repr(bas beta 1))) ->
 le!_len=Some(Vint(Int.repr(Z.of_nat len))) ->
 scalar_de62_state_bounds(inv_de_rho rho) -> inv_state_matches len rho st ->
 scalar_de62_coefficient_link value (inv_de_rho rho) st ->
 inv_fg_limb_bounds rho -> inv_fg_value_capacity len rho -> exists lef mf out,
 Clight2.exec_stmt secp_ge e le m inv_caller_loop_body E0 lef mf out /\
 rep (scalar_inv_batch_rho len st rho) beta (inv_mod_loop_regs modinfo_scalar_limb) mf /\
 lef!_len=Some(Vint(Int.repr(Z.of_nat(scalar_inv_batch_length len st rho)))) /\
 lef!_eta=Some(Vlong(Int64.repr(eta(fst(stepN 62 st))))) /\
 scalar_de62_state_bounds(inv_de_rho(scalar_inv_batch_rho len st rho)) /\
 scalar_de62_coefficient_link value (inv_de_rho(scalar_inv_batch_rho len st rho)) (fst(stepN 62 st)) /\
 inv_state_matches (scalar_inv_batch_length len st rho) (scalar_inv_batch_rho len st rho) (fst(stepN 62 st)) /\
 inv_fg_limb_bounds(scalar_inv_batch_rho len st rho) /\
 inv_fg_value_capacity (scalar_inv_batch_length len st rho) (scalar_inv_batch_rho len st rho) /\
 (g st=0 -> out=Out_break /\
  de62_input_value(inv_de_rho(scalar_inv_batch_rho len st rho)) false mod canonical_group_order=
  de62_input_value(inv_de_rho rho) false mod canonical_group_order) /\
 (out=Out_break <-> g(fst(stepN 62 st))=0) /\ (out=Out_break \/ out=Out_normal) /\
 (0<scalar_inv_batch_length len st rho<=5)%nat /\
 (forall id,id<>_eta -> id<>_t'1 -> id<>_t'7 -> id<>_t'8 ->
   ~In id inv_post_modified -> lef!id=le!id) /\
 lframe(scalar_inv_batch_frame beta) m mf.
Proof.
 intros CountCall EtaRange Length Rep Env Eta Modinfo Len Bounds State Link Limbs Capacity.
 destruct(exec_inv_mod_batch modinfo_scalar_limb len rho st beta e le m CountCall EtaRange Length Rep Env Eta State)
  as(mb & Batch & BatchRep & Matrix & BFrame).
 set (r:=inv_batch_result_rho st rho).
 set (le1:=PTree.set _eta (Vlong(Int64.repr(eta(fst(stepN 62 st))))) (inv_divstep_returned st rho le)).
 assert(Assign:Clight2.exec_stmt secp_ge e (inv_divstep_returned st rho le) mb inv_return_eta E0 le1 mb Out_normal).
 { rewrite inv_return_eta_source;apply exec_Sset;apply eval_Etempvar;apply PTree.gss. }
 assert(Modinfo1:le1!_modinfo=Some(Vptr(blk beta 1)(Ptrofs.repr(bas beta 1)))).
 { unfold le1;rewrite PTree.gso by discriminate;rewrite inv_divstep_returned_outside by discriminate;exact Modinfo. }
 assert(Len1:le1!_len=Some(Vint(Int.repr(Z.of_nat len)))).
 { unfold le1;rewrite PTree.gso by discriminate;rewrite inv_divstep_returned_outside by discriminate;exact Len. }
 assert(FG:forall high j,(j<5)%nat -> Z.abs(Int64.signed(fg_array_word(inv_fg_rho len r) high j))<=2^62).
 { intros high j J;rewrite inv_fg_limb_array by exact J;apply inv_batch_fg_bounds;[exact Limbs|exact J]. }
 destruct(exec_scalar_inv_after_divsteps value len r st beta e le1 mb Length BatchRep Env Modinfo1 Len1
  (scalar_inv_batch_de_bounds st rho Bounds) (inv_batch_state_matches st len rho Length State) Matrix
  (scalar_inv_batch_link st rho value Link) FG)
  as(lef & mf & out & Updates & Post & NewLen & NewDE & NewLink & NewState & Low & Zero & NextBounds &
   DENumeric & FGNumeric & Stop & Nonzero & Outcomes & Range & TFrame & Frame).
 destruct(NextBounds (inv_batch_fg_capacity st len rho Length Capacity)) as(NewLimbs & NewCapacity).
 assert(NewEta:lef!_eta=Some(Vlong(Int64.repr(eta(fst(stepN 62 st)))))).
 { rewrite(inv_post_eta_preserved le1 lef TFrame);unfold le1;apply PTree.gss. }
 assert(ZeroNext:g st=0 -> out=Out_break /\
  de62_input_value(inv_de_rho(scalar_inv_batch_rho len st rho)) false mod canonical_group_order=
  de62_input_value(inv_de_rho rho) false mod canonical_group_order).
 { intro Z;destruct(Zero Z) as(Break & D);split;[exact Break|].
   unfold r in D;rewrite inv_batch_de_value in D;exact D. }
 assert(StopNext:out=Out_break <-> g(fst(stepN 62 st))=0).
 { rewrite Stop;rewrite(proj2 NewState);reflexivity. }
 assert(Temps:forall id,id<>_eta -> id<>_t'1 -> id<>_t'7 -> id<>_t'8 ->
  ~In id inv_post_modified -> lef!id=le!id).
 { intros id E T1 T7 T8 Outside;rewrite(TFrame id Outside);unfold le1;
   rewrite PTree.gso by congruence;apply inv_divstep_returned_outside;assumption. }
 exists lef,mf,out;split.
 - rewrite scalar_inv_batch_body_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0)
    (m1:=m) (le1:=le);[constructor|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mb) (le1:=le1);[|exact Updates].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Batch|exact Assign].
 - split;[exact Post|];split;[exact NewLen|];split;[exact NewEta|];split;[exact NewDE|];
   split;[exact NewLink|];split;[exact NewState|];split;[exact NewLimbs|];split;[exact NewCapacity|];
   split;[exact ZeroNext|];split;[exact StopNext|];split;[exact Outcomes|];split;[exact Range|];split;[exact Temps|].
   eapply lframe_trans;[eapply lframe_implies;[exact BFrame|]|eapply lframe_implies;[exact Frame|]];
   intros b ofs [B Rest] Valid;tauto.
Qed.
