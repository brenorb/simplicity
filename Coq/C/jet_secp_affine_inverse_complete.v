(** Complete original finite ge_set_gej_var call. The actual field inverse,
    arithmetic, affine stores and local frees are composed, with CTZ explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.extraMath C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_point_mul_storage
 C.jet_secp_multiply_checkpoint_columns C.jet_secp_invert_literal C.jet_secp_fe_inv_prefix
 C.jet_secp_fe_inverse_var C.jet_secp_fe_inverse_state C.jet_secp_modinfo_fe_caller
 C.jet_secp_gej_affine_entry C.jet_secp_gej_affine_arithmetic C.jet_secp_gej_affine_finish
 C.jet_secp_field_io_preserve C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words.

Lemma exec_affine_inverse_from_call le m mf bp b2 b3 :
 le!_a=Some(Vptr bp Ptrofs.zero) ->
 Clight2.eval_funcall secp_ge m(Internal f_secp256k1_fe_inv_var)
  [Vptr bp(Ptrofs.repr 80);Vptr bp(Ptrofs.repr 80)] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge(affine_local_env b2 b3)le m affine_inverse_statement E0 le mf Out_normal.
Proof.
 intros Point Call;unfold affine_inverse_statement;eapply exec_curve_call with
  (vargs:=[Vptr bp(Ptrofs.repr 80);Vptr bp(Ptrofs.repr 80)])(v:=Vundef).
 - unfold secp_pure;repeat(first[left;reflexivity|right]).
 - reflexivity.
 - eapply eval_Econs.
   + apply eval_affine_point_address;[cbn;tauto|exact Point].
   + reflexivity.
   + eapply eval_Econs;[apply eval_affine_point_address;[cbn;tauto|exact Point]|reflexivity|constructor].
 - exact Call.
Qed.

Lemma affine_after_inverse_closed :
 closed_stmtb field_io_helpers(affine_arithmetic_context affine_finish_statement)=true.
Proof. vm_compute;reflexivity. Qed.

Theorem eval_affine_finite_initialized x y z m bp br :
 (forall mc w,Int64.unsigned w<>0 ->
   Clight2.eval_funcall secp_ge mc(Internal f_secp256k1_ctz64_var)[Vlong w]
    E0 mc(Vint(Int.repr(Z_ctz(Int64.unsigned w))))) ->
 bp<>br -> square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m bp 0(words5 x) -> fe_at m bp 40(words5 y) -> fe_at m bp 80(words5 z) ->
 Mem.load Mint32 m bp 120=Some(Vint Int.zero) -> modinfo_fe_state m ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable ->
 exists zi mf,
 Clight2.eval_funcall secp_ge m(Internal f_secp256k1_ge_set_gej_var)
  [Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0(words5(point_mul_words x(square_words zi))) /\
 fe_at mf br 40(words5(point_mul_words y(point_mul_words zi(square_words zi)))) /\
 Mem.load Mint32 mf br 80=Some(Vint Int.zero) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 square_input_bounds(point_mul_words x(square_words zi)) /\
 square_input_bounds(point_mul_words y(point_mul_words zi(square_words zi))) /\
 radix_value zi=literal_invert_numeric(fe_inv_value z) /\
 radix_value(point_mul_words x(square_words zi)) mod field_prime=
  (radix_value x*(radix_value zi*radix_value zi)) mod field_prime /\
 radix_value(point_mul_words y(point_mul_words zi(square_words zi))) mod field_prime=
  (radix_value y*(radix_value zi*(radix_value zi*radix_value zi))) mod field_prime /\
 modinfo_fe_state mf /\ lframe(fun b _=>b<>bp /\ b<>br)m mf /\ readonly_preserved m mf.
Proof.
 intros CountCall Separate BX BY BZ X Y Z Flag Ready FP FR.
 destruct(Mem.alloc m 0 40) as(m1,b2) eqn:A1.
 destruct(Mem.alloc m1 0 40) as(ma,b3) eqn:A2.
 pose proof(affine_helper_entry m m1 ma b2 b3 br bp A1 A2) as Entry.
 pose proof(Mem.fresh_block_alloc _ _ _ _ _ A1) as Fresh2.
 assert(Fresh3:~Mem.valid_block m b3).
 { intro Valid;apply(Mem.fresh_block_alloc _ _ _ _ _ A2);eapply Mem.valid_block_alloc;eassumption. }
 assert(N23:b2<>b3).
 { intro Same;apply(Mem.fresh_block_alloc _ _ _ _ _ A2);rewrite <-Same;eapply Mem.valid_new_block;exact A1. }
 assert(ValidP:Mem.valid_block m bp) by(eapply Mem.perm_valid_block;apply(FP 0);lia).
 assert(ValidR:Mem.valid_block m br) by(eapply Mem.perm_valid_block;apply(FR 0);lia).
 assert(P2:bp<>b2) by(congruence).
 assert(P3:bp<>b3) by(congruence).
 assert(R2:br<>b2) by(congruence).
 assert(R3:br<>b3) by(congruence).
 assert(AllocFrame:lframe(fun _ _=>True)m ma).
 { eapply lframe_trans;apply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption. }
 assert(EntryReadonly:readonly_preserved m ma) by(eapply entry_preserved;exact Entry).
 assert(ReadyA:modinfo_fe_state ma) by(exact(proj1(modinfo_fe_state_preserved m ma Ready EntryReadonly))).
 assert(XA:fe_at ma bp 0(words5 x)) by(eapply curve_keep_field_range;[reflexivity|exact X|exact AllocFrame|intros;exact I]).
 assert(YA:fe_at ma bp 40(words5 y)) by(eapply curve_keep_field_range;[reflexivity|exact Y|exact AllocFrame|intros;exact I]).
 assert(ZA:fe_at ma bp 80(words5 z)) by(eapply curve_keep_field_range;[reflexivity|exact Z|exact AllocFrame|intros;exact I]).
 assert(FlagA:Mem.load Mint32 ma bp 120=Some(Vint Int.zero)).
 { rewrite(proj1 AllocFrame);[exact Flag|exact ValidP|intros;exact I]. }
 assert(FPA:Mem.range_perm ma bp 0 128 Cur Freeable) by(eapply curve_keep_free;[lia|exact FP|exact AllocFrame|intros;exact I]).
 assert(FRA:Mem.range_perm ma br 0 88 Cur Freeable) by(eapply curve_keep_free;[lia|exact FR|exact AllocFrame|intros;exact I]).
 assert(F2A:Mem.range_perm ma b2 0 40 Cur Freeable).
 { intros pos Range;eapply Mem.perm_alloc_1;[exact A2|];eapply Mem.perm_alloc_2;eassumption. }
 assert(F3A:Mem.range_perm ma b3 0 40 Cur Freeable).
 { intros pos Range;eapply Mem.perm_alloc_2;eassumption. }
 destruct(eval_fe_inverse_var_point z x y ma bp CountCall BZ ZA XA YA ReadyA FPA)
  as(zi & mn & Inverse & XN & YN & ZN & BZI & Numeric & Literal & FPN & ReadyN & InverseFrame & InverseReadonly).
 assert(FRN:Mem.range_perm mn br 0 88 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FRA|exact InverseFrame|];intros;left;congruence. }
 assert(F2N:Mem.range_perm mn b2 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F2A|exact InverseFrame|];intros;left;congruence. }
 assert(F3N:Mem.range_perm mn b3 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F3A|exact InverseFrame|];intros;left;congruence. }
 destruct(exec_affine_after_inverse_and_free(affine_finite_temps br bp)mn bp br b2 b3 x y zi
  eq_refl eq_refl P2 P3 N23 ltac:(congruence) R2 R3 BX BY BZI XN YN ZN FPN FRN F2N F3N)
  as(mw & mf & Arithmetic & Free & XO & YO & FlagF & FPF & FRF & BXO & BYO & VX & VY & PostFrame).
 assert(PostReadonly:readonly_preserved mn mf).
 { eapply preserved_trans;[|eapply freelist_preserved;exact Free].
   exact(proj1(internal_exec_preserved _ _ field_io_helpers_ok)
    _ _ _ _ _ _ _ _ Arithmetic (entry_plain _ _ _ _ _ _ _ Entry eq_refl) affine_after_inverse_closed). }
 assert(Frame:lframe(fun b _=>b<>bp /\ b<>br)m mf).
 { eapply lframe_implies with(P:=fun b _=>Mem.valid_block m b /\ b<>bp /\ b<>br).
   - eapply lframe_trans.
     + eapply lframe_implies;[exact AllocFrame|];intros;exact I.
     + eapply lframe_trans.
       * eapply lframe_implies;[exact InverseFrame|];intros b pos(V & NP & NR) _;left;exact NP.
       * eapply lframe_implies;[exact PostFrame|];intros b pos(V & NP & NR) _.
         split;[split;[unfold affine_arithmetic_frame;intuition congruence|exact NR]|].
         split;congruence.
   - intros b pos Outside Valid;split;assumption. }
 exists zi,mf;split.
 - eapply eval_funcall_internal with(e:=affine_local_env b2 b3)(le1:=affine_entry_temps br bp)
   (le2:=affine_finite_temps br bp)(m1:=ma)(m2:=mw)(out:=Out_normal).
   + exact Entry.
   + rewrite affine_entry_source;eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=ma)(le1:=affine_finite_temps br bp).
     * apply(exec_affine_finite_flag(affine_entry_temps br bp)ma bp b2 b3);[reflexivity|exact FlagA].
     * eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mn)(le1:=affine_finite_temps br bp).
       -- apply(exec_affine_inverse_from_call(affine_finite_temps br bp)ma mn bp b2 b3);
          [reflexivity|exact Inverse].
       -- exact Arithmetic.
   + reflexivity.
   + exact Free.
 - split;[exact XO|];split;[exact YO|];split;[exact FlagF|];split;[exact FPF|];split;[exact FRF|];
   split;[exact BXO|];split;[exact BYO|];split;[exact Numeric|];split;[exact VX|];split;[exact VY|];split.
   + exact(proj1(modinfo_fe_state_preserved mn mf ReadyN PostReadonly)).
   + split;[exact Frame|];eapply preserved_trans;[exact EntryReadonly|].
     eapply preserved_trans;[exact InverseReadonly|exact PostReadonly].
Qed.
