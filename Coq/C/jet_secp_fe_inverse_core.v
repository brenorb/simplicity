(** Complete original modinv64_var call at the original field modulus.
    Existing startup/copies, divsteps, field update invariant and literal
    finish are composed, with original CTZ calls still explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.Word C.jet_toZ C.jet_predicate_spec.
Require Import C.extraMath C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix C.jet_secp_modinfo_fe_global
 C.jet_secp_modinfo_fe_copy C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_copies
 C.jet_secp_modinv_var_seed C.jet_secp_modinv_var_de C.jet_secp_modinv_var_fg
 C.jet_secp_modinv_var_zero C.jet_secp_modinv_var_finish C.jet_secp_modinv_var_free
 C.jet_secp_fe_inverse_loop C.jet_secp_fe_inverse_loop_finish C.jet_secp_fe_inverse_batch
 C.jet_secp_modinv_de_exec C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_normalize62_exec
 C.jet_secp_invert_literal C.jet_secp_signed62_numeric C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_fe_math C.jet_secp_fe_inv_prefix
 C.jet_secp_closed_helpers C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge modinfo_fe_block.

Lemma field_inv_core_body_source : fn_body f_secp256k1_modinv64_var=
 statement_sequence(firstn 14(fst inv_start_parts))(Ssequence inv_caller_loop inv_finish).
Proof. reflexivity. Qed.
Lemma field_inv_core_private_outside m bs betaN b : length betaN=5%nat ->
 Forall(fun p=>~Mem.valid_block m(fst p)) betaN -> Mem.valid_block m b ->
 inv_free_outside ([(bs,0);(modinfo_fe_block,0)]++betaN)b.
Proof.
 intros Len Fresh Valid r R Same;apply(inv_copy_fresh [(bs,0);(modinfo_fe_block,0)] betaN m
  eq_refl Len Fresh r R);rewrite <-Same;exact Valid.
Qed.
Lemma field_inv_core_prefix_outside m bs betaN b ofs : length betaN=5%nat ->
 Forall(fun p=>~Mem.valid_block m(fst p)) betaN -> Mem.valid_block m b ->
 b<>bs -> b<>modinfo_fe_block ->
 ~foot ([(bs,0);(modinfo_fe_block,0)]++betaN)(map rshape(sregs inv_start_state)) b ofs.
Proof.
 intros Len Fresh Valid X Mod(r & shape & d & chunk & At & Cell & Block & Range).
 assert(R:(r<7)%nat).
 { change(r<length(map rshape(sregs inv_start_state)))%nat;apply nth_error_Some;rewrite At;discriminate. }
 destruct r as[|[|r]];[apply X;exact Block|apply Mod;exact Block|].
 exact(field_inv_core_private_outside m bs betaN b Len Fresh Valid (S(S r)) ltac:(lia) Block).
Qed.
Lemma field_inv_core_finish_outside beta b ofs : b<>blk beta 0 -> b<>modinfo_fe_block ->
 blk beta 1=modinfo_fe_block -> inv_free_outside beta b -> field_inv_loop_finish_frame beta b ofs.
Proof.
 intros X Mod Block Private.
 assert(DE:~foot(inv_de_layout beta)(map rshape de62_regs)b ofs).
 { intros(r & shape & d & chunk & At & Cell & Equal & Range).
   assert(R:(r<4)%nat) by(change(r<length(map rshape de62_regs))%nat;apply nth_error_Some;rewrite At;discriminate).
   rewrite inv_de_block in Equal by exact R.
   destruct r as[|[|[|[|r]]]];try lia;cbn [inv_de_select nth] in Equal;
    [exact(Private 2%nat ltac:(lia) Equal)|exact(Private 3%nat ltac:(lia) Equal)|
     exact(Private 6%nat ltac:(lia) Equal)|rewrite Block in Equal;exact(Mod Equal)]. }
 assert(FG:~foot(inv_fg_layout beta)(map rshape fg_regs)b ofs).
 { intros(r & shape & d & chunk & At & Cell & Equal & Range).
   assert(R:(r<3)%nat) by(change(r<length(map rshape fg_regs))%nat;apply nth_error_Some;rewrite At;discriminate).
   rewrite inv_fg_block in Equal by exact R.
   destruct r as[|[|[|r]]];try lia;cbn [inv_fg_select nth] in Equal;
    [exact(Private 4%nat ltac:(lia) Equal)|exact(Private 5%nat ltac:(lia) Equal)|exact(Private 6%nat ltac:(lia) Equal)]. }
 split.
 - split;[apply Private;lia|];split;[exact DE|];split;[exact FG|];split;apply Private;lia.
 - split;[split;left;[apply Private;lia|exact Mod]|];split;assumption.
Qed.

Theorem eval_field_inv_core w m bs :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 signed62_normalized w -> 0<=signed62_unsigned_value w<feP ->
 bs<>modinfo_fe_block -> fe_at m bs 0(words5 w) -> Mem.range_perm m bs 0 40 Cur Freeable ->
 modinfo_fe_global_rep m -> exists words mr,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_var)
  [Vptr bs Ptrofs.zero;Vptr modinfo_fe_block Ptrofs.zero] E0 mr Vundef /\
 fe_at mr bs 0(words5 words) /\ signed62_normalized words /\
 signed62_unsigned_value words=literal_invert_numeric(signed62_unsigned_value w) /\
 (forall input:Ty.tySem(Word 8),signed62_unsigned_value w=@toZ (WordToZ 8) input mod feP ->
  @fromZ (WordToZ 8)(signed62_unsigned_value words)=@literal_fe_invert Alg.CoreFunSem input) /\
 Mem.range_perm mr bs 0 40 Cur Freeable /\ modinfo_fe_global_rep mr /\
 lframe(fun b _=>b<>bs /\ b<>modinfo_fe_block) m mr /\ readonly_preserved m mr.
Proof.
 intros CountCall Normal Range Sep Input Free Global.
 pose proof(inv_start_rep_from_storage w m bs Sep Input Free Global) as Start.
 destruct(inv_entry_to_loop w [(bs,0);(modinfo_fe_block,0)] m Start eq_refl)
  as(betaN & e & le & mi & lc & mc & Entry & Prefix & Objects & Temps & Env & Len & Eta & Fresh & PFrame).
 set(beta:=[(bs,0);(modinfo_fe_block,0)]++betaN) in *.
 assert(NewLen:length betaN=5%nat).
 { pose proof(proj1 Objects) as Size;change(length beta=7%nat) in Size;unfold beta in Size;rewrite app_length in Size;cbn in Size;lia. }
 assert(Block:blk beta 1=modinfo_fe_block) by reflexivity.
 assert(Base:bas beta 1=0) by reflexivity.
 assert(X:lc!_x=Some(Vptr(blk beta 0)Ptrofs.zero)).
 { pose proof(Temps _x (XP 0 0) eq_refl) as T;exact T. }
 assert(Modinfo:lc!_modinfo=Some(Vptr(blk beta 1)(Ptrofs.repr(bas beta 1)))).
 { pose proof(Temps _modinfo (XP 1 0) eq_refl) as T;exact T. }
 pose proof(inv_seed_rep w beta mc Objects) as Seed.
 pose proof(field_inv_seed_ready w beta e lc mc Normal Seed Env Eta Modinfo Len) as Ready.
 destruct(exec_field_inv_loop_finish(signed62_unsigned_value w)0 beta e lc mc 5(inv_seed_rho w)
  CountCall Range Ready Block Base X)
  as(words & lf & mf & mr & LoopFinish & Freed & Output & OutNormal & Numeric & Literal & Owned & OutGlobal & FFrame & FinishReadonly).
 assert(Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_var)
  [Vptr bs Ptrofs.zero;Vptr modinfo_fe_block Ptrofs.zero] E0 mr Vundef).
 { eapply eval_funcall_internal with(e:=e)(le1:=le)(le2:=lf)(m1:=mi)(m2:=mf)(out:=Out_normal).
   - exact Entry.
   - rewrite field_inv_core_body_source;eapply exec_statement_prefix_then_last;[exact Prefix|exact LoopFinish].
   - reflexivity.
   - exact Freed. }
 assert(Frame:lframe(fun b _=>b<>bs /\ b<>modinfo_fe_block)m mr).
 { eapply lframe_implies with(P:=fun b _=>Mem.valid_block m b /\ b<>bs /\ b<>modinfo_fe_block).
   - eapply lframe_trans.
     + eapply lframe_implies;[exact PFrame|];intros b ofs(Valid & Xb & Mb) _.
       exact(field_inv_core_prefix_outside m bs betaN b ofs NewLen Fresh Valid Xb Mb).
     + eapply lframe_implies;[exact FFrame|];intros b ofs(Valid & Xb & Mb) _.
       apply field_inv_core_finish_outside;[exact Xb|exact Mb|exact Block|].
       exact(field_inv_core_private_outside m bs betaN b NewLen Fresh Valid).
   - intros b ofs(Xb & Mb) Valid;repeat split;assumption. }
 exists words,mr;split;[exact Call|];split;[exact Output|];split;[exact OutNormal|];split;[exact Numeric|];
 split;[exact Literal|];split;[exact Owned|];split;[exact OutGlobal|];split;[exact Frame|].
 eapply preserved_trans;[eapply entry_preserved;exact Entry|].
 eapply preserved_trans;[|exact FinishReadonly].
 eapply secp_closed_stmt_preserved;[exact Prefix|apply(inv_env_plain beta e Env)|exact secp_closed_ready_prefix].
Qed.
