(** Connect real Strauss entry/preparation to its actual scalar-split call.
    This is a staged execution result, not the complete guarded wNAF branch. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Cop Clight Clightdefs ClightBigstep Integers Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv.
Require Import C.jet_secp_generator_entry C.jet_secp_generator_initialize C.jet_secp_generator_globalz_call.
Require Import C.jet_secp_generator_zero_global C.jet_secp_generator_split_call.
Require Import C.jet_secp_scalar_add_reader_support C.jet_secp_scalar_get_b32_storage.
Require Import C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_split128_literal C.jet_secp_canonical_scalar.
Require Import C.jet_secp_field_read_preservation C.jet_secp_point_set_bit C.jet_secp_multiply_normalize_bridge.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem generator_entry_and_scalar_split m bs bx ba r a bng base value :
 generator_zero_global_state m ->
 Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr ba Ptrofs.zero) ->
 scalar_at m bng base (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))) ->
 exists mi mp mf bt bz b0 b128 bw0 bw128 bj bn bl,
 let e:=generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl in
 let le:=generator_entry_temps bs r a (Vptr bng (Ptrofs.repr base)) in
 let lr:=generator_ready_temps le (Vptr ba Ptrofs.zero) (Vptr bx Ptrofs.zero) in
 function_entry2 secp_ge f_secp256k1_ecmult_strauss_wnaf
  [Vptr bs Ptrofs.zero;r;Vlong Int64.one;a;Vptr generator_zero_block Ptrofs.zero;
   Vptr bng (Ptrofs.repr base)] m e le mi /\
 Clight2.exec_stmt secp_ge e le mi generator_prepare_non_generator E0 lr mp Out_normal /\
 eval_expr secp_ge e lr mp (Etempvar _ng (tptr (Tstruct __5826 noattr)))
  (Vptr bng (Ptrofs.repr base)) /\
 Cop.bool_val (Vptr bng (Ptrofs.repr base)) (tptr (Tstruct __5826 noattr)) mp=Some true /\
 Clight2.exec_stmt secp_ge e lr mp generator_scalar_split_call E0 lr mf Out_normal /\
 scalar_at mf b0 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (literal_split128_low value)))) /\
 scalar_at mf b128 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (literal_split128_high value)))) /\
 fe_at mf bz 0 (words5 (point_set_bit_words true)) /\
 NoDup [bt;bz;b0;b128;bw0;bw128;bj;bn;bl] /\
 (forall b,Mem.valid_block m b -> ~ In b [bt;bz;b0;b128;bw0;bw128;bj;bn;bl]) /\
 (forall b hi,In (b,hi) (generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 (forall pos k p,Mem.perm m bng pos k p -> Mem.perm mf bng pos k p) /\
 lframe (fun b _=>b<>bng) m mf.
Proof.
 intros Zero X A Input.
 assert (InputValid:Mem.valid_block m bng).
 { destruct Input as (_ & _ & _ & _ & Readable & _).
   eapply Mem.perm_valid_block;apply (Readable base);lia. }
 destruct (generator_entry_and_prepare m bs bx ba r a (Vptr bng (Ptrofs.repr base)) Zero X A)
  as (mi & mp & bt & bz & b0 & b128 & bw0 & bw128 & bj & bn & bl &
   Entry & Prepare & Field & Separate & Old & Free & FrameP & PreservedP).
 set (e:=generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl).
 set (le:=generator_entry_temps bs r a (Vptr bng (Ptrofs.repr base))).
 set (lr:=generator_ready_temps le (Vptr ba Ptrofs.zero) (Vptr bx Ptrofs.zero)).
 assert (SourceOutside:forall b,In b [bt;bz;b0;b128;bw0;bw128;bj;bn;bl] -> b<>bng).
 { intros b InLocal Eq;subst b;exact (Old bng InputValid InLocal). }
 assert (ZSource:bz<>bng) by (apply SourceOutside;cbn [In];tauto).
 assert (LowSource:b0<>bng) by (apply SourceOutside;cbn [In];tauto).
 assert (HighSource:b128<>bng) by (apply SourceOutside;cbn [In];tauto).
 assert (LowHigh:b0<>b128 /\ bz<>b0 /\ bz<>b128).
 { pose proof Separate as S;repeat rewrite NoDup_cons_iff in S;cbn [In] in S;intuition congruence. }
 destruct LowHigh as (LowHigh & ZLow & ZHigh).
 assert (InputP:scalar_at mp bng base (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value))))).
 { eapply scalar_at_lframe;[exact Input|exact FrameP|intros;congruence]. }
 assert (NG:lr!_ng=Some (Vptr bng (Ptrofs.repr base))).
 { unfold lr,generator_ready_temps;rewrite generator_no_points_preserves by discriminate.
   rewrite generator_initial_preserves by discriminate;reflexivity. }
 assert (Present:Cop.bool_val (Vptr bng (Ptrofs.repr base))
  (tptr (Tstruct __5826 noattr)) mp=Some true).
 { destruct InputP as (_ & Base & Align & Hi & Readable & _).
   change ((if Mem.weak_valid_pointer mp bng (Ptrofs.unsigned (Ptrofs.repr base))
    then Some true else None)=Some true).
   rewrite Ptrofs.unsigned_repr by lia.
   assert (Valid:Mem.weak_valid_pointer mp bng base=true).
   { apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm.
     eapply Mem.perm_implies;[apply (Readable base);lia|apply perm_any_N]. }
   rewrite Valid;reflexivity. }
 destruct (exec_generator_scalar_split e lr mp value b0 b128 bng base
  eq_refl eq_refl eq_refl NG LowHigh LowSource HighSource
  (Free b0 32 ltac:(cbn [generator_local_storage In];tauto))
  (Free b128 32 ltac:(cbn [generator_local_storage In];tauto)) InputP)
  as (mf & Split & Low & High & LowFree & HighFree & Blocks & Perms & FrameS).
 assert (FieldF:fe_at mf bz 0 (words5 (point_set_bit_words true))).
 { eapply field_at_lframe;[exact Field|exact FrameS|];intros;repeat split;assumption. }
 assert (Frame:lframe (fun b _=>b<>bng) m mf).
 { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\ b<>bng).
   - eapply lframe_trans.
     + eapply lframe_implies;[exact FrameP|].
       intros b pos (Valid & Other) _ Eq;subst b;apply (Old bz Valid);cbn [In];tauto.
     + eapply lframe_implies;[exact FrameS|].
       intros b pos (Valid & Other) _;split;[|split;[|exact Other]].
       * intro Eq;subst b;apply (Old b0 Valid);cbn [In];tauto.
       * intro Eq;subst b;apply (Old b128 Valid);cbn [In];tauto.
   - intros b pos Other Valid;split;assumption. }
 exists mi,mp,mf,bt,bz,b0,b128,bw0,bw128,bj,bn,bl.
 split;[exact Entry|];split;[exact Prepare|];split.
 - apply eval_Etempvar;exact NG.
 - split;[exact Present|];split;[exact Split|];split;[exact Low|];split;[exact High|];
    split;[exact FieldF|];split;[exact Separate|];split;[exact Old|];split.
   + intros b hi Slot pos Range;apply (proj2 (Perms b pos Cur Freeable));apply (Free b hi Slot);exact Range.
   + split;[|exact Frame].
     intros pos k p Perm;apply (proj2 (Perms bng pos k p)).
     apply (proj1 (proj2 FrameP));[exact InputValid|congruence|exact Perm].
Qed.
