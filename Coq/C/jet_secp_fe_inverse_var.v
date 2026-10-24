(** Actual original fe_inv_var caller, for whole fields and embedded slices.
    Copy/normalize/pack/core/unpack/free are derived. CTZ is explicit; no
    implementation, modulus or literal specification is substituted. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.Word C.jet_toZ C.jet_predicate_spec.
Require Import C.extraMath C.jet_sx_mem C.jet_sx_state C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_fe_inv_statements C.jet_secp_fe_inv_prefix C.jet_secp_fe_inv_finish
 C.jet_secp_fe_inverse_state C.jet_secp_modinfo_fe_global C.jet_secp_modinfo_fe_caller
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_signed62_numeric C.jet_secp_signed62_repack C.jet_secp_invert_literal
 C.jet_secp_statement_prefix C.jet_secp_closed_helpers C.jet_clight_internal_frame
 C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge modinfo_fe_block.

Lemma exec_fe_inv_inverse le mp mc bt bs :
 Clight2.eval_funcall secp_ge mp (Internal f_secp256k1_modinv64_var)
  [Vptr bs Ptrofs.zero;Vptr modinfo_fe_block Ptrofs.zero] E0 mc Vundef ->
 Clight2.exec_stmt secp_ge (fe_inv_env bt bs) le mp fe_inv_inverse E0 le mc Out_normal.
Proof.
 intro Core;unfold fe_inv_inverse;eapply exec_curve_call with
  (vargs:=[Vptr bs Ptrofs.zero;Vptr modinfo_fe_block Ptrofs.zero])(v:=Vundef).
 - unfold secp_pure;repeat(first[left;reflexivity|right]).
 - reflexivity.
 - eapply eval_Econs.
   + unfold fe_inv_s_address;apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
   + reflexivity.
   + eapply eval_Econs.
     * apply eval_Eaddrof;apply eval_Evar_global;[reflexivity|exact modinfo_fe_global_symbol].
     * reflexivity.
     * constructor.
 - exact Core.
Qed.

Theorem eval_fe_inverse_var_slice w m bx sbase bd dbase size :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 square_input_bounds w -> fe_at m bx sbase(words5 w) -> modinfo_fe_state m ->
 0<=dbase -> (8|dbase) -> dbase+40<=Ptrofs.max_unsigned -> dbase+40<=size ->
 Mem.range_perm m bd 0 size Cur Freeable -> exists result mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_inv_var)
  [Vptr bd(Ptrofs.repr dbase);Vptr bx(Ptrofs.repr sbase)] E0 mf Vundef /\
 fe_at mf bd dbase(words5 result) /\ square_input_bounds result /\
 radix_value result=literal_invert_numeric(fe_inv_value w) /\
 (forall input:Ty.tySem(Word 8),radix_value w=@toZ (WordToZ 8) input ->
  @fromZ (WordToZ 8)(radix_value result)=@literal_fe_invert Alg.CoreFunSem input) /\
 Mem.range_perm mf bd 0 size Cur Freeable /\ modinfo_fe_state mf /\
 lframe(fun b pos=>b<>bd \/ pos<dbase \/ dbase+40<=pos)m mf /\ readonly_preserved m mf.
Proof.
 intros CountCall Bounds Input Ready Base Align Max Fit FD.
 destruct(fe_inv_entry_to_core w m bx sbase bd dbase Bounds Input(proj1 Ready))
  as(bt & bs & mi & mp & Entry & Prefix & Start & Packed & Canonical & Source & FTP & FSP &
   PackedNormal & PackedValue & GlobalP & TS & FreshT & FreshS & PFrame).
 assert(Plain:plain_env(fe_inv_env bt bs)) by(eapply entry_plain;[exact Entry|reflexivity]).
 assert(EntryReadonly:readonly_preserved m mi) by(eapply entry_preserved;exact Entry).
 assert(PrefixReadonly:readonly_preserved mi mp).
 { eapply secp_closed_stmt_preserved;[exact Prefix|exact Plain|vm_compute;reflexivity]. }
 assert(ReadyP:modinfo_fe_state mp).
 { apply(proj1(modinfo_fe_state_preserved m mp Ready
    (preserved_trans m mi mp EntryReadonly PrefixReadonly))). }
 assert(SG:bs<>modinfo_fe_block) by(intro Same;apply FreshS;rewrite Same;exact(proj1(proj1 Ready))).
 assert(DValid:Mem.valid_block m bd) by(eapply Mem.perm_valid_block;apply(FD 0);lia).
 assert(DT:bd<>bt) by(intro Same;apply FreshT;rewrite <-Same;exact DValid).
 assert(DS:bd<>bs) by(intro Same;apply FreshS;rewrite <-Same;exact DValid).
 assert(FDP:Mem.range_perm mp bd 0 size Cur Freeable).
 { eapply curve_keep_free;[lia|exact FD|exact PFrame|];intros;exact I. }
 destruct(eval_field_inv_core_initialized(fe_inv_packed_words w)mp bs CountCall PackedNormal
  ltac:(rewrite PackedValue;exact(proj1(fe_inv_value_range w))) SG Packed FSP ReadyP)
  as(words & mc & Core & Output & OutNormal & Numeric & Literal & FSC & ReadyC & CFrame & CoreReadonly).
 assert(FTC:Mem.range_perm mc bt 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FTP|exact CFrame|];intros;exact TS. }
 assert(FDC:Mem.range_perm mc bd 0 size Cur Freeable).
 { eapply curve_keep_free;[lia|exact FDP|exact CFrame|];intros;exact DS. }
 destruct(exec_fe_inv_unpack_slice_and_free (fe_inv_slice_temps bd dbase bx sbase) mc bt bs bd dbase size words
  eq_refl TS DT DS Base Align Max Fit OutNormal Output FSC FTC FDC)
  as(mu & mf & Unpack & Free & Stored & Owned & Positioned & Value & UFrame).
 assert(Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_inv_var)
  [Vptr bd(Ptrofs.repr dbase);Vptr bx(Ptrofs.repr sbase)] E0 mf Vundef).
 { eapply eval_funcall_internal with(e:=fe_inv_env bt bs)
   (le1:=fe_inv_slice_temps bd dbase bx sbase)(le2:=fe_inv_slice_temps bd dbase bx sbase)
   (m1:=mi)(m2:=mu)(out:=Out_normal).
   - exact Entry.
   - rewrite fe_inv_prefix_source;eapply exec_statement_prefix_then_last;[exact Prefix|].
     eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mc)(le1:=fe_inv_slice_temps bd dbase bx sbase).
     + apply exec_fe_inv_inverse;exact Core.
     + exact Unpack.
   - reflexivity.
   - exact Free. }
 assert(Preserved:readonly_preserved m mf).
 { eapply preserved_trans;[exact EntryReadonly|].
   eapply preserved_trans;[exact PrefixReadonly|].
   eapply preserved_trans;[exact CoreReadonly|].
   eapply preserved_trans;[|eapply freelist_preserved;exact Free].
   eapply secp_closed_stmt_preserved;[exact Unpack|exact Plain|vm_compute;reflexivity]. }
 assert(Frame:lframe(fun b pos=>b<>bd \/ pos<dbase \/ dbase+40<=pos)m mf).
 { eapply lframe_implies with(P:=fun b pos=>Mem.valid_block m b /\ (b<>bd \/ pos<dbase \/ dbase+40<=pos)).
   - eapply lframe_trans.
     + eapply lframe_implies;[exact PFrame|];intros;exact I.
     + eapply lframe_trans.
       * eapply lframe_implies;[exact CFrame|];intros b pos[Valid Outside] _ Same.
         apply FreshS;rewrite <-Same;exact Valid.
       * eapply lframe_implies;[exact UFrame|];intros b pos[Valid Outside] _.
         split;[exact Outside|];split;intro Same;
          [apply FreshT|apply FreshS];rewrite <-Same;exact Valid.
   - intros b pos Outside Valid;split;assumption. }
 exists(fe_repack_words false words),mf;split;[exact Call|];split;[exact Stored|];split.
 - apply fe_inv_unpacked_bounds;exact OutNormal.
 - split.
   + rewrite Value,Numeric,PackedValue;reflexivity.
   + split.
     * intros input InputValue;rewrite Value;apply Literal.
       rewrite PackedValue;unfold fe_inv_value;rewrite InputValue;reflexivity.
     * split;[exact Owned|];split;[exact(proj1(modinfo_fe_state_preserved m mf Ready Preserved))|];
       split;assumption.
Qed.

Corollary eval_fe_inverse_var w m bx bd :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 square_input_bounds w -> fe_at m bx 0(words5 w) -> modinfo_fe_state m ->
 Mem.range_perm m bd 0 40 Cur Freeable -> exists result mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_inv_var)
  [Vptr bd Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf Vundef /\
 fe_at mf bd 0(words5 result) /\ square_input_bounds result /\
 radix_value result=literal_invert_numeric(fe_inv_value w) /\
 (forall input:Ty.tySem(Word 8),radix_value w=@toZ (WordToZ 8) input ->
  @fromZ (WordToZ 8)(radix_value result)=@literal_fe_invert Alg.CoreFunSem input) /\
 Mem.range_perm mf bd 0 40 Cur Freeable /\ modinfo_fe_state mf /\
 lframe(fun b _=>b<>bd)m mf /\ readonly_preserved m mf.
Proof.
 intros CountCall Bounds Input Ready Free.
 destruct(eval_fe_inverse_var_slice w m bx 0 bd 0 40 CountCall Bounds Input Ready
  ltac:(lia) ltac:(exists 0;reflexivity) ltac:(change(40<=18446744073709551615);lia) ltac:(lia) Free)
  as(result & mf & Call & Output & ResultBounds & Numeric & Literal & Owned & ReadyF & Frame & Preserved).
 exists result,mf;split;[exact Call|];split;[exact Output|];split;[exact ResultBounds|];split;[exact Numeric|];
 split;[exact Literal|];split;[exact Owned|];split;[exact ReadyF|];split;[|exact Preserved].
 eapply lframe_implies;[exact Frame|];intros b pos Different Valid;left;exact Different.
Qed.

(** The real point-normalization caller inverts Z in place at offset 80.
    X, Y and the complete 128-byte point ownership survive. *)
Corollary eval_fe_inverse_var_point w x y m bp :
 (forall mc z,Int64.unsigned z<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong z]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned z))))) ->
 square_input_bounds w -> fe_at m bp 80(words5 w) ->
 fe_at m bp 0(words5 x) -> fe_at m bp 40(words5 y) -> modinfo_fe_state m ->
 Mem.range_perm m bp 0 128 Cur Freeable -> exists result mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_inv_var)
  [Vptr bp(Ptrofs.repr 80);Vptr bp(Ptrofs.repr 80)] E0 mf Vundef /\
 fe_at mf bp 0(words5 x) /\ fe_at mf bp 40(words5 y) /\ fe_at mf bp 80(words5 result) /\
 square_input_bounds result /\ radix_value result=literal_invert_numeric(fe_inv_value w) /\
 (forall input:Ty.tySem(Word 8),radix_value w=@toZ (WordToZ 8) input ->
  @fromZ (WordToZ 8)(radix_value result)=@literal_fe_invert Alg.CoreFunSem input) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ modinfo_fe_state mf /\
 lframe(fun b pos=>b<>bp \/ pos<80 \/ 120<=pos)m mf /\ readonly_preserved m mf.
Proof.
 intros CountCall Bounds Z X Y Ready Owned.
 destruct(eval_fe_inverse_var_slice w m bp 80 bp 80 128 CountCall Bounds Z Ready
  ltac:(lia) ltac:(exists 10;reflexivity) ltac:(change(120<=18446744073709551615);lia) ltac:(lia) Owned)
  as(result & mf & Call & Output & ResultBounds & Numeric & Literal & Free & ReadyF & Frame & Preserved).
 assert(XF:fe_at mf bp 0(words5 x)).
 { eapply curve_keep_field_range;[reflexivity|exact X|exact Frame|];intros pos Range;right;left;lia. }
 assert(YF:fe_at mf bp 40(words5 y)).
 { eapply curve_keep_field_range;[reflexivity|exact Y|exact Frame|];intros pos Range;right;left;lia. }
 exists result,mf;split;[exact Call|];split;[exact XF|];split;[exact YF|];split;[exact Output|];
 split;[exact ResultBounds|];split;[exact Numeric|];split;[exact Literal|];split;[exact Free|];
 split;[exact ReadyF|];split;assumption.
Qed.
