(** Complete original scalar_inverse_var: real packing, complete modular
    inverse call, unpacking and cleanup. This is internal conditional progress:
    CTZ remains a premise and whole-global byte framing is not claimed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.Word C.jet_toZ C.jet_predicate_spec.
Require Import C.extraMath C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_scalar_inverse_core C.jet_secp_scalar_inverse_caller C.jet_secp_modinfo_scalar_global
 C.jet_secp_scalar_signed62 C.jet_secp_scalar_add_initial C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_overflow_numeric C.jet_secp_scalar_invert_literal C.jet_secp_canonical_scalar
 C.jet_secp_signed62_numeric C.jet_secp_curve_frame.
Require Import C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge scalar_inv_modinfo_block.

Theorem eval_scalar_inverse_var w m bd bx :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 modinfo_scalar_state m -> scalar_at m bx 0 (scalar_add_values w 0) ->
 Mem.range_perm m bx 0 32 Cur Freeable -> Mem.range_perm m bd 0 32 Cur Freeable ->
 0<=scalar_limb_value w<canonical_group_order -> exists result mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_inverse_var)
  [Vptr bd Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf bd 0 (scalar_add_values result 0) /\
 scalar_limb_value result=literal_scalar_invert_numeric(scalar_limb_value w) /\
 (forall input:Ty.tySem(Word 8),scalar_limb_value w=@toZ (WordToZ 8) input mod canonical_group_order ->
  @fromZ (WordToZ 8) (scalar_limb_value result)=@literal_scalar_invert Alg.CoreFunSem input) /\
 Mem.range_perm mf bd 0 32 Cur Freeable /\ modinfo_scalar_global_rep mf /\
 lframe(fun b _=>b<>bd /\ b<>bx /\ b<>scalar_inv_modinfo_block) m mf /\ readonly_preserved m mf.
Proof.
 intros CountCall Global Input FX FD Range.
 destruct(scalar_inv_entry_with_modinfo w m bd bx Global Input FX FD)
  as(bs & mi & mp & Entry & Pack & Args & Metadata & Packed & Normal & Value & Source &
    FS & FXP & FDP & SX & DS & Fresh & PFrame).
 assert(SG:bs<>scalar_inv_modinfo_block).
 { intro Same;apply Fresh;rewrite Same;exact(proj1(proj1 Global)). }
 assert(DG:bd<>scalar_inv_modinfo_block).
 { intro Same;apply(proj2 Global 0);rewrite <-Same;apply Mem.perm_cur_max;
   eapply Mem.perm_implies;[apply(FD 0);lia|constructor]. }
 destruct(eval_scalar_inv_core (scalar62_words true w) mp bs CountCall Normal
  ltac:(rewrite Value;exact Range) SG Packed FS Metadata)
  as(words & mc & Core & Result & OutNormal & Numeric & Simplicity & Owned & CoreGlobal & CFrame & CoreReadonly).
 assert(FDC:Mem.range_perm mc bd 0 32 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FDP|exact CFrame|];intros;split;assumption. }
 destruct(scalar_inv_call_from_core words m mi mp mc bs bd bx Entry Pack Core DS OutNormal Result Owned FDC)
  as(mf & Call & Output & Converted & Free & UFrame & CallReadonly).
 assert(NumericOut:scalar_limb_value(scalar62_words false words)=literal_scalar_invert_numeric(scalar_limb_value w)).
 { rewrite Converted,Numeric,Value;reflexivity. }
 assert(Literal:forall input:Ty.tySem(Word 8),scalar_limb_value w=@toZ (WordToZ 8) input mod canonical_group_order ->
  @fromZ (WordToZ 8) (scalar_limb_value(scalar62_words false words))=@literal_scalar_invert Alg.CoreFunSem input).
 { intros input Eq;rewrite Converted;apply Simplicity;rewrite Value;exact Eq. }
 assert(OutGlobal:modinfo_scalar_global_rep mf).
 { eapply modinfo_scalar_global_lframe;[exact CoreGlobal|exact UFrame|];intros;split;congruence. }
 assert(Frame:lframe(fun b _=>b<>bd /\ b<>bx /\ b<>scalar_inv_modinfo_block) m mf).
 { eapply lframe_implies with(P:=fun b _=>Mem.valid_block m b /\ b<>bd /\ b<>bx /\ b<>scalar_inv_modinfo_block).
   - eapply lframe_trans.
     + eapply lframe_implies;[exact PFrame|];intros b ofs(Valid & D & X & G) _.
       split;[intro Same;apply Fresh;rewrite <-Same;exact Valid|exact X].
     + eapply lframe_trans.
       * eapply lframe_implies;[exact CFrame|];intros b ofs(Valid & D & X & G) _.
         split;[intro Same;apply Fresh;rewrite <-Same;exact Valid|exact G].
       * eapply lframe_implies;[exact UFrame|];intros b ofs(Valid & D & X & G) _.
         split;[exact D|intro Same;apply Fresh;rewrite <-Same;exact Valid].
   - intros b ofs(D & X & G) Valid;repeat split;assumption. }
 exists(scalar62_words false words),mf;split;[exact Call|];split;[exact Output|];split;[exact NumericOut|];
 split;[exact Literal|];split;[exact Free|];split;[exact OutGlobal|];split;[exact Frame|apply CallReadonly;exact CoreReadonly].
Qed.
