(** Isolated next-step support: predicates on an owned five-limb field. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_local_regions.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition field_odd_run : option res :=
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 40 f_secp256k1_fe_is_odd
    [XP 0 0] local_write_initial_regs [] 6.
Definition field_odd_tree := Eval vm_compute in field_odd_run.
Definition field_odd_state : sstate :=
  match field_odd_tree with Some (RDone state _) => state | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition field_odd_ret : sx := XL2I (XLb Band (XLv 1) (XI2L Signed (XIc Int.one))).
Lemma field_odd_run_eq : field_odd_run = Some (RDone field_odd_state ONormal).
Proof. reflexivity. Qed.
Lemma field_odd_return : (stemps field_odd_state)!1%positive = Some field_odd_ret.
Proof. reflexivity. Qed.
Lemma field_odd_regions : sregs field_odd_state = local_write_initial_regs.
Proof. reflexivity. Qed.
Lemma field_odd_value rho layout :
  den rho layout field_odd_ret = Vint (Int.repr (Int64.unsigned (Int64.and (rho 1%nat) Int64.one))).
Proof. reflexivity. Qed.

Theorem eval_field_odd_from_owned_region m layout rho :
  rep rho layout local_write_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_odd)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf
      (Vint (Int.repr (Int64.unsigned (Int64.and (rho 1%nat) Int64.one)))) /\
    rep rho layout local_write_initial_regs mf /\
    lframe (fun b pos => ~ foot layout (map rshape local_write_initial_regs) b pos) m mf.
Proof.
  intro HRep.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 40 f_secp256k1_fe_is_odd
    [XP 0 0] local_write_initial_regs 6 _ field_odd_run_eq eq_refl rho layout m HRep)
    as [mf [result [HCall [HFinal [HReturn [HShape HFrame]]]]]].
  cbn [rsel fst] in HFinal, HReturn.
  rewrite field_odd_regions in HFinal.
  rewrite field_odd_return in HReturn.
  change (result = den rho (lay layout) field_odd_ret) in HReturn.
  rewrite field_odd_value in HReturn; subst result.
  change (map (den rho (lay layout)) [XP 0 0]) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0))] in HCall.
  rewrite Z.add_0_r in HCall.
  exists mf; split; [exact HCall|]; split; assumption.
Qed.

Require Import C.jet_exec C.jet_readBit_layout C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_write_fe_numeric C.jet_secp_local_call C.jet_secp_canonical_odd C.jet_secp_canonical_normalize.
Local Opaque canonical_fe_normalize canonical_fe_is_odd.
Theorem eval_field_odd_canonical m ba (value : Ty.tySem (Word.Word 8)) :
  fe_at m ba 0 (map Int64.repr (fe_limbs_of
    (@Word.ToZ.Theory.toZ (Word.WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)))) ->
  Mem.range_perm m ba 0 40 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_odd)
      [Vptr ba Ptrofs.zero] E0 mf (Vint (bit_int (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem value)))) /\
    Mem.range_perm mf ba 0 40 Cur Freeable /\
    lframe (fun b _ => b <> ba) m mf.
Proof.
  intros HField HFree.
  set (v := @Word.ToZ.Theory.toZ (Word.WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)).
  pose proof (local_write_initial_rep_from_field v 0 m ba HField HFree) as HRep.
  destruct (eval_field_odd_from_owned_region m [(ba,0)] (write_fe_rho v 0) HRep)
    as [mf [HCall [HFinal HFrame]]].
  assert (HRet : Int64.unsigned (Int64.and (write_fe_rho v 0 1%nat) Int64.one) =
    Z.b2z (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem value))).
  { change (Int64.unsigned (Int64.and (Int64.repr (v mod 2 ^ 52)) Int64.one) =
      Z.b2z (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem value))).
    rewrite field_low_limb_odd_value, canonical_fe_is_odd_numeric; reflexivity. }
  rewrite HRet in HCall.
  assert (HBit : Int.repr (Z.b2z (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem value))) =
    bit_int (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem value))).
  { destruct (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem value)); reflexivity. }
  rewrite HBit in HCall.
  pose proof (rep_free_region _ _ _ _ 0 40 HFinal ltac:(cbn; lia) eq_refl) as [_ HFinalFree].
  exists mf; split; [exact HCall|]; split; [exact HFinalFree|].
  eapply lframe_implies; [exact HFrame|]; intros b pos HOther HValid.
  apply no_local_write_foot; exact HOther.
Qed.
