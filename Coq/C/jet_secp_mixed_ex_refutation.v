(** The fixed public literal local-spec contract is false.  Reuse the actual
    public counterexample and the existing Clight determinism theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_normalize_local
  C.jet_secp_add_literal C.jet_secp_mixed_ex_counterexample C.jet_clight_determinism.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Simplicity.Translate.encode literal_gej_ge_add_ex.

Theorem gej_ge_add_ex_not_literal_local_spec :
  ~secp_jet_local_spec f_simplicity_gej_ge_add_ex
    (Ty.Prod (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (Ty.Prod (Word 8) (Word 8)))
    (Ty.Prod (Word 8) (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)))
    (@literal_gej_ge_add_ex Simplicity.Alg.CoreFunSem).
Proof.
  intro Correct.
  destruct (gej_ge_add_ex_public_counterexample (Vlong Int64.zero))
    as (minit & m & bd & bs & bi & bw & edge & mf & Init & Base & Align & Source & Input &
      Output & Sep & Old & Call & Fields & Cells & Wrong).
  destruct (Correct (Vlong Int64.zero) m bd 0 bs 0 bi bw edge 0 1024 0 extended_ratio_input
    Base Align Source ltac:(lia) ltac:(change (1280<=18446744073709551615);lia) Input Output)
    as (mg & OtherCall & OtherOutput & Rest).
  destruct (eval_funcall_unique jets_secp.prog m (Internal f_simplicity_gej_ge_add_ex)
    [Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero;Vlong Int64.zero] mf (Vint Int.one)
    E0 mg (Vint Int.one) Call OtherCall) as (_ & EqualMemory & _).
  subst mg;apply Wrong;exact OtherOutput.
Qed.
