(** Exact public contextual contract; no claim about arbitrary overlapping
    buffers or correspondence established by the real environment builder. *)
From Coq Require Import ZArith List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_prim.
Require Import C.jet_application_context_contract C.jet_elements_null_data_environment.
Require Import C.jet_elements_null_data_layout C.jet_elements_null_data_bitmachine.

Theorem elements_output_null_datum_bitmachine_spec :
  application_jet_bitmachine_spec f_simplicity_output_null_datum elements_ge Elements.env
    (Ty.Prod Word32 Word32)
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (Ty.Sum (Ty.Prod (Word 1) Word256) (Ty.Sum (Ty.Sum Ty.Unit Ty.Unit) (Word 2)))))
    elements_null_data_environment_rep
    (@elements_output_null_datum_spec (PrimitivePrimSem option_Monad_Zero)).
Proof.
  intros logical_env env m L s [iw jw] tail fp HRep HEnvSep HBM HSep HWrite HNext HSpace.
  exact (elements_output_null_datum_environment_bitmachine logical_env env fp iw jw m L s tail
    HRep HEnvSep HBM HSep HWrite HNext HSpace).
Qed.
