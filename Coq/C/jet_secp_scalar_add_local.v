(** Full original-C public contract against the literal canonical scalar-add port. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_frame_inv C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_normalize_local C.jet_secp_canonical_scalar_add C.jet_secp_scalar_add_lifecycle.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_scalar_add encode.

Theorem scalar_add_literal_local_spec :
  secp_jet_local_spec f_simplicity_scalar_add (Ty.Prod (Word 8) (Word 8)) (Word 8)
    (@canonical_scalar_add Alg.CoreFunSem).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [a b]
    HBase HAlign HSource HCursor HMax HInput HOutput.
  change (rc+512 <= Int64.max_unsigned) in HMax.
  change (write_frame_at m bd dbase bw outedge cursor 256) in HOutput.
  destruct (eval_secp_scalar_add_literal env m bd dbase bs sbase bw outedge cursor 256 bi edge rc a b
    HOutput ltac:(lia) HBase HAlign HSource HInput HCursor HMax)
    as (mf & HCall & HFinal & HFrame).
  destruct HFinal as (HV & HF & HN & (HCells & HPrefix & HFields & HLoads & HPerms) & Hw).
  rewrite encode_length in HFields, HLoads.
  exists mf. split; [exact HCall|]. split; [exact HCells|]. split; [exact HPrefix|].
  split; [exact HFields|].
  intros chunk bx ofs HValid HFrameOther HOutputOther.
  destruct (Pos.eq_dec bx bd) as [HD|HD];
    [apply HLoads; [split; [left; exact HD|exact HValid]|assumption|assumption]|].
  destruct (Pos.eq_dec bx bw) as [HW|HW];
    [apply HLoads; [split; [right; left; exact HW|exact HValid]|assumption|assumption]|].
  destruct (Pos.eq_dec bx bi) as [HI|HI];
    [apply HLoads; [split; [right; right; exact HI|exact HValid]|assumption|assumption]|].
  apply (proj1 HFrame); [exact HValid|]. intros pos HPos.
  unfold extA, fext; intros [[H|[H|H]] _]; contradiction.
Qed.
Print Assumptions scalar_add_literal_local_spec.

