(** Original C affine jet against literal canonical Simplicity, full input pair. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_word_repr C.jet_frame_layout C.jet_input_layout C.jet_write_layout.
Require Import C.jet_output_layout C.jet_encoding C.jet_frame_inv C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_normalize_local.
Require Import C.jet_secp_gej_negate_literal C.jet_secp_ge_negate_call.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_ge_negate.

Theorem ge_negate_literal_local_spec :
  secp_jet_local_spec f_simplicity_ge_negate
    (Ty.Prod (Word 8) (Word 8)) (Ty.Prod (Word 8) (Word 8))
    (@literal_ge_negate Alg.CoreFunSem).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HBase HAlign HSource HCursor HMax HInput HOutput.
  destruct a as [x y].
  change (rc+512 <= Int64.max_unsigned) in HMax.
  change (write_frame_at m bd dbase bw outedge cursor 512) in HOutput.
  change (frame_input_cells_at m bi edge rc (encode x ++ encode y)) in HInput.
  rewrite frame_input_cells_at_app, encode_word_length in HInput.
  destruct HInput as [HX HY].
  change (frame_input_cells_at m bi edge (rc+256) (encode y)) in HY.
  rewrite encode_word in HX,HY.
  destruct (eval_ge_negate_literal_public env m bd dbase bs sbase bw outedge cursor 512 bi edge rc
    x y HOutput ltac:(lia) HBase HAlign HSource HX HY HCursor HMax)
    as (mf & HCall & HFinal & HFrame).
  destruct HFinal as (HV & HF & HN & (HCells & HPrefix & HFields & HLoads & HPerms) & Hw).
  rewrite encode_length in HFields,HLoads.
  exists mf;split;[exact HCall|];split;[exact HCells|].
  split;[exact HPrefix|];split;[exact HFields|].
  intros chunk b ofs HValid HFrameOther HOutputOther.
  destruct (Pos.eq_dec b bd) as [HD|HD];
    [apply HLoads;[split;[left;exact HD|exact HValid]|assumption|assumption]|].
  destruct (Pos.eq_dec b bw) as [HW|HW];
    [apply HLoads;[split;[right;left;exact HW|exact HValid]|assumption|assumption]|].
  destruct (Pos.eq_dec b bi) as [HI|HI];
    [apply HLoads;[split;[right;right;exact HI|exact HValid]|assumption|assumption]|].
  apply (proj1 HFrame);[exact HValid|];intros pos HPos.
  unfold extA,fext;intros [[H|[H|H]] _];contradiction.
Qed.
Timeout 60 Print Assumptions ge_negate_literal_local_spec.
