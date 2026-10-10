(** Full original-C jet contract against the literal canonical point program. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_word_repr C.jet_frame_layout C.jet_input_layout C.jet_write_layout.
Require Import C.jet_output_layout C.jet_encoding C.jet_frame_inv C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_normalize_local.
Require Import C.jet_secp_literal_gej_predicate C.jet_secp_gej_predicate_call.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_gej_is_infinity.

Theorem gej_is_infinity_literal_local_spec :
  secp_jet_local_spec f_simplicity_gej_is_infinity
    (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (Ty.Sum Ty.Unit Ty.Unit)
    (@literal_gej_is_infinity Alg.CoreFunSem).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HBase HAlign HSource HCursor HMax HInput HOutput.
  destruct a as [[x y] z].
  change (rc+768 <= Int64.max_unsigned) in HMax.
  change (write_frame_at m bd dbase bw outedge cursor 1) in HOutput.
  change (frame_input_cells_at m bi edge rc ((encode x ++ encode y) ++ encode z)) in HInput.
  rewrite !frame_input_cells_at_app, !app_length, !encode_word_length in HInput.
  destruct HInput as [[HX HY] HZ].
  change (frame_input_cells_at m bi edge (rc+256) (encode y)) in HY.
  change (frame_input_cells_at m bi edge (rc+512) (encode z)) in HZ.
  rewrite encode_word in HX, HY, HZ.
  destruct (eval_gej_predicate_canonical_public env m bd dbase bs sbase bw outedge cursor 1 bi edge rc
    x y z HOutput ltac:(lia) HBase HAlign HSource HX HY HZ HCursor HMax)
    as (mf & HCall & HFinal & HFrame).
  destruct HFinal as (HV & HF & HN & (HCells & HPrefix & HFields & HLoads & HPerms) & Hw).
  rewrite encode_length in HFields, HLoads.
  rewrite literal_gej_is_infinity_value.
  exists mf; split; [exact HCall|]. split; [exact HCells|].
  split; [exact HPrefix|]. split; [exact HFields|].
  intros chunk b ofs HValid HFrameOther HOutputOther.
  destruct (Pos.eq_dec b bd) as [HD|HD];
    [apply HLoads; [split; [left;exact HD|exact HValid]|assumption|assumption]|].
  destruct (Pos.eq_dec b bw) as [HW|HW];
    [apply HLoads; [split; [right;left;exact HW|exact HValid]|assumption|assumption]|].
  destruct (Pos.eq_dec b bi) as [HI|HI];
    [apply HLoads; [split; [right;right;exact HI|exact HValid]|assumption|assumption]|].
  apply (proj1 HFrame); [exact HValid|]; intros pos HPos.
  unfold extA, fext; intros [[H|[H|H]] _]; contradiction.
Qed.
Timeout 60 Print Assumptions gej_is_infinity_literal_local_spec.
