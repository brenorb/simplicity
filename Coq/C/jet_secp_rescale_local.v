(** Public C-to-literal-Simplicity equivalence for every input word and every
    frame satisfying the repository's standard local jet contract. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_word_repr C.jet_frame_layout C.jet_input_layout C.jet_write_layout.
Require Import C.jet_output_layout C.jet_encoding C.jet_frame_inv C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_normalize_local.
Require Import C.jet_secp_rescale_literal C.jet_secp_rescale_public_call.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_gej_rescale.

Theorem gej_rescale_literal_local_spec :
  secp_jet_local_spec f_simplicity_gej_rescale
    (Ty.Prod (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (Word 8))
    (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))
    (@literal_gej_rescale Alg.CoreFunSem).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HBase HAlign HSource HCursor HMax HInput HOutput.
  destruct a as [[[x y] z] s].
  change (rc+1024 <= Int64.max_unsigned) in HMax.
  change (write_frame_at m bd dbase bw outedge cursor 768) in HOutput.
  change (frame_input_cells_at m bi edge rc (((encode x ++ encode y) ++ encode z) ++ encode s)) in HInput.
  rewrite !frame_input_cells_at_app, !app_length, !encode_word_length in HInput.
  destruct HInput as [[[HX HY] HZ] HS].
  change (frame_input_cells_at m bi edge (rc+256) (encode y)) in HY.
  change (frame_input_cells_at m bi edge (rc+512) (encode z)) in HZ.
  change (frame_input_cells_at m bi edge (rc+768) (encode s)) in HS.
  rewrite encode_word in HX, HY, HZ, HS.
  destruct (eval_gej_rescale_literal_public env m bd dbase bs sbase bw outedge cursor 768 bi edge rc
    x y z s HOutput ltac:(lia) HBase HAlign HSource HX HY HZ HS HCursor HMax)
    as (mf & HCall & HFinal & HFrame).
  destruct HFinal as (HV & HF & HN & (HCells & HPrefix & HFields & HLoads & HPerms) & Hw).
  rewrite encode_length in HFields, HLoads.
  exists mf; split; [exact HCall|]; split; [exact HCells|].
  split; [exact HPrefix|]; split; [exact HFields|].
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
