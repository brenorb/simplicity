(** Original public C X-equivalence against its literal Simplicity program. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_frame_inv C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_normalize_local C.jet_secp_x_equiv_literal C.jet_secp_x_equiv_public_call.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_gej_x_equiv Simplicity.Translate.encode.

Lemma x_equiv_input_windows m bi edge rc (q x y z : tySem (Word 8)) :
  frame_input_cells_at m bi edge rc
    (@encode (Ty.Prod (Word 8) (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))) (q,((x,y),z))) ->
  frame_input_cells_at m bi edge rc (map Some (frame_input_word_bits q)) /\
  frame_input_cells_at m bi edge (rc+256) (map Some (frame_input_word_bits x)) /\
  frame_input_cells_at m bi edge (rc+512) (map Some (frame_input_word_bits y)) /\
  frame_input_cells_at m bi edge (rc+768) (map Some (frame_input_word_bits z)).
Proof.
  intro HInput.
  change (frame_input_cells_at m bi edge rc
    (encode q ++ ((encode x ++ encode y) ++ encode z))) in HInput.
  rewrite !frame_input_cells_at_app, !app_length, !encode_word_length in HInput.
  change (frame_input_cells_at m bi edge rc (encode q) /\
    (frame_input_cells_at m bi edge (rc+256) (encode x) /\
     frame_input_cells_at m bi edge (rc+256+256) (encode y)) /\
    frame_input_cells_at m bi edge (rc+256+512) (encode z)) in HInput.
  rewrite !encode_word in HInput. destruct HInput as (HQ & (HX & HY) & HZ).
  split;[exact HQ|]. split;[exact HX|]. split.
  - replace (rc+512) with (rc+256+256) by lia;exact HY.
  - replace (rc+768) with (rc+256+512) by lia;exact HZ.
Qed.

Theorem gej_x_equiv_literal_local_spec :
  secp_jet_local_spec f_simplicity_gej_x_equiv
    (Ty.Prod (Word 8) (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))) (Ty.Sum Ty.Unit Ty.Unit)
    (@literal_gej_x_equiv Alg.CoreFunSem).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [q [[x y] z]]
    HBase HAlign HSource HCursor HMax HInput HOutput.
  change (rc+1024<=Int64.max_unsigned) in HMax.
  change (write_frame_at m bd dbase bw outedge cursor 1) in HOutput.
  destruct (x_equiv_input_windows m bi edge rc q x y z HInput) as (HQ & HX & HY & HZ).
  destruct (eval_gej_x_equiv_literal_public env m bd dbase bs sbase bw outedge cursor 1 bi edge rc
    q x y z HOutput ltac:(lia) HBase HAlign HSource HQ HX HY HZ HCursor HMax)
    as (mf & HCall & HFinal & HFrame).
  destruct HFinal as [HV [HF [HN [[HCells [HPrefix [HFields [HLoads HPerms]]]] Hw]]]].
  rewrite encode_length in HFields,HLoads.
  exists mf. split;[exact HCall|]. split;[exact HCells|]. split;[exact HPrefix|]. split;[exact HFields|].
  intros chunk b ofs HValid HFrameOther HOutputOther.
  destruct (Pos.eq_dec b bd) as [HD|HD];
    [apply HLoads;[split;[left;exact HD|exact HValid]|assumption|assumption]|].
  destruct (Pos.eq_dec b bw) as [HW|HW];
    [apply HLoads;[split;[right;left;exact HW|exact HValid]|assumption|assumption]|].
  destruct (Pos.eq_dec b bi) as [HI|HI];
    [apply HLoads;[split;[right;right;exact HI|exact HValid]|assumption|assumption]|].
  apply (proj1 HFrame);[exact HValid|]. intros pos HPos.
  unfold extA,fext;intros [[HE|[HE|HE]] _];contradiction.
Qed.
