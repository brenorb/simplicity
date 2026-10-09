(** Full canonical public contract for the original field zero jet. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout C.jet_encoding C.jet_frame_inv C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_normalize_local C.jet_secp_canonical_zero C.jet_secp_zero_lifecycle.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_is_zero encode.
Theorem fe_zero_local_spec :
  secp_jet_local_spec f_simplicity_fe_is_zero (Word 8) Bit
    (@canonical_fe_is_zero Alg.CoreFunSem).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HBase HAlign HSource HCursor HMax HInput HOutput.
  change (rc + 256 <= Int64.max_unsigned) in HMax.
  change (write_frame_at m bd dbase bw outedge cursor 1) in HOutput.
  rewrite encode_word in HInput.
  destruct (eval_secp_fe_zero_canonical env m bd dbase bs sbase bw outedge cursor 1 bi edge rc a
    HOutput ltac:(lia) HBase HAlign HSource HInput HCursor HMax)
    as [mf [HCall [HFinal HFrame]]].
  destruct HFinal as [HV [HF [HN [[HCells [HPrefix [HFields [HLoads HPerms]]]] Hw]]]].
  rewrite encode_length in HFields, HLoads.
  exists mf; split; [exact HCall|]; split; [exact HCells|]; split; [exact HPrefix|];
    split; [exact HFields|].
  intros chunk b ofs HValid HFrameOther HOutputOther.
  destruct (Pos.eq_dec b bd) as [HD|HD];
    [apply HLoads; [split; [left; exact HD|exact HValid]|assumption|assumption]|].
  destruct (Pos.eq_dec b bw) as [HW|HW];
    [apply HLoads; [split; [right; left; exact HW|exact HValid]|assumption|assumption]|].
  destruct (Pos.eq_dec b bi) as [HI|HI];
    [apply HLoads; [split; [right; right; exact HI|exact HValid]|assumption|assumption]|].
  apply (proj1 HFrame); [exact HValid|]; intros pos HPos.
  unfold extA, fext; intros [[H|[H|H]] _]; contradiction.
Qed.
