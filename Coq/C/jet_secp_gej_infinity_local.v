From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout C.jet_encoding C.jet_frame_inv C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_normalize_local C.jet_secp_literal_infinity C.jet_secp_gej_public_call.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_gej_infinity encode.
Theorem gej_infinity_literal_local_spec :
  secp_jet_local_spec f_simplicity_gej_infinity Ty.Unit (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))
    (@literal_gej_infinity Alg.CoreFunSem).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HBase HAlign HSource HCursor HMax HInput HOutput.
  destruct a.
  change (write_frame_at m bd dbase bw outedge cursor 768) in HOutput.
  destruct (eval_gej_infinity_literal_public env m bd dbase bs sbase bw outedge cursor 768 bi edge rc
    HOutput ltac:(lia) HBase HAlign HSource)
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
Print Assumptions gej_infinity_literal_local_spec.
