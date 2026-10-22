(** Original public C jet against the fixed primitive-bearing square-root term.
    No assumption about mathematical square roots is required. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout
 C.jet_encoding C.jet_frame_inv C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp
 C.jet_secp_normalize_local C.jet_secp_root_literal C.jet_secp_root_public_call.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_fe_square_root Simplicity.Translate.encode.

Theorem fe_square_root_literal_local_spec :
 secp_jet_local_spec f_simplicity_fe_square_root (Word 8) (Ty.Sum Ty.Unit (Word 8))
  (@literal_fe_square_root Simplicity.Alg.CoreFunSem).
Proof.
 intros env m bd base bs sbase bi bw edge outedge cursor rc x
  HBase HAlign HSource HCursor HMax HInput HOutput.
 change (rc+256<=Int64.max_unsigned) in HMax.
 change (write_frame_at m bd base bw outedge cursor 257) in HOutput.
 rewrite encode_word in HInput.
 destruct (eval_fe_square_root_literal_public env m bd base bs sbase bw outedge cursor 257 bi edge rc
  x HOutput ltac:(lia) HBase HAlign HSource HInput HCursor HMax)
  as (mf & HCall & HFinal & HFrame).
 destruct HFinal as (HValid & HF & HN & (HCells & HPrefix & HFields & HLoads & HPerms) & Hw).
 rewrite encode_length in HFields,HLoads.
 exists mf;split;[exact HCall|];split;[exact HCells|];split;[exact HPrefix|];split;[exact HFields|].
 intros chunk b ofs HValidB HFrameOther HOutputOther.
 destruct (Pos.eq_dec b bd) as [HD|HD];
  [apply HLoads;[split;[left;exact HD|exact HValidB]|assumption|assumption]|].
 destruct (Pos.eq_dec b bw) as [HW|HW];
  [apply HLoads;[split;[right;left;exact HW|exact HValidB]|assumption|assumption]|].
 destruct (Pos.eq_dec b bi) as [HI|HI];
  [apply HLoads;[split;[right;right;exact HI|exact HValidB]|assumption|assumption]|].
 apply (proj1 HFrame);[exact HValidB|];intros pos HPos.
 unfold extA,fext;intros [[HE|[HE|HE]] _];contradiction.
Qed.
