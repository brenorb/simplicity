(** Complete original public C jet against its fixed primitive-bearing term. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout
 C.jet_encoding C.jet_frame_inv C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp
 C.jet_secp_normalize_local C.jet_secp_gej_ge_equiv_reader C.jet_secp_gej_ge_equiv_literal
 C.jet_secp_gej_ge_equiv_bridge C.jet_secp_gej_ge_equiv_public_call.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_gej_ge_equiv.

Theorem gej_ge_equiv_literal_local_spec :
 secp_jet_local_spec f_simplicity_gej_ge_equiv
  (Ty.Prod (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (Ty.Prod (Word 8) (Word 8)))
  (Ty.Sum Ty.Unit Ty.Unit) (@literal_gej_ge_equiv Alg.CoreFunSem).
Proof.
 intros env m bd dbase bs sbase bi bw edge outedge cursor rc [[[x y] z] [u v]]
  HBase HAlign HSource HCursor HMax HInput HOutput.
 change (rc+1280<=Int64.max_unsigned) in HMax.
 change (write_frame_at m bd dbase bw outedge cursor 1) in HOutput.
 change (frame_input_cells_at m bi edge rc (((encode x++encode y)++encode z)++(encode u++encode v))) in HInput.
 rewrite !frame_input_cells_at_app,!app_length,!encode_word_length in HInput.
 destruct HInput as [[[HX HY] HZ] [HU HV]].
 change (frame_input_cells_at m bi edge (rc+256) (encode y)) in HY.
 change (frame_input_cells_at m bi edge (rc+512) (encode z)) in HZ.
 change (frame_input_cells_at m bi edge (rc+768) (encode u)) in HU.
 change (frame_input_cells_at m bi edge (rc+768+256) (encode v)) in HV.
 replace (rc+768+256) with (rc+1024) in HV by lia.
 rewrite encode_word in HX,HY,HZ,HU,HV.
 destruct (eval_gej_ge_equiv_public_c_bit env m bd dbase bs sbase bw outedge cursor 1 bi edge rc
  x y z u v HOutput ltac:(lia) HBase HAlign HSource HX HY HZ HU HV HCursor HMax)
  as (mf & HCall & HFinal & HFrame).
 rewrite gej_ge_equiv_reader_matches_literal in HFinal.
 assert (Encoding : [Some (Bit.toBool (@literal_gej_ge_equiv Alg.CoreFunSem (((x,y),z),(u,v))))]=
  encode (@literal_gej_ge_equiv Alg.CoreFunSem (((x,y),z),(u,v)))).
 { destruct (@literal_gej_ge_equiv Alg.CoreFunSem (((x,y),z),(u,v))) as [b|b];destruct b;reflexivity. }
 rewrite Encoding in HFinal.
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
