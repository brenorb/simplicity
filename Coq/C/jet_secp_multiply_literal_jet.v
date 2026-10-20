(** Original public C jet against the existing literal Simplicity specification. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_frame_inv C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_normalize_local C.jet_secp_negate_literal_contract.
Require Import C.jet_secp_multiply_public_public C.jet_secp_multiply_literal_spec.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_fe_multiply Simplicity.Translate.encode.

Theorem eval_original_public_field_multiply_literal v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    (x y : Ty.tySem (Word 8)) :
  write_frame_at m0 bd dbase bw outedge cursor N -> 256 <= N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  frame_input_cells_at m0 bi edge rc
    (@Simplicity.Translate.encode (Ty.Prod (Word 8) (Word 8)) (x, y)) ->
  0 <= rc -> rc + 512 <= Int64.max_unsigned ->
  exists mf,
    Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_fe_multiply)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] E0 mf (Vint Int.one) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (@Simplicity.Translate.encode (Word 8) (@literal_fe_multiply Alg.CoreFunSem (x, y))) /\
    lframe (fun b _ => ~ extA m0 bd bw bi b) m0 mf.
Proof.
  intros HO HC HB HA HF HI HR HM.
  destruct (eval_original_public_field_multiply v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    x y HO HC HB HA HF HI HR HM) as (mf & HCall & HFinal & HFrame).
  rewrite input_product_matches_literal in HFinal.
  exists mf; split; [exact HCall|]; split; assumption.
Qed.

Theorem fe_multiply_literal_local_spec :
  secp_jet_local_spec f_simplicity_fe_multiply (Ty.Prod (Word 8) (Word 8)) (Word 8)
    (@literal_fe_multiply Alg.CoreFunSem).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [x y]
    HBase HAlign HSource HCursor HMax HInput HOutput.
  change (rc + 512 <= Int64.max_unsigned) in HMax.
  change (write_frame_at m bd dbase bw outedge cursor 256) in HOutput.
  destruct (eval_original_public_field_multiply_literal env m bd dbase bs sbase bw outedge cursor 256 bi edge rc
    x y HOutput ltac:(lia) HBase HAlign HSource HInput HCursor HMax)
    as (mf & HCall & HFinal & HFrame).
  destruct HFinal as [HV [HF [HN [[HCells [HPrefix [HFields [HLoads HPerms]]]] Hw]]]].
  rewrite Simplicity.Translate.encode_length in HFields, HLoads.
  exists mf; split; [exact HCall|]; split; [exact HCells|]; split; [exact HPrefix|]; split; [exact HFields|].
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
