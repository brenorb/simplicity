(** Actual public field-invert read/inverse/write calls. All storage, output,
    ownership, framing and global preservation follow from the initial state. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.extraMath C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_exec C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_frame C.jet_secp_wrapper_run
 C.jet_frame_layout C.jet_frame_inv C.jet_input_layout C.jet_output_layout C.jet_encoding
 C.jet_secp_local_regions C.jet_secp_local_call C.jet_secp_public_body C.jet_secp_curve_frame
 C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_invert_literal
 C.jet_secp_fe_invert_writer C.jet_secp_negate_writer_bridge C.jet_secp_write_fe_wide_values
 C.jet_secp_write_fe_wide_exec C.jet_secp_modinfo_fe_caller C.jet_secp_fe_inverse_state
 C.jet_secp_field_io_preserve C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_fe_invert encode.

Theorem eval_field_read_invert_write m0 bd dbase bw outedge cursor N bi edge rc
 (value:Ty.tySem(Word 8)) m ba bl :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 write_frame_at m0 bd dbase bw outedge cursor N ->
 frame_input_cells_at m0 bi edge rc (map Some(frame_input_word_bits value)) ->
 0<=rc -> rc+256<=Int64.max_unsigned ->
 Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
 frame_fields_at m bl 0 bi edge rc -> ba<>bl ->
 xsep(extA m0 bd bw bi)[(ba,0);(bl,0)] ->
 invA m0 bd dbase bw outedge cursor N bi rc false [] 256
  (read_fe_rho(frame_input_word_bits value)rc) [] m ->
 modinfo_fe_state m -> exists mr mn mf,
 Clight2.eval_funcall secp_ge m(Internal f_read_fe)
  [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef /\
 Clight2.eval_funcall secp_ge mr(Internal f_secp256k1_fe_inv_var)
  [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mn Vundef /\
 Clight2.eval_funcall secp_ge mn(Internal f_write_fe)
  [Vptr bd(Ptrofs.repr dbase);Vptr ba Ptrofs.zero] E0 mf Vundef /\
 finv m0 bd dbase bw outedge cursor N bi mf true(encode(@literal_fe_invert Alg.CoreFunSem value)) /\
 Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf bl 0 16 Cur Freeable /\
 lframe(secp_locals_outside m0 bd bw bi ba bl)m mf /\ modinfo_fe_state mf /\ readonly_preserved m mf.
Proof.
 intros CountCall HO HI Hrc HM HA HL HS Separate Sep Inv Ready.
 destruct(eval_local_read_fe_canonical m0 bd dbase bw outedge cursor N bi edge rc value m ba bl
  HO HI Hrc HM HA HL HS Separate Sep Inv)
  as(mr & Read & Field & FreeAR & FreeLR & InvR & ReadFrame).
 pose proof(field_reader_preserved _ _ _ _ _ Read) as ReadReadonly.
 pose proof(proj1(modinfo_fe_state_preserved m mr Ready ReadReadonly)) as ReadyR.
 destruct(fe_inverse_writer_from_reader mr ba value CountCall ReadyR Field FreeAR)
  as(result & mn & Inverse & Stored & ResultBounds & OutputWord & FreeAN & ReadyN & InverseFrame & InverseReadonly).
 assert(InverseExt:lframe(fun b _=>extA m0 bd bw bi b)mr mn).
 { eapply lframe_implies;[exact InverseFrame|].
   intros b pos Ext Valid Same;subst b;exact(Sep 0%nat ltac:(cbn;lia)Ext). }
 assert(InvN:invA m0 bd dbase bw outedge cursor N bi rc false [] 256
  (read_fe_rho(frame_input_word_bits value)rc)(read_fe_log bi(Ptrofs.repr edge))mn).
 { eapply invA_stable;[exact HO|exact InvR|exact InverseExt]. }
 assert(FreeLN:Mem.range_perm mn bl 0 16 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FreeLR|exact InverseFrame|];intros;congruence. }
 assert(ValidLN:Mem.valid_block mn bl) by(eapply Mem.perm_valid_block;apply(FreeLN 0);lia).
 set(wrho:=wide_fe_rho(result 0%nat)(result 1%nat)(result 2%nat)(result 3%nat)(result 4%nat)rc).
 assert(WriterRep:rep wrho[(ba,0)]local_write_initial_regs mn).
 { apply wide_field_initial_rep;[exact Stored|exact FreeAN]. }
 assert(WriterSep:xsep(extA m0 bd bw bi)[(ba,0)]).
 { intros r R;destruct r as[|r];[apply(Sep 0%nat);cbn;lia|cbn in R;lia]. }
 assert(WriterInv:invA m0 bd dbase bw outedge cursor N bi rc false [] 256 wrho [] mn).
 { change(Int64.repr rc=Int64.repr rc /\ finv m0 bd dbase bw outedge cursor N bi mn false [] /\
   256<=N /\ 0<=256) in InvN |- *;exact InvN. }
 assert(Wide:forall i,(i<5)%nat -> Int64.unsigned(result i)<=2^60).
 { intros i I;pose proof(ResultBounds i I);destruct(Nat.eqb i 4);lia. }
 destruct(eval_local_wide_write_fe m0 bd dbase bw outedge cursor N bi rc
  (result 0%nat)(result 1%nat)(result 2%nat)(result 3%nat)(result 4%nat) false [] mn[(ba,0)]
  HO(Wide 0%nat ltac:(lia))(Wide 1%nat ltac:(lia))(Wide 2%nat ltac:(lia))
  (Wide 3%nat ltac:(lia))(Wide 4%nat ltac:(lia)) WriterRep WriterSep WriterInv)
  as(mf & Write & Final & WrittenRep & WriteFrame).
 rewrite OutputWord in Final;cbn [app] in Final.
 pose proof(wide_local_final_freeable _ ba mf bd(Ptrofs.repr dbase)WrittenRep) as FreeA.
 assert(FrameL:forall pos,frame(extA m0 bd bw bi)[(ba,0)]local_write_initial_regs mn bl pos).
 { intro pos;split;[exact ValidLN|];split.
   - apply no_local_write_foot;congruence.
   - exact(Sep 1%nat ltac:(cbn;lia)). }
 assert(FreeLF:Mem.range_perm mf bl 0 16 Cur Freeable).
 { intros pos Range;eapply(proj1(proj2 WriteFrame));[exact ValidLN|apply FrameL|apply FreeLN;exact Range]. }
 pose proof(field_writer_preserved _ _ _ _ _ Write) as WriteReadonly.
 exists mr,mn,mf;split;[exact Read|];split;[exact Inverse|];split;[exact Write|];
 split;[exact Final|];split;[exact FreeA|];split;[exact FreeLF|];split.
 - eapply lframe_trans.
   + eapply lframe_implies;[exact ReadFrame|].
     intros b pos[NotA [NotL NotExt]] Valid;split;[exact Valid|];split;
      [apply no_local_read_foot;assumption|exact NotExt].
   + eapply lframe_trans.
     * eapply lframe_implies;[exact InverseFrame|];intros b pos[NotA [NotL NotExt]] Valid;exact NotA.
     * eapply lframe_implies;[exact WriteFrame|];intros b pos[NotA [NotL NotExt]] Valid.
       split;[exact Valid|];split;[apply no_local_write_foot;exact NotA|exact NotExt].
 - split;[exact(proj1(modinfo_fe_state_preserved mn mf ReadyN WriteReadonly))|].
   eapply preserved_trans;[exact ReadReadonly|];eapply preserved_trans;[exact InverseReadonly|exact WriteReadonly].
Qed.
