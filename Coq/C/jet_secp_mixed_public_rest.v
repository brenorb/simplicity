(** Derive the original public read/read/helper/write/return sequence. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_exec C.jet_encoding C.jet_word_repr C.jet_readBit_layout C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
 C.jet_sx_mem C.jet_sx_state C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.jet_secp_frame C.jet_secp_public_body
 C.jet_secp_public_copy C.jet_secp_wrapper_run C.jet_secp_rescale_public_reads
 C.jet_secp_mixed_public_entry C.jet_secp_mixed_public_body C.jet_secp_mixed_public_reads
 C.jet_secp_mixed_literal_bridge C.jet_secp_point_output_literal C.jet_secp_add_literal.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_gej_ge_add Simplicity.Translate.encode.

Theorem exec_mixed_rest_owned le m0 bd dbase bw outedge cursor N bi edge rc
    (x y z u v : Ty.tySem (Word 8)) m bp ba bl :
 le!_dst=Some (Vptr bd (Ptrofs.repr dbase)) ->
 write_frame_at m0 bd dbase bw outedge cursor N -> 768<=N ->
 frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
 frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits y)) ->
 frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits z)) ->
 frame_input_cells_at m0 bi edge (rc+768) (map Some (frame_input_word_bits u)) ->
 frame_input_cells_at m0 bi edge (rc+1024) (map Some (frame_input_word_bits v)) ->
 0<=rc -> rc+1280<=Int64.max_unsigned ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi edge rc ->
 bp<>bl -> ba<>bl -> bp<>ba -> xsep (extA m0 bd bw bi) [(bp,0);(ba,0);(bl,0)] ->
 finv m0 bd dbase bw outedge cursor N bi m false [] ->
 exists mf,
 Clight2.exec_stmt secp_ge (mixed_public_env bl bp ba) le m mixed_public_rest E0 le mf
   (Out_return (Some (Vint Int.one,tint))) /\
 finv m0 bd dbase bw outedge cursor N bi mf true
   (Simplicity.Translate.encode (@literal_gej_ge_add Alg.CoreFunSem (((x,y),z),(u,v)))) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bl 0 16 Cur Freeable /\ lframe (rescale_locals_outside m0 bd bw bi bp ba bl) m mf.
Proof.
 intros HD HO HN HX HY HZ HU HV Hrc HM HFP HFA HFL HSource HPL HAL HPA HSep HFin.
 destruct (eval_mixed_public_reads m0 bd dbase bw outedge cursor N bi edge rc x y z u v m bp ba bl
   HO HN HX HY HZ HU HV Hrc HM HFP HFA HFL HSource HPL HAL HPA HSep HFin)
   as (mr & ms & CP & CA & FX & FY & FZ & FU & FV & FlagP & FlagA & FPS & FAS & FLS & FinS & ReadFrame).
 destruct (eval_mixed_literal x y z u v ms bp ba HPA FlagP FlagA FX FY FZ FU FV FPS FAS)
   as (mn & ox & oy & oz & CH & OX & OY & OZ & FPN & FAN & BX & BY & BZ & Literal & HelperFrame).
 assert (FLN : Mem.range_perm mn bl 0 16 Cur Freeable).
 { intros pos HP;apply (proj1 (proj2 HelperFrame)).
   - eapply Mem.perm_valid_block;apply (FLS 0);lia.
   - split;congruence.
   - apply FLS;exact HP. }
 assert (FinN : finv m0 bd dbase bw outedge cursor N bi mn false []).
 { eapply finv_stable;[exact HO|exact FinS|].
   eapply lframe_implies;[exact HelperFrame|];intros b pos HE HB;split;intro EQ;subst b;
     [apply (HSep 0%nat ltac:(cbn;lia))|apply (HSep 1%nat ltac:(cbn;lia))];exact HE. }
 assert (HSP : xsep (extA m0 bd bw bi) [(bp,0)]).
 { intros [|r] HI;[exact (HSep 0%nat ltac:(cbn;lia))|cbn in HI;lia]. }
 destruct (eval_write_gej_literal_output m0 bd dbase bw outedge cursor N bi rc mn bp ox oy oz
   (@literal_gej_ge_add Alg.CoreFunSem (((x,y),z),(u,v))) HO HN FinN BX BY BZ OX OY OZ FPN HSP Literal)
   as (mf & CW & Final & FPF & WriteFrame).
 assert (FAF : Mem.range_perm mf ba 0 88 Cur Freeable).
 { intros pos HP;apply (proj1 (proj2 WriteFrame)).
   - eapply Mem.perm_valid_block;apply (FAN 0);lia.
   - split;[congruence|exact (HSep 1%nat ltac:(cbn;lia))].
   - apply FAN;exact HP. }
 assert (FLF : Mem.range_perm mf bl 0 16 Cur Freeable).
 { intros pos HP;apply (proj1 (proj2 WriteFrame)).
   - eapply Mem.perm_valid_block;apply (FLN 0);lia.
   - split;[congruence|exact (HSep 2%nat ltac:(cbn;lia))].
   - apply FLN;exact HP. }
 exists mf;split.
 - eapply exec_mixed_rest_from_calls;eassumption.
 - split;[exact Final|];split;[exact FPF|];split;[exact FAF|];split;[exact FLF|].
   eapply lframe_trans;[exact ReadFrame|];eapply lframe_trans.
   + eapply lframe_implies;[exact HelperFrame|];intros b pos (NP & NA & NL & NE) HB;split;assumption.
   + eapply lframe_implies;[exact WriteFrame|];intros b pos (NP & NA & NL & NE) HB;split;assumption.
Qed.
