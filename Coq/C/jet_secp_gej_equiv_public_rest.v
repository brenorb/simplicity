(** Derive the original public read/read/helper/write/return sequence from
    general frames against the exact fixed Simplicity composition. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_exec C.jet_encoding C.jet_readBit_layout C.jet_frame_layout C.jet_input_layout
 C.jet_output_layout C.jet_frame_inv C.jet_sx_mem C.jet_sx_state C.jet_sx_exec C.jet_secp_linkage
 C.jets_secp C.jet_secp_frame C.jet_secp_rescale_public_reads C.jet_secp_curve_frame
 C.jet_secp_gej_equiv_public_body C.jet_secp_gej_pair_reads
 C.jet_secp_gej_equiv_function C.jet_secp_gej_equiv_literal C.jet_secp_gej_add_public_entry C.jet_secp_mixed_public_entry C.jet_secp_bit_writer.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_gej_equiv.

Theorem exec_gej_equiv_public_rest_owned le m0 bd base bw outedge cursor N bi edge rc
 (x y z u v w : Ty.tySem (Word 8)) m bp ba bl :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 write_frame_at m0 bd base bw outedge cursor N -> 1<=N ->
 frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
 frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits y)) ->
 frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits z)) ->
 frame_input_cells_at m0 bi edge (rc+768) (map Some (frame_input_word_bits u)) ->
 frame_input_cells_at m0 bi edge (rc+1024) (map Some (frame_input_word_bits v)) ->
 frame_input_cells_at m0 bi edge (rc+1280) (map Some (frame_input_word_bits w)) ->
 0<=rc -> rc+1536<=Int64.max_unsigned ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable ->
 Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi edge rc ->
 bp<>bl -> ba<>bl -> bp<>ba -> xsep (extA m0 bd bw bi) [(bp,0);(ba,0);(bl,0)] ->
 finv m0 bd base bw outedge cursor N bi m false [] -> exists mf,
 Clight2.exec_stmt secp_ge (gej_add_public_env bl bp ba) le m gej_equiv_public_rest E0
  (PTree.set _t'1 (Vint (if (Bit.toBool (@literal_gej_equiv Alg.CoreFunSem (((x,y),z),((u,v),w)))) then Int.one else Int.zero)) le) mf
  (Out_return (Some (Vint Int.one,tint))) /\
 finv m0 bd base bw outedge cursor N bi mf true [Some ((Bit.toBool (@literal_gej_equiv Alg.CoreFunSem (((x,y),z),((u,v),w)))))] /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 Mem.range_perm mf bl 0 16 Cur Freeable /\ lframe (rescale_locals_outside m0 bd bw bi bp ba bl) m mf.
Proof.
 intros HD HO HN HX HY HZ HU HV HW Hrc HM FP FA FL Source PL AL PA Sep Fin.
 destruct (eval_gej_pair_public_reads m0 bd base bw outedge cursor N 1 bi edge rc x y z u v w m bp ba bl
  HO ltac:(lia) HN HX HY HZ HU HV HW Hrc HM FP FA FL Source PL AL PA Sep Fin)
  as (mr & ms & RP & RA & X & Y & Z & U & V & W & FlagP & FlagA & FPS & FAS & FLS & FinS & FrameR).
 destruct (eval_gej_equiv_reader x y z u v w ms bp ba PA X Y Z U V W FlagP FlagA FPS FAS)
  as (mn & Helper & FPN & FAN & FrameH).
 assert (FLN : Mem.range_perm mn bl 0 16 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FLS|exact FrameH|];intros;split;congruence. }
 assert (FinN : finv m0 bd base bw outedge cursor N bi mn false []).
 { eapply finv_stable;[exact HO|exact FinS|].
   eapply lframe_implies;[exact FrameH|];intros b pos HE HB;split;intro EQ;subst b;
    [apply (Sep 0%nat ltac:(cbn;lia))|apply (Sep 1%nat ltac:(cbn;lia))];exact HE. }
 destruct (eval_secp_writeBit_from_invariant m0 bd base bw outedge cursor N bi mn
  ((Bit.toBool (@literal_gej_equiv Alg.CoreFunSem (((x,y),z),((u,v),w))))) HO HN FinN) as (mf & Write & Final & FrameW & PermW).
 assert (ExtD : extA m0 bd bw bi bd)
  by (apply fext_bd with (dbase:=base) (outedge:=outedge) (cursor:=cursor) (N:=N);exact HO).
 assert (ExtW : extA m0 bd bw bi bw).
 { split;[right;left;reflexivity|];eapply bw_valid;[exact HO|lia]. }
 assert (Outside : forall b,b=bp \/ b=ba \/ b=bl -> ~extA m0 bd bw bi b).
 { intros b [HE|[HE|HE]];subst b;
   [exact (Sep 0%nat ltac:(cbn;lia))|exact (Sep 1%nat ltac:(cbn;lia))|exact (Sep 2%nat ltac:(cbn;lia))]. }
 assert (NoWrite : forall b,b=bp \/ b=ba \/ b=bl -> b<>bd /\ b<>bw).
 { intros b HB;pose proof (Outside b HB);split;intro EQ;subst b;contradiction. }
 assert (FPF : Mem.range_perm mf bp 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FPN|exact FrameW|];intros;apply NoWrite;tauto. }
 assert (FAF : Mem.range_perm mf ba 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FAN|exact FrameW|];intros;apply NoWrite;tauto. }
 assert (FLF : Mem.range_perm mf bl 0 16 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FLN|exact FrameW|];intros;apply NoWrite;tauto. }
 exists mf;split.
 - eapply exec_gej_equiv_public_rest_from_calls;eassumption.
 - split;[exact Final|];split;[exact FPF|];split;[exact FAF|];split;[exact FLF|].
   eapply lframe_trans;[exact FrameR|];eapply lframe_trans.
   + eapply lframe_implies;[exact FrameH|];intros b pos (NP & NA & NL & NE) HB;split;assumption.
   + eapply lframe_implies;[exact FrameW|];intros b pos (NP & NA & NL & NE) HB;
     split;intro EQ;subst b;contradiction.
Qed.
