(** Derive the original guarded public remainder from its input/frame storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.jet_exec C.jet_readBit_layout C.jet_encoding C.jet_input_layout C.jet_output_layout.
Require Import C.jet_frame_layout C.jet_frame_inv C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_wrapper_run C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_public_body C.jet_secp_bit_writer C.jet_secp_gej_flag_read.
Require Import C.jet_secp_canonical_zero C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_square_spec_bridge C.jet_secp_rescale_public_reads C.jet_secp_curve_frame.
Require Import C.jet_secp_x_equiv_function C.jet_secp_x_equiv_literal C.jet_secp_x_equiv_literal_bridge.
Require Import C.jet_secp_x_equiv_public_reads C.jet_secp_x_equiv_public_statements.
Import ListNotations Clightdefs Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_gej_x_equiv canonical_fe_is_zero Simplicity.Translate.encode.

Definition x_equiv_word_comparison (q x z : tySem (Word 8)) :=
  Z.eqb (radix_value (square_reader_rho x) mod feP)
    ((radix_value (square_reader_rho z)*radix_value (square_reader_rho z)*radix_value (square_reader_rho q)) mod feP).
Lemma x_equiv_word_result q x z :
  x_equiv_result (square_reader_rho q) (square_reader_rho x) (square_reader_rho z) =
    bit_int (x_equiv_word_comparison q x z).
Proof. reflexivity. Qed.

Theorem eval_x_equiv_guarded_call (q x z : tySem (Word 8)) (inf : bool) m bp bq :
  bp<>bq -> fe_at m bp 0 (words5 (square_reader_rho x)) ->
  fe_at m bp 80 (words5 (square_reader_rho z)) -> fe_at m bq 0 (words5 (square_reader_rho q)) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bq 0 40 Cur Freeable ->
  exists mn,
    (if inf then mn=m else Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_eq_x_var)
      [Vptr bq Ptrofs.zero;Vptr bp Ptrofs.zero] E0 mn (Vint (bit_int (x_equiv_word_comparison q x z)))) /\
    Mem.range_perm mn bp 0 128 Cur Freeable /\ Mem.range_perm mn bq 0 40 Cur Freeable /\
    lframe (fun b _ => b<>bp /\ b<>bq) m mn.
Proof.
  intros HPQ HX HZ HQ HFP HFQ;destruct inf.
  - exists m. split;[reflexivity|]. split;[exact HFP|]. split;[exact HFQ|apply lframe_refl].
  - destruct (eval_x_equiv_function (square_reader_rho q) (square_reader_rho x) (square_reader_rho z)
      m bp bq (square_reader_bounds q) (square_reader_bounds x) (square_reader_bounds z)
      HPQ HX HZ HQ HFP HFQ) as (mn & HC & PFn & QFn & HF).
    rewrite x_equiv_word_result in HC. exists mn. split;[exact HC|].
    split;[exact PFn|]. split;assumption.
Qed.

Theorem exec_x_equiv_public_rest_owned le m0 bd dbase bw outedge cursor N bi edge rc
    (q x y z : tySem (Word 8)) m bp bq bl :
  le!_dst=Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m0 bd dbase bw outedge cursor N -> 1<=N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits q)) ->
  frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits y)) ->
  frame_input_cells_at m0 bi edge (rc+768) (map Some (frame_input_word_bits z)) ->
  0<=rc -> rc+1024<=Int64.max_unsigned ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bq 0 40 Cur Freeable ->
  Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi edge rc ->
  bp<>bl -> bq<>bl -> bp<>bq -> xsep (extA m0 bd bw bi) [(bp,0);(bq,0);(bl,0)] ->
  finv m0 bd dbase bw outedge cursor N bi m false [] ->
  exists le' mf,
    Clight2.exec_stmt secp_ge (x_equiv_public_env bl bq bp) le m x_equiv_public_rest E0 le' mf
      (Out_return (Some (Vint Int.one,tint))) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_gej_x_equiv Alg.CoreFunSem (q,((x,y),z)))) /\
    Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bq 0 40 Cur Freeable /\
    Mem.range_perm mf bl 0 16 Cur Freeable /\
    lframe (rescale_locals_outside m0 bd bw bi bp bq bl) m mf.
Proof.
  intros HD HO HN HQ HX HY HZ Hrc HM HFP HFQ HFL HSource HPL HQL HPQ HSep HFin.
  destruct (eval_x_equiv_public_reads m0 bd dbase bw outedge cursor N bi edge rc q x y z m bp bq bl
    HO HN HQ HX HY HZ Hrc HM HFP HFQ HFL HSource HPL HQL HPQ HSep HFin)
    as (mq & mr & CQ & CP & FX & FZ & FQ & Flag & PFR & QFR & FLR & FinR & FrameR).
  set (inf := Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)).
  set (comp := x_equiv_word_comparison q x z).
  pose proof (eval_gej_flag_accessor mr bp 0 (bit_int inf) ltac:(lia)
    ltac:(change Ptrofs.max_unsigned with 18446744073709551615;lia) Flag) as CF.
  destruct (eval_x_equiv_guarded_call q x z inf mr bp bq HPQ FX FZ FQ PFR QFR)
    as (mn & CE & PFN & QFN & FrameN).
  assert (ExtN : eqext m0 bd bw bi mr mn).
  { eapply lframe_implies;[exact FrameN|]. intros b pos HE HV;split;intro HB;subst b;
      [exact (HSep 0%nat ltac:(cbn;lia) HE)|exact (HSep 1%nat ltac:(cbn;lia) HE)]. }
  assert (FinN : finv m0 bd dbase bw outedge cursor N bi mn false []).
  { eapply finv_stable;eassumption. }
  pose proof (curve_keep_free _ mr mn bl 16 ltac:(lia) FLR FrameN
    ltac:(intro pos;split;congruence)) as FLN.
  destruct (eval_secp_writeBit_from_invariant m0 bd dbase bw outedge cursor N bi mn
    (andb (negb inf) comp) HO HN FinN) as (mf & CW & FinW & FrameW & PermW).
  assert (HBit : andb (negb inf) comp = Bit.toBool (@literal_gej_x_equiv Alg.CoreFunSem (q,((x,y),z)))).
  { assert (HE : bit_int (andb (negb inf) comp) =
      bit_int (Bit.toBool (@literal_gej_x_equiv Alg.CoreFunSem (q,((x,y),z))))).
    { rewrite <- x_equiv_guarded_result_literal. fold inf.
      destruct inf;[reflexivity|exact (eq_sym (x_equiv_word_result q x z))]. }
    destruct (andb (negb inf) comp), (Bit.toBool (@literal_gej_x_equiv Alg.CoreFunSem (q,((x,y),z))));
      try reflexivity;discriminate HE. }
  assert (HVD : Mem.valid_block m0 bd).
  { pose proof HO as [_ [[HE _] _]]. exact (load_valid _ _ _ _ _ HE). }
  assert (HVW : Mem.valid_block m0 bw).
  { destruct (write_frame_at_head m0 bd dbase bw outedge cursor N ltac:(lia) HO)
      as [_ [_ [_ [w HL]]]]. exact (load_valid _ _ _ _ _ HL). }
  exists (x_equiv_branch_temps le inf comp),mf. split.
  - eapply exec_x_equiv_public_rest_from_calls;eassumption.
  - split.
    + assert (HE : Simplicity.Translate.encode (@literal_gej_x_equiv Alg.CoreFunSem (q,((x,y),z))) =
        [Some (andb (negb inf) comp)]).
      { rewrite HBit. destruct (@literal_gej_x_equiv Alg.CoreFunSem (q,((x,y),z)));reflexivity. }
      rewrite HE;exact FinW.
    + split;[intros pos HP;apply PermW;apply PFN;exact HP|].
      split;[intros pos HP;apply PermW;apply QFN;exact HP|].
      split;[intros pos HP;apply PermW;apply FLN;exact HP|].
      eapply lframe_trans;[exact FrameR|]. eapply lframe_trans.
      * eapply lframe_implies;[exact FrameN|]. intros b pos (HNP & HNQ & HNL & HNE) HV;split;assumption.
      * eapply lframe_implies;[exact FrameW|]. intros b pos (HNP & HNQ & HNL & HNE) HV.
        unfold extA,fext in HNE;split;intro HB;subst b;apply HNE;split;
          [left;reflexivity|exact HVD|right;left;reflexivity|exact HVW].
Qed.
