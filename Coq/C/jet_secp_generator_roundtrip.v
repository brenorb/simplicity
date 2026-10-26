(** Compose the original save, load and affine-write calls from actual point
    fields. This is a caller span, not the missing whole hash_to_curve proof. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Translate.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame
  C.jet_frame_inv C.jet_output_layout C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_field_add_initial C.jet_secp_generator_save C.jet_secp_generator_save_values
  C.jet_secp_generator_save_initial C.jet_secp_generator_save_storage
  C.jet_secp_generator_codec C.jet_secp_generator_load_write C.jet_secp_curve_frame
  C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Simplicity.Translate.encode generator_saved_bytes.

Lemma generator_saved_concat_loads rho m bg :
  (forall (second:bool) i,(i<32)%nat ->
    Mem.load Mint8unsigned m bg ((if second then 32 else 0)+Z.of_nat i)=
      Some (Vint (nth i (map Int.repr (generator_saved_bytes rho (if second then 5 else 0))) Int.zero))) ->
  forall i,(i<64)%nat -> Mem.load Mint8unsigned m bg (Z.of_nat i)=
    Some (Vint (Int.repr (nth i (generator_saved_bytes rho 0++generator_saved_bytes rho 5) 0))).
Proof.
  intros Halves i Index;destruct (lt_dec i 32) as [Left|Right].
  - pose proof (Halves false i Left) as Load;rewrite Z.add_0_l in Load.
    rewrite app_nth1 by (rewrite generator_saved_bytes_length;exact Left).
    change (Mem.load Mint8unsigned m bg (Z.of_nat i)=
      Some (Vint (nth i (map Int.repr (generator_saved_bytes rho 0)) (Int.repr 0)))) in Load.
    rewrite map_nth in Load;exact Load.
  - pose proof (Halves true (i-32)%nat ltac:(lia)) as Load.
    change (Mem.load Mint8unsigned m bg (32+Z.of_nat (i-32))=
      Some (Vint (nth (i-32)%nat (map Int.repr (generator_saved_bytes rho 5)) (Int.repr 0)))) in Load.
    replace (32+Z.of_nat (i-32)) with (Z.of_nat i) in Load by lia.
    rewrite app_nth2 by (rewrite generator_saved_bytes_length;lia).
    rewrite generator_saved_bytes_length.
    rewrite map_nth in Load;exact Load.
Qed.

Theorem eval_generator_save_load_write m0 bd base bw edge cursor N bi (rc:Z) rho flag m bp bg :
  write_frame_at m0 bd base bw edge cursor N -> 512<=N ->
  finv m0 bd base bw edge cursor N bi m false [] ->
  bp<>bg -> fe_at m bp 0 (field_values rho 0) -> fe_at m bp 40 (field_values rho 5) ->
  Mem.load Mint32 m bp 80=Some (Vint flag) ->
  Mem.range_perm m bp 0 88 Cur Freeable -> Mem.range_perm m bg 0 64 Cur Freeable ->
  xsep (extA m0 bd bw bi) [(bp,0);(bg,0)] ->
  (forall i,(i<10)%nat -> Int64.unsigned (rho i)<=2^60) ->
  exists ms ml mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_generator_save)
    [Vptr bg Ptrofs.zero;Vptr bp Ptrofs.zero] E0 ms Vundef /\
  Clight2.eval_funcall secp_ge ms (Internal f_secp256k1_generator_load)
    [Vptr bp Ptrofs.zero;Vptr bg Ptrofs.zero] E0 ml Vundef /\
  Clight2.eval_funcall secp_ge ml (Internal f_write_ge)
    [Vptr bd (Ptrofs.repr base);Vptr bp Ptrofs.zero] E0 mf Vundef /\
  finv m0 bd base bw edge cursor N bi mf true
    (@Simplicity.Translate.encode (Ty.Prod (Word 8) (Word 8))
      (generator_loaded_output (generator_saved_bytes rho 0) (generator_saved_bytes rho 5))) /\
  Mem.range_perm mf bp 0 88 Cur Freeable /\ Mem.range_perm mf bg 0 64 Cur Freeable /\
  lframe (fun b _=>b<>bp /\ b<>bg /\ ~extA m0 bd bw bi b) m mf /\ readonly_preserved m mf.
Proof.
  intros Output Cap Inv Sep X Y Flag FP FG External Bounds.
  destruct (eval_generator_save_bytes flag rho [(bp,0);(bg,0)] m
    (generator_save_initial_from_fields rho flag m bp bg Sep X Y Flag FP FG) Bounds)
    as (ms & Save & FPS & FGS & FlagS & Halves & FrameS & ReadOnlyS).
  pose proof (curve_frame_two (generator_save_regs flag) bp bg m ms eq_refl FrameS) as FrameSave.
  assert (OutP:~extA m0 bd bw bi bp) by exact (External 0%nat ltac:(clear;cbn;lia)).
  assert (OutG:~extA m0 bd bw bi bg) by exact (External 1%nat ltac:(clear;cbn;lia)).
  assert (InvS:finv m0 bd base bw edge cursor N bi ms false []).
  { eapply finv_stable;[exact Output|exact Inv|].
    eapply lframe_implies;[exact FrameSave|];intros b pos Ext Valid;split;intro Same;subst b;contradiction. }
  pose proof (generator_saved_concat_loads rho ms bg Halves) as Bytes.
  destruct (eval_generator_load_write m0 bd base bw edge cursor N bi rc
    (generator_saved_bytes rho 0) (generator_saved_bytes rho 5) ms bp bg Output Cap InvS
    (generator_saved_bytes_length rho 0) (generator_saved_bytes_length rho 5)
    (generator_saved_bytes_bound rho 0) (generator_saved_bytes_bound rho 5)
    Sep FPS FGS External Bytes) as (ml & mf & Load & Write & Final & FPF & FGF & FrameRest & ReadOnlyRest).
  exists ms,ml,mf;split;[exact Save|];split;[exact Load|];split;[exact Write|];
    split;[exact Final|];split;[exact FPF|];split;[exact FGF|];split.
  - eapply lframe_trans.
    + eapply lframe_implies;[exact FrameSave|];intros b pos [NP [NG NE]] Valid;split;assumption.
    + exact FrameRest.
  - eapply preserved_trans;[exact ReadOnlyS|exact ReadOnlyRest].
Qed.
