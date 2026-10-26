(** Whole original saver call and its actual serialized byte loads. Initial
    representation and limb bounds are internal caller obligations, not new
    restrictions on the public hash_to_curve input. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep
  C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math C.jet_secp_fe_b32
  C.jet_secp_generator_save C.jet_secp_generator_save_values
  C.jet_secp_closed_helpers C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma generator_save_output_loads flag rho beta m :
  (forall i,(i<10)%nat -> Int64.unsigned (rho i)<=2^60) ->
  rep rho beta (generator_save_final_regs flag rho beta) m ->
  Mem.range_perm m (blk beta 0) 0 88 Cur Freeable /\
  Mem.range_perm m (blk beta 1) 0 64 Cur Freeable /\
  Mem.load Mint32 m (blk beta 0) 80=Some (Vint flag) /\
  (forall (second:bool) i,(i<32)%nat ->
    Mem.load Mint8unsigned m (blk beta 1) ((if second then 32 else 0)+Z.of_nat i)=
      Some (Vint (nth i (map Int.repr (be_bytes (generator_save_value rho (if second then 5 else 0)))) Int.zero))).
Proof.
  intros Bounds Rep.
  pose proof (rep_region _ _ _ m 0 _ Rep eq_refl) as R0.
  pose proof (rep_region _ _ _ m 1 _ Rep eq_refl) as R1.
  pose proof R0 as (_ & _ & _ & _ & Base0 & _ & Free0 & _).
  pose proof R1 as (_ & _ & _ & _ & Base1 & _ & Free1 & _).
  split;[exact Free0|];split;[exact Free1|];split.
  - pose proof (region_load _ _ _ 0 _ 80 Mint32 (XI flag) R0) as Load.
    rewrite Base0,Z.add_0_l in Load;apply Load.
    unfold generator_save_final_regs,generator_save_output_regs;apply in_or_app;right;apply in_or_app;right;left;reflexivity.
  - intros second i Index.
    set (offset:=if second then 5%nat else 0%nat).
    set (bytes:=generator_save_bytes offset (generator_save_choice rho beta offset)).
    assert (Nth:nth_error bytes i=Some (nth i bytes (XI Int.zero))).
    { apply nth_error_nth';unfold bytes;rewrite generator_save_bytes_length;exact Index. }
    pose proof (region_load _ _ _ 1 _ ((if second then 32 else 0)+Z.of_nat i)
      Mint8unsigned (nth i bytes (XI Int.zero)) R1) as Load.
    assert (Member:In (mkcell ((if second then 32 else 0)+Z.of_nat i) Mint8unsigned
      (Some (nth i bytes (XI Int.zero))))
      (rcells (nth 1 (generator_save_final_regs flag rho beta) (mkreg [] true None)))).
    { unfold generator_save_final_regs,generator_save_output_regs;cbn [nth rcells].
      destruct second;[apply in_or_app;right|apply in_or_app;left];
        apply generator_save_byte_cell_member;exact Nth. }
    specialize (Load Member);rewrite Base1,Z.add_0_l in Load.
    rewrite (generator_save_byte_value rho beta offset i (nth i bytes (XI Int.zero))) in Load.
    + exact Load.
    + intros j J;apply Bounds;unfold offset;destruct second;lia.
    + exact Nth.
Qed.

Theorem eval_generator_save_bytes flag rho beta m :
  rep rho beta (generator_save_regs flag) m ->
  (forall i,(i<10)%nat -> Int64.unsigned (rho i)<=2^60) ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_generator_save)
    [Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));Vptr (blk beta 0) (Ptrofs.repr (bas beta 0))] E0 mf Vundef /\
  Mem.range_perm mf (blk beta 0) 0 88 Cur Freeable /\
  Mem.range_perm mf (blk beta 1) 0 64 Cur Freeable /\
  Mem.load Mint32 mf (blk beta 0) 80=Some (Vint flag) /\
  (forall (second:bool) i,(i<32)%nat ->
    Mem.load Mint8unsigned mf (blk beta 1) ((if second then 32 else 0)+Z.of_nat i)=
      Some (Vint (nth i (map Int.repr (be_bytes (generator_save_value rho (if second then 5 else 0)))) Int.zero))) /\
  lframe (fun b pos=>~foot beta (map rshape (generator_save_regs flag)) b pos) m mf /\
  readonly_preserved m mf.
Proof.
  intros Initial Bounds.
  destruct (eval_generator_save_symbolic flag rho beta m Initial) as (mf & Run & Final & Frame).
  rewrite generator_save_selected_regs in Final.
  destruct (generator_save_output_loads flag rho beta mf Bounds Final) as (Free0 & Free1 & Flag & Bytes).
  exists mf;split;[exact Run|];split;[exact Free0|];split;[exact Free1|];split;[exact Flag|];
    split;[exact Bytes|];split;[exact Frame|].
  eapply (secp_closed_function_preserved f_secp256k1_generator_save);[vm_compute;reflexivity|reflexivity|exact Run].
Qed.
