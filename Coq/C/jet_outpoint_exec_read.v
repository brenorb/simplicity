(** Original 36-byte scratch-array reader, parameterized by its actual byte count. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_encoding.
Require Import C.jet_buffer_input C.jet_read8s_layout C.jet_elements_support_sha_add_n_exec.
Require Import C.jet_elements_support_sha_transport C.jet_elements_sha_program C.jet_elements_support_sha_linkage.
Require Import C.jets_elements C.jet_elements_linkage.
Require Import C.jet_nonce_exec_effects C.jet_nonce_exec_calls C.jet_nonce_exec_payload C.jet_outpoint_exec_shape.
Import Mem Values Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge sha_ge ge0.
Set Default Timeout 10.

Lemma op_count_cast m n : 0 <= n <= 36 ->
  Cop.sem_cast (Vint (Int.repr n)) tint tulong m = Some (Vlong (Int64.repr n)).
Proof.
  intro HN. change (Some (Vlong (Int64.repr (Int.signed (Int.repr n)))) = Some (Vlong (Int64.repr n))).
  rewrite Int.signed_repr; [reflexivity|].
  change (Int.min_signed) with (-2147483648). change Int.max_signed with 2147483647. lia.
Qed.

Theorem op_read_exec le m bl bm bb bx bi edge rc n (xs : list (Ty.tySem Word8)) :
  Z.of_nat (length xs) = n -> 0 <= n <= 36 ->
  bl <> bb -> bl <> bi -> bb <> bi ->
  0 <= rc -> rc + 8 * n <= Int64.max_unsigned ->
  frame_fields_at m bl 0 bi edge rc -> Mem.valid_access m Mint64 bl 8 Writable ->
  Mem.range_perm m bb 0 n Cur Writable ->
  frame_input_cells_at m bi edge rc (concat (map (@encode Word8) xs)) ->
  exists mf,
    Clight2.exec_stmt elements_ge (op_env bl bm bb bx) le m (op_read n) E0 le mf Out_normal /\
    uint8_array_at mf bb 0 (map word8_array_value xs) /\
    frame_fields_at mf bl 0 bi edge (rc + 8 * n) /\ nonce_effects m mf [bl; bb].
Proof.
  intros HLen HN Hlb Hli Hbi H0 HM HF PW PB HI.
  assert (HIv : forall i x, nth_error xs i = Some x -> frame_input_word_at m bi edge (rc + 8 * Z.of_nat i) x).
  { apply frame_input_byte_list. exact HI. }
  destruct (eval_read8s_layout m bb 0 bl 0 bi edge rc xs
    ltac:(lia) ltac:(rewrite HLen; change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(rewrite HLen; exact PB) Hlb Hli Hbi nonce_local_frame_base H0 ltac:(rewrite HLen; exact HM) HF PW HIv)
    as (mf & HRead & HArray & HFields & HLoads & HPerm & HValid).
  rewrite HLen in HRead, HFields.
  exists mf. split.
  - destruct nonce_readbytes_link as [HS HFun]. unfold op_read.
    change le with (set_opttemp None Vundef le) at 2.
    eapply exec_Scall with (vf := Vptr (elements_symbol_block _read8s) Ptrofs.zero)
      (f := Internal f_read8s) (vargs := [Vptr bb Ptrofs.zero; Vlong (Int64.repr n); Vptr bl Ptrofs.zero]) (vres := Vundef).
    + reflexivity.
    + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact HS]|apply deref_loc_reference; reflexivity].
    + eapply eval_Econs.
      * eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity].
      * reflexivity.
      * eapply eval_Econs; [apply eval_Econst_int|apply op_count_cast; exact HN|].
        eapply eval_Econs; [apply eval_Eaddrof, eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
    + exact HFun.
    + reflexivity.
    + rewrite <- elements_sha_genv. eapply sha_transport_call; [exact sg_in_read8s|exact HRead].
  - split; [exact HArray|]. split; [exact HFields|].
    constructor; [|exact HPerm|exact HValid]. intros ch b ofs V N.
    apply HLoads; left; intro E; subst b; apply N; cbn; tauto.
Qed.
