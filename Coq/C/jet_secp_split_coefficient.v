(** Instantiate the original rounded-product function with either actual
    split-lambda global. The final storage is the literal rounded coefficient;
    all input representation and counting/rounding obligations are discharged. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_word_repr C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_scalar_constant C.jet_secp_split_multipliers
 C.jet_secp_scalar_borrowed_inputs C.jet_secp_scalar_mul_reader_bridge
 C.jet_secp_scalar_mul_borrowed_alloc C.jet_secp_scalar_mul512_low
 C.jet_secp_scalar_mul_writer_bridge C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_shift384_function C.jet_secp_split_round_literal
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge split_multiplier_block.

Lemma split_multiplier_limbs first :
 map Int64.repr (scalar_limbs_of (split_multiplier_value first))=split_multiplier_words first.
Proof.
 rewrite <-(split_multiplier_value_checked first);apply four_words_scalar_limbs;apply split_multiplier_count.
Qed.

Theorem eval_split_coefficient first k m bk bc : 0<=k<2^256 -> split_multipliers_ready m ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of k)) ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m bc 0 32 Cur Freeable -> bc<>bk ->
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul_shift_var)
 [Vptr bc Ptrofs.zero;Vptr bk Ptrofs.zero;Vptr (split_multiplier_block first) Ptrofs.zero;Vint (Int.repr 384)] E0 mf Vundef /\
 scalar_at mf bc 0 (map Int64.repr (scalar_limbs_of (split_coefficient first k))) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of k)) /\
 Mem.range_perm mf bc 0 32 Cur Freeable /\ Mem.range_perm mf bk 0 32 Cur Freeable /\
 split_multipliers_ready mf /\ keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun b _=>b<>bc /\ b<>bk /\ b<>split_multiplier_block first) m mf.
Proof.
 intros Range Ready Input FreeK FreeC Separate.
 pose proof (Ready first) as Global.
 assert (KB:bk<>split_multiplier_block first) by (eapply scalar_constant_separate;[exact Global|exact FreeK]).
 assert (CB:bc<>split_multiplier_block first) by (eapply scalar_constant_separate;[exact Global|exact FreeC]).
 assert (GlobalInput:scalar_at m (split_multiplier_block first) 0
  (map Int64.repr (scalar_limbs_of (split_multiplier_value first)))).
 { rewrite split_multiplier_limbs;exact (proj1 Global). }
 pose proof (scalar_borrowed_inputs_from_storage k (split_multiplier_value first) m bk
  (split_multiplier_block first) Input GlobalInput FreeK KB) as Inputs.
 destruct (eval_scalar_mul_shift384_borrowed (scalar_mul_reader_rho k (split_multiplier_value first))
  [(bk,0);(split_multiplier_block first,0)] m bc Inputs FreeC
  ltac:(intros [|[|r]] R;[exact Separate|exact CB|lia]))
  as (mf & Call & Output & InputsF & FreeCF & Keep & Preserve & Frame).
 destruct (scalar_mul_reader_input_values k (split_multiplier_value first) Range
  ltac:(pose proof (split_multiplier_bounds first);lia)) as [InputValue GlobalValue].
 unfold shift384_output_value in Output;rewrite InputValue,GlobalValue in Output.
 destruct (scalar_borrowed_inputs_source k (split_multiplier_value first) mf bk (split_multiplier_block first) InputsF)
  as [InputF FreeKF].
 exists mf;split;[exact Call|];split;[exact Output|];split;[exact InputF|];split;[exact FreeCF|];split;
 [exact FreeKF|];split;[eapply split_multipliers_readonly;[exact Ready|exact Preserve]|];
 split;[exact Keep|];split;[exact Preserve|].
 eapply lframe_implies;[exact Frame|].
 intros b ofs (NotC & NotK & NotG) Valid;split;[exact NotC|].
 intros (r & sh & d & ch & Nth & Cell & Eq & Bytes);destruct r as [|[|r]].
 - apply NotK;exact Eq.
 - apply NotG;exact Eq.
 - cbn [scalar_mul_borrowed_inputs map nth_error] in Nth;destruct r;discriminate Nth.
Qed.

Theorem eval_split_coefficient_literal first (k:Ty.tySem (Word 8)) m bk bc : split_multipliers_ready m ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k))) ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m bc 0 32 Cur Freeable -> bc<>bk ->
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul_shift_var)
 [Vptr bc Ptrofs.zero;Vptr bk Ptrofs.zero;Vptr (split_multiplier_block first) Ptrofs.zero;Vint (Int.repr 384)] E0 mf Vundef /\
 scalar_at mf bc 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (@literal_split_coefficient first Alg.CoreFunSem k)))) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k))) /\
 Mem.range_perm mf bc 0 32 Cur Freeable /\ Mem.range_perm mf bk 0 32 Cur Freeable /\
 split_multipliers_ready mf /\ keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun b _=>b<>bc /\ b<>bk /\ b<>split_multiplier_block first) m mf.
Proof.
 intros Ready Input FK FC Separate;rewrite literal_split_coefficient_numeric.
 apply eval_split_coefficient;[apply word_toZ_range|exact Ready|exact Input|exact FK|exact FC|exact Separate].
Qed.
