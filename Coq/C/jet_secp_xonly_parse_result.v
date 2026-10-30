(** Exact success/failure meaning of the original x-only parser's return. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Simplicity.Alg.
Require Import C.jet_toZ C.jet_read8s_layout C.jet_sx_mem C.jet_memcpy_model C.jet_memset_model
 C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math C.jet_secp_decompress_literal
 C.jet_secp_xonly_parse_control C.jet_secp_xonly_parse_field C.jet_secp_xonly_parse_function
 C.jet_secp_affine_storage C.jet_secp_storage_numeric C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_decompress.
Lemma xonly_sum_distinct {A B} (a:A) (b:B):(inl a:sum A B)<>inr b.
Proof. discriminate. Qed.
Lemma xonly_parse_success_iff (pk:Ty.tySem (Word 8)):
 xonly_parse_result pk=Int.one <->@toZ (WordToZ 8) pk<feP /\
 exists ax ay,@literal_decompress Simplicity.Alg.CoreFunSem ((inl tt),pk)=inr (ax,ay).
Proof.
 pose (decoded:=@literal_decompress Simplicity.Alg.CoreFunSem ((inl tt:Ty.tySem Bit),pk)).
 change ((if Z.ltb (@toZ (WordToZ 8) pk) feP then
  match decoded with inl _=>Int.zero|inr _=>Int.one end else Int.zero)=Int.one <->
  @toZ (WordToZ 8) pk<feP /\ exists ax ay,decoded=inr (ax,ay)).
 destruct (Z.ltb (@toZ (WordToZ 8) pk) feP) eqn:Accepted.
 - apply Z.ltb_lt in Accepted;destruct decoded as [[]|[ax ay]].
   + split.
     * intro Bad;exfalso;apply Int.one_not_zero;symmetry;exact Bad.
     * intros [_ (a & b & Bad)];exfalso;exact (xonly_sum_distinct tt (a,b) Bad).
   + split;[intros _;split;[exact Accepted|exists ax,ay;reflexivity]|intros _;reflexivity].
 - apply Z.ltb_ge in Accepted;split.
   + intro Bad;exfalso;apply Int.one_not_zero;symmetry;exact Bad.
   + intros [Bound _];exfalso;lia.
Qed.
Lemma xonly_parse_failure_iff (pk:Ty.tySem (Word 8)):
 xonly_parse_result pk=Int.zero <->feP<=@toZ (WordToZ 8) pk \/
 @literal_decompress Simplicity.Alg.CoreFunSem ((inl tt),pk)=inl tt.
Proof.
 pose (decoded:=@literal_decompress Simplicity.Alg.CoreFunSem ((inl tt:Ty.tySem Bit),pk)).
 change ((if Z.ltb (@toZ (WordToZ 8) pk) feP then
  match decoded with inl _=>Int.zero|inr _=>Int.one end else Int.zero)=Int.zero <->
  feP<=@toZ (WordToZ 8) pk \/ decoded=inl tt).
 destruct (Z.ltb (@toZ (WordToZ 8) pk) feP) eqn:Accepted.
 - apply Z.ltb_lt in Accepted;destruct decoded as [[]|[ax ay]].
   + split;[intros _;right;reflexivity|intros _;reflexivity].
   + split.
     * intro Bad;exfalso;exact (Int.one_not_zero Bad).
     * intros [Bound|Bad];[exfalso;lia|exfalso;exact (xonly_sum_distinct tt (ax,ay) (eq_sym Bad))].
 - apply Z.ltb_ge in Accepted;split;[intros _;left;exact Accepted|intros _;reflexivity].
Qed.
Theorem eval_xonly_pubkey_parse_success (Copy:memcpy_model) (Clear:memset_model)
 (pk ax ay:Ty.tySem (Word 8)) m bout bin:
 @toZ (WordToZ 8) pk<feP ->@literal_decompress Simplicity.Alg.CoreFunSem ((inl tt),pk)=inr (ax,ay) ->
 bout<>bin ->Mem.range_perm m bout 0 64 Cur Freeable ->Mem.range_perm m bin 0 32 Cur Freeable ->
 uint8_array_at m bin 0 (map Int.repr (xonly_input_bytes pk)) ->exists mf storage,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_xonly_pubkey_parse)
 [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf (Vint Int.one) /\
 affine_storage_readable mf bout 0 storage /\
 field_storage_value storage=@toZ (WordToZ 8) ax /\
 field_storage_value (fun i=>storage (4+i)%nat)=@toZ (WordToZ 8) ay /\
 Mem.range_perm mf bout 0 64 Cur Freeable /\Mem.range_perm mf bin 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bout /\b<>bin) m mf /\readonly_preserved m mf.
Proof.
 intros Bound Decoded Separate FreeOut FreeIn Input.
 destruct (eval_xonly_pubkey_parse_owned Copy Clear pk m bout bin Separate FreeOut FreeIn Input)
 as (mf & Call & Parsed & FreeO & FreeI & Frame & Read).
 assert (Success:xonly_parse_result pk=Int.one).
 { apply xonly_parse_success_iff;split;[exact Bound|exists ax,ay;exact Decoded]. }
 rewrite Success in Call.
 destruct (Parsed Bound ax ay Decoded) as (storage & Storage & VX & VY).
 exists mf,storage;split;[exact Call|];split;[exact Storage|];split;[exact VX|];split;[exact VY|].
 split;[exact FreeO|];split;[exact FreeI|];split;assumption.
Qed.
