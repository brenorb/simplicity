(** Original write_gej for any proved literal output triple, reusing the general writer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Values Memory Events.
Require Import Simplicity.Word Simplicity.Ty Simplicity.Alg.
Require Simplicity.Translate.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem
  C.jet_frame_inv C.jet_output_layout C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp
  C.jet_secp_point_three_general_writes C.jet_secp_rescale_writer C.jet_secp_rescale_literal
  C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
  C.jet_secp_gej_negate_literal.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Simplicity.Translate.encode.

Lemma point_output_encoding x y z (result : Ty.tySem (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))) :
  ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=
    result ->
  ((Simplicity.Translate.encode (rescale_field_output x)++Simplicity.Translate.encode (rescale_field_output y))++
    Simplicity.Translate.encode (rescale_field_output z))=
    Simplicity.Translate.encode (result).
Proof.
  intro HE;pose proof (f_equal (@Simplicity.Translate.encode (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))) HE) as HC.
  rewrite (@point_encode_pair (Ty.Prod (Word 8) (Word 8)) (Word 8)),(@point_encode_pair (Word 8) (Word 8)) in HC.
  exact HC.
Qed.
Theorem eval_write_gej_literal_output m0 bd dbase bw edge cursor N bi (rc : Z) m bp
    x y z (result : Ty.tySem (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))) :
  write_frame_at m0 bd dbase bw edge cursor N -> 768<=N ->
  finv m0 bd dbase bw edge cursor N bi m false [] ->
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> xsep (extA m0 bd bw bi) [(bp,0)] ->
  ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=
    result ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_write_gej)
    [Vptr bd (Ptrofs.repr dbase);Vptr bp Ptrofs.zero] E0 mf Vundef /\
  finv m0 bd dbase bw edge cursor N bi mf true
    (Simplicity.Translate.encode (result)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\
  lframe (fun b _ => b<>bp /\ ~extA m0 bd bw bi b) m mf.
Proof.
  intros HO HN HI BX BY BZ HX HY HZ HF HS HE.
  rewrite <-rescale_point_limbs in HX,HY,HZ.
  destruct (eval_write_gej_general m0 bd dbase bw edge cursor N bi rc m bp
    (rescale_point_field x) (rescale_point_field y) (rescale_point_field z) HO HN HI
    (rescale_point_bounds _ BX) (rescale_point_bounds _ BY) (rescale_point_bounds _ BZ) HX HY HZ HF HS)
    as (mf & HC & HFin & HFree & HFrame).
  rewrite !rescale_point_output,(point_output_encoding x y z result HE) in HFin.
  exists mf;split;[exact HC|];split;[exact HFin|];split;assumption.
Qed.
