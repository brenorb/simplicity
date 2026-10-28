(** The existing field-call footprints exclude the affine point's flag.
    These facts retain the flag through the actual validity helper calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Memory Values.
Require Import C.jet_sx_state C.jet_sx_rep C.jet_sx_mem
 C.jet_secp_curve_square C.jet_secp_curve_mul C.jet_secp_curve_frame.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma curve_square_flag_readback k bout bin m mf :
 bout<>bin -> Mem.valid_block m bin ->
 lframe (fun b pos=>~foot ((bout,0)::(bin,0)::nil)
   (map rshape (curve_square_regs k)) b pos) m mf ->
 Mem.load Mint32 mf bin 80=Mem.load Mint32 m bin 80.
Proof.
 intros Different Valid Frame;apply (proj1 Frame);[exact Valid|].
 intros pos Range Foot.
 destruct (curve_square_foot k bout bin bin pos Foot) as [[Same _]|[_ At]].
 - congruence.
 - destruct k;cbn [curve_square_offset] in At;cbn [size_chunk] in Range;lia.
Qed.
Lemma curve_mul_flag_readback bout bin m mf :
 bout<>bin -> Mem.valid_block m bin ->
 lframe (fun b pos=>~foot ((bout,0)::(bin,0)::nil)
   (map rshape curve_mul_regs) b pos) m mf ->
 Mem.load Mint32 mf bin 80=Mem.load Mint32 m bin 80.
Proof.
 intros Different Valid Frame;rewrite curve_mul_square_shape in Frame.
 exact (curve_square_flag_readback false bout bin m mf Different Valid Frame).
Qed.
