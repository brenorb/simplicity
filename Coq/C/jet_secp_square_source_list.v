From Coq Require Import List Lia.
Require Import C.jet_sx_expr C.jet_secp_square_execution C.jet_secp_square_schedule C.jet_secp_square_source_links.
Import ListNotations.
Set Default Timeout 10.
Local Opaque square_limbs sq_r0 sq_r1 sq_r2 sq_r3 sq_r4.
Lemma original_square_symbolic_output : square_limbs = [sq_r0;sq_r1;sq_r2;sq_r3;sq_r4].
Proof.
  apply nth_ext with (d := XLv 0) (d' := XLv 0).
  - rewrite square_limbs_count; reflexivity.
  - intros i HI; rewrite square_limbs_count in HI.
    destruct i as [|[|[|[|[|i]]]]]; try (exfalso; lia).
    + exact square_r0_source.
    + exact square_r1_source.
    + exact square_r2_source.
    + exact square_r3_source.
    + exact square_r4_source.
Qed.
