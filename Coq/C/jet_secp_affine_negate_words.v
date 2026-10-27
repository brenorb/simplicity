(** Reuse the original affine negation executor for arbitrary stored limbs,
    including weak-normalized table entries rather than reader-only limbs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem
 C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_multiply_normalize_bridge
 C.jet_secp_write_fe_wide_values C.jet_secp_owned_field_slice C.jet_secp_point_write_run C.jet_secp_local_regions
 C.jet_secp_affine_weak_exec C.jet_secp_affine_negate_exec C.jet_secp_affine_negate_owned
 C.jet_secp_field_negate_values C.jet_secp_field_negate_separate.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition affine_words_rho (w:nat->int64) := wide_fe_rho (w 0%nat) (w 1%nat)
 (w 2%nat) (w 3%nat) (w 4%nat) 0.

Lemma affine_words_rho_shift w i : (i<5)%nat -> affine_words_rho w (S i)=w i.
Proof. intros Bound;do 5 (destruct i as [|i];[reflexivity|]);lia. Qed.

Lemma affine_y_words_initial w m b : fe_at m b 40 (words5 w) ->
 Mem.range_perm m b 0 88 Cur Freeable ->
 rep (affine_words_rho w) [(b,0)] (affine_initial_regs AffineY) m.
Proof.
 intros Field Free;change (rep (affine_words_rho w) [(b,0)] (owned_field_slice 40 88) m).
 apply owned_field_slice_initial_rep;[lia|exact Field|exact Free].
Qed.

Lemma affine_y_foot_range b bx pos :
 foot [(b,0)] (map rshape (affine_initial_regs AffineY)) bx pos -> bx=b /\ 40<=pos<80.
Proof.
 intros (r & shape & d & ch & Lookup & Member & Same & Range).
 destruct r as [|r];[|destruct r;discriminate Lookup].
 inversion Lookup;subst shape.
 change (bx=b) in Same;split;[exact Same|].
 change (In (d,ch) [(40,Mint64);(48,Mint64);(56,Mint64);(64,Mint64);(72,Mint64)]) in Member.
 change (d<=pos<d+size_chunk ch) in Range.
 destruct Member as [E|[E|[E|[E|[E|E]]]]];try contradiction;
  inversion E;subst d ch;change (size_chunk Mint64) with 8 in Range;lia.
Qed.

Theorem eval_affine_y_negate_words w m b :
 fe_at m b 40 (words5 w) -> Mem.range_perm m b 0 88 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
  [Vptr b (Ptrofs.repr 40);Vptr b (Ptrofs.repr 40);Vint Int.one] E0 mf Vundef /\
 fe_at mf b 40 (words5 (negate_sep_words w)) /\
 Mem.range_perm mf b 0 88 Cur Freeable /\
 lframe (fun bx pos=>bx<>b \/ pos<40 \/ 80<=pos) m mf.
Proof.
 intros Field Free.
 destruct (eval_affine_negate_from_owned_region AffineY m [(b,0)] (affine_words_rho w)
  (affine_y_words_initial w m b Field Free)) as (mf & Call & Final & Frame).
 assert (FreeF:Mem.range_perm mf b 0 88 Cur Freeable).
 { exact (proj2 (rep_free_region _ _ _ _ 0 88 Final ltac:(change (0<1)%nat;lia)
    (affine_negate_owned_size AffineY))). }
 exists mf;split;[exact Call|];split.
 - destruct Field as (Base & Align & Max & Perm & Loads).
   split;[exact Base|];split;[exact Align|];split;[exact Max|];split.
   + intros pos Range;eapply Mem.perm_implies;[apply FreeF;change (40<=pos<40+40) in Range;lia|constructor].
   + intros i v Nth.
     assert (Index:(i<5)%nat).
     { change (i<length (words5 (negate_sep_words w)))%nat;apply nth_error_Some;rewrite Nth;discriminate. }
     assert (Value:v=negate_value (affine_words_rho w) i).
     { do 5 (destruct i as [|i];[inversion Nth;reflexivity|]);lia. }
     rewrite Value;exact (affine_negate_rep_loads AffineY mf [(b,0)] (affine_words_rho w) Final i Index).
 - split;[exact FreeF|].
   eapply lframe_implies;[exact Frame|].
   intros bx pos Outside Valid Foot;destruct (affine_y_foot_range b bx pos Foot) as [Same Range].
   destruct Outside as [Other|[Before|After]];[congruence|lia|lia].
Qed.
