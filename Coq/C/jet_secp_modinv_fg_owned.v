(** Restore the actual transition caller's owned matrix representation. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_call C.jet_secp_modinv_fg_permissions.
Require Import C.jet_secp_modinv_fg_start C.jet_secp_modinv_fg_body C.jet_secp_linkage C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fg_matrix_cells := u64_cells 0 [XLv 10;XLv 11;XLv 12;XLv 13].
Definition fg_matrix_region (owned : bool) := mkreg fg_matrix_cells owned (if owned then Some 32 else None).
Definition fg_region_default := mkreg [] false None.
Definition fg_owned_regs := [nth 0 fg_regs fg_region_default;nth 1 fg_regs fg_region_default;fg_matrix_region true].
Definition fg_result_array len (high : bool) := nth (if high then 1 else 0) (fg_call_out len) fg_region_default.
Definition fg_owned_out len := [fg_result_array len false;fg_result_array len true;fg_matrix_region true].

Lemma fg_rep_three rho beta m a b c : length beta=3%nat -> rsep beta [a;b;c] ->
 region_ok rho beta m 0 a -> region_ok rho beta m 1 b -> region_ok rho beta m 2 c -> rep rho beta [a;b;c] m.
Proof.
 intros Len Sep A B C;split;[exact Len|];split;[exact Sep|].
 intros [|[|[|r]]] reg Entry;cbn [nth_error] in Entry.
 - injection Entry as <-;exact A.
 - injection Entry as <-;exact B.
 - injection Entry as <-;exact C.
 - destruct r;discriminate Entry.
Qed.
Definition fg_three_distinct beta := forall i j,(i<3)%nat -> (j<3)%nat -> i<>j -> blk beta i<>blk beta j.
Lemma fg_sep_three_distinct beta a b c : rfree a<>None -> rfree b<>None -> rsep beta [a;b;c] -> fg_three_distinct beta.
Proof.
 intros A B Sep i j I J Ne.
 assert (Ei : nth_error [a;b;c] i=Some (nth i [a;b;c] fg_region_default)) by (apply nth_error_nth';exact I).
 assert (Ej : nth_error [a;b;c] j=Some (nth j [a;b;c] fg_region_default)) by (apply nth_error_nth';exact J).
 destruct (Sep i j _ _ Ne Ei Ej) as [Different|(OI & OJ & Disjoint)];[exact Different|].
 exfalso;destruct i as [|[|[|i]]],j as [|[|[|j]]];try lia;cbn [nth] in OI,OJ;congruence.
Qed.
Lemma fg_distinct_three_sep beta a b c : fg_three_distinct beta -> rsep beta [a;b;c].
Proof.
 intros Distinct i j ri rj Ne Ei Ej;left;apply Distinct;[| |exact Ne].
 - apply (proj1 (nth_error_Some [a;b;c] i));rewrite Ei;discriminate.
 - apply (proj1 (nth_error_Some [a;b;c] j));rewrite Ej;discriminate.
Qed.

Lemma fg_matrix_weaken rho beta m r : region_ok rho beta m r (fg_matrix_region true) ->
 region_ok rho beta m r (fg_matrix_region false).
Proof.
 intros (Base & Valid & Sorted & Cells & Owned);unfold region_ok,fg_matrix_region;cbn [rcells rw rfree] in *.
 split;[exact Base|];split;[exact Valid|];split;[exact Sorted|];split;[|exact I].
 apply Forall_forall;intros c Member;pose proof (proj1 (Forall_forall _ _) Cells c Member) as Cell.
 destruct Cell as (Max & Aligned & Perm & Value);unfold cell_ok;cbn.
 split;[exact Max|];split;[exact Aligned|];split;[|exact Value].
 intros ofs Range;eapply Mem.perm_implies;[apply Perm;exact Range|constructor].
Qed.
Lemma fg_matrix_cell_bounds : Forall (fun c=>0<=cofs c /\ cofs c+size_chunk (cchunk c)<=32) fg_matrix_cells.
Proof. repeat constructor;cbn;lia. Qed.
Lemma fg_matrix_restore rho beta m r : region_ok rho beta m r (fg_matrix_region false) ->
 bas beta r=0 -> Mem.range_perm m (blk beta r) 0 32 Cur Freeable ->
 region_ok rho beta m r (fg_matrix_region true).
Proof.
 intros (Base & Valid & Sorted & Cells & _) Zero Owned.
 unfold region_ok,fg_matrix_region;cbn [rcells rw rfree] in *.
 split;[exact Base|];split;[exact Valid|];split;[exact Sorted|];split.
 - apply Forall_forall;intros c Member.
   destruct (proj1 (Forall_forall _ _) Cells c Member) as (Max & Aligned & Perm & Value).
   destruct (proj1 (Forall_forall _ _) fg_matrix_cell_bounds c Member) as (Low & High).
   unfold cell_ok;cbn;split;[exact Max|];split;[exact Aligned|];split;[|exact Value].
   intros ofs Range;rewrite Zero in Range;cbn [Z.add] in Range.
   eapply Mem.perm_implies;[apply Owned;lia|constructor].
 - split;[exact Zero|];split;[reflexivity|];split;[exact Owned|].
   eapply Forall_impl;[|exact fg_matrix_cell_bounds];intros c (_ & High);exact High.
Qed.

Lemma fg_call_three len : (0<len<=5)%nat ->
 fg_call_out len=[fg_result_array len false;fg_result_array len true;fg_matrix_region false].
Proof. destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;reflexivity. Qed.
Lemma fg_call_arrays_owned len high : (0<len<=5)%nat -> rfree (fg_result_array len high)=Some 40.
Proof. destruct high;destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;reflexivity. Qed.

Lemma fg_owned_weaken rho beta m : rep rho beta fg_owned_regs m -> rep rho beta fg_regs m.
Proof.
 intros (Len & Sep & Regions);apply fg_rep_three.
 - exact Len.
 - apply fg_distinct_three_sep;eapply (fg_sep_three_distinct beta
    (nth 0 fg_regs fg_region_default) (nth 1 fg_regs fg_region_default) (fg_matrix_region true));
    [discriminate|discriminate|exact Sep].
 - exact (Regions 0%nat _ eq_refl).
 - exact (Regions 1%nat _ eq_refl).
 - apply fg_matrix_weaken;exact (Regions 2%nat _ eq_refl).
Qed.
Lemma fg_owned_matrix rho beta m : rep rho beta fg_owned_regs m ->
 bas beta 2=0 /\ Mem.range_perm m (blk beta 2) 0 32 Cur Freeable.
Proof.
 intro Rep;pose proof (rep_region rho beta _ m 2 _ Rep eq_refl) as Region.
 destruct Region as (_ & _ & _ & _ & Zero & _ & Owned & _);split;assumption.
Qed.
Lemma fg_output_restore rho beta len m : (0<len<=5)%nat -> rep rho beta (fg_call_out len) m ->
 bas beta 2=0 -> Mem.range_perm m (blk beta 2) 0 32 Cur Freeable -> rep rho beta (fg_owned_out len) m.
Proof.
 intros Len Rep Zero Owned;rewrite (fg_call_three len Len) in Rep;destruct Rep as (Length & Sep & Regions).
 apply fg_rep_three.
 - exact Length.
 - apply fg_distinct_three_sep;eapply (fg_sep_three_distinct beta
    (fg_result_array len false) (fg_result_array len true) (fg_matrix_region false));[| |exact Sep];
   rewrite fg_call_arrays_owned by exact Len;discriminate.
 - exact (Regions 0%nat _ eq_refl).
 - exact (Regions 1%nat _ eq_refl).
 - apply fg_matrix_restore;[exact (Regions 2%nat _ eq_refl)|exact Zero|exact Owned].
Qed.

Theorem eval_fg_transition_owned len rho beta m : (0<len<=5)%nat ->
 Int64.loword (rho 14%nat)=Int.repr (Z.of_nat len) -> fg_input_bounds rho -> rep rho beta fg_owned_regs m -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_update_fg_62_var)
  [Vint (Int.repr (Z.of_nat len));Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef /\
 (forall (high : bool) j,(j<len)%nat -> Mem.load Mint64 mf (blk beta (if high then 1 else 0))
  (bas beta (if high then 1 else 0)+8*Z.of_nat j)=Some (Vlong (fg_body_word len rho high j))) /\
 (forall high,fg_body_value len rho high=fg_matrix_value rho high len/2^62) /\
 rep (fg_body_rho len rho) beta (fg_owned_out len) mf /\
 lframe (fun b ofs=>~foot beta (map rshape fg_regs) b ofs) m mf.
Proof.
 intros Bound Len Bounds Rep;destruct (fg_owned_matrix rho beta m Rep) as (Zero & Matrix).
 destruct (eval_fg_transition_matrix_permissions len rho beta m Bound Len Bounds (fg_owned_weaken rho beta m Rep) Matrix)
  as (mf & Call & Freeable & Words & Numeric & Out & Frame).
 exists mf;split;[exact Call|];split;[exact Words|];split;[exact Numeric|];split;[|exact Frame].
 apply fg_output_restore;assumption.
Qed.
