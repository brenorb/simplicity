(** The actual ascending C loop against the balanced literal pass1_8 tree.
    The comparison normalizes stored field encodings, including raw ratios;
    preserving the later pass2 consumers is a separate remaining obligation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_toZ C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_scalar_table_literal C.jet_secp_odd_table_literal_walk C.jet_secp_odd_table_loop C.jet_secp_odd_table_iteration
 C.jet_secp_mixed_xy_literal C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_rescale_literal C.jet_secp_canonical_normalize
 C.jet_secp_curve_statements C.jet_secp_slice_permissions C.jet_secp_add_literal
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_pass1_8 literal_table_advance literal_table_ratio canonical_fe_normalize rescale_field_output.
Local Opaque literal_gej_ge_add_ex.

Fixpoint literal_table_map_tree n (f:Ty.tySem (Word 8)->Ty.tySem (Word 8)) :
 Ty.tySem (literal_table_tree n) -> Ty.tySem (literal_table_tree n) :=
 match n as k return Ty.tySem (literal_table_tree k) -> Ty.tySem (literal_table_tree k) with
 | Datatypes.O=>fun p=>(f (fst p),f (snd p))
 | Datatypes.S k=>fun p=>(f (fst p),
   (literal_table_map_tree k f (fst (snd p)),literal_table_map_tree k f (snd (snd p)))) end.
Definition literal_table_normalize_tree n := literal_table_map_tree n (@canonical_fe_normalize Alg.CoreFunSem).
Definition literal_table_flat (xs ys ratios:nat->Ty.tySem (Word 8)) : Ty.tySem (literal_table_tree 3) :=
 (ratios 4,
  ((ratios 2,((ratios 1,((xs 0,ys 0),(xs 1,ys 1))),(ratios 3,((xs 2,ys 2),(xs 3,ys 3))))),
   (ratios 6,((ratios 5,((xs 4,ys 4),(xs 5,ys 5))),(ratios 7,((xs 6,ys 6),(xs 7,ys 7)))))))%nat.
Definition table_state_point s j := (rescale_field_output (odd_table_xs s j),rescale_field_output (odd_table_ys s j)).
Definition table_state_tree s : Ty.tySem (literal_table_tree 3) :=
 literal_table_flat (fun j=>rescale_field_output (odd_table_xs s j))
  (fun j=>rescale_field_output (odd_table_ys s j)) (fun j=>rescale_field_output (odd_table_ratios s j)).

Lemma literal_table_map_flat f xs ys ratios : literal_table_map_tree 3 f (literal_table_flat xs ys ratios)=
 literal_table_flat (fun j=>f (xs j)) (fun j=>f (ys j)) (fun j=>f (ratios j)).
Proof. reflexivity. Qed.
Lemma literal_table_flat_congr xs ys ratios xs' ys' ratios' :
 (forall k,(k<8)%nat -> xs k=xs' k) -> (forall k,(k<8)%nat -> ys k=ys' k) ->
 (forall k,(0<k<8)%nat -> ratios k=ratios' k) ->
 literal_table_flat xs ys ratios=literal_table_flat xs' ys' ratios'.
Proof.
 intros HX HY HR;unfold literal_table_flat.
 let rec pair_fields := lazymatch goal with
 | |- xs ?k=_=>exact (HX k ltac:(repeat constructor))
 | |- ys ?k=_=>exact (HY k ltac:(repeat constructor))
 | |- ratios ?k=_=>exact (HR k ltac:(repeat constructor))
 | |- (?a,?b)=(?c,?d)=>apply f_equal2;[pair_fields|pair_fields]
 end in pair_fields.
Qed.
Lemma literal_pass1_8_flat a b : fst (@literal_pass1_8 Alg.CoreFunSem (a,b))=
 literal_table_flat (fun j=>fst (fst (literal_table_advance j a b)))
  (fun j=>snd (fst (literal_table_advance j a b))) (fun j=>literal_table_ratio (Nat.pred j) a b).
Proof.
 destruct a as [[x y] z].
 refine (eq_trans (f_equal fst (literal_pass1_8_step ((x,y),z) b)) _).
 unfold literal_table_flat;cbn [fst snd Nat.pred].
 let rec pair_routes := lazymatch goal with
 | |- fst (literal_table_advance ?k ?a ?b)=_=>exact (@surjective_pairing _ _ (fst (literal_table_advance k a b)))
 | |- literal_table_ratio _ _ _=literal_table_ratio _ _ _=>reflexivity
 | |- (?a,?b)=(?c,?d)=>apply f_equal2;[pair_routes|pair_routes]
 | |- _=>reflexivity
 end in pair_routes.
Qed.
Lemma literal_pass1_8_z a b : snd (@literal_pass1_8 Alg.CoreFunSem (a,b))=snd (literal_table_advance 7 a b).
Proof.
 pose proof (literal_pass1_8_step a b) as Shape.
 remember (@literal_pass1_8 Alg.CoreFunSem (a,b)) as result eqn:Result in *.
 destruct result as [tree z];cbn [snd] in *;injection Shape as Tree Z;exact Z.
Qed.

Theorem table_prefix_tree_literal s a b : table_prefix_literal 8 s a b ->
 table_state_tree s=literal_table_normalize_tree 3 (fst (@literal_pass1_8 Alg.CoreFunSem (a,b))).
Proof.
 intro Prefix;rewrite literal_pass1_8_flat;unfold literal_table_normalize_tree;rewrite literal_table_map_flat.
 apply literal_table_flat_congr.
 - intros k Bound;apply mixed_xy_output_normalize;exact (proj1 (Prefix k Bound)).
 - intros k Bound;apply mixed_xy_output_normalize;exact (proj1 (proj2 (Prefix k Bound))).
 - intros k [Positive Bound];apply mixed_xy_output_normalize;exact (proj2 (proj2 (Prefix k Bound)) Positive).
Qed.

Theorem exec_odd_table_pass1_eight e le m br ba bg bz s u v a b :
 NoDup [br;ba;bg;bz] -> e!_ai=Some (ba,Tstruct __6123 noattr) -> e!_d_ge=Some (bg,curve_ge_type) ->
 e!_secp256k1_gej_add_ge_var=None -> e!_secp256k1_ge_set_xy=None ->
 le!_pre_a=Some (Vptr br Ptrofs.zero) -> le!_zr=Some (Vptr bz Ptrofs.zero) ->
 le!_i=Some (Vint Int.one) -> le!_n=Some (Vint (Int.repr 8)) ->
 odd_table_prefix m br bz 1 s -> odd_table_prefix_bounds 1 s ->
 odd_table_accumulator m ba s -> odd_table_accumulator_bounds s ->
 square_input_bounds u -> square_input_bounds v ->
 fe_at m bg 0 (words5 u) -> fe_at m bg 40 (words5 v) -> Mem.load Mint32 m bg 80=Some (Vint Int.zero) ->
 Mem.range_perm m br 0 704 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable ->
 Mem.range_perm m bg 0 88 Cur Freeable -> Mem.range_perm m bz 0 320 Cur Freeable ->
 table_acc_literal s a -> table_prefix_literal 1 s a b -> table_word_literal u (fst b) -> table_word_literal v (snd b) ->
 let sf:=odd_table_walk 7 1 s u v in exists lef mf,
 Clight2.exec_stmt secp_ge e le m odd_table_loop E0 lef mf Out_normal /\
 table_state_tree sf=literal_table_normalize_tree 3 (fst (@literal_pass1_8 Alg.CoreFunSem (a,b))) /\
 rescale_field_output (odd_table_z sf)=@canonical_fe_normalize Alg.CoreFunSem (snd (@literal_pass1_8 Alg.CoreFunSem (a,b))) /\
 odd_table_prefix mf br bz 8 sf /\ odd_table_prefix_bounds 8 sf /\
 odd_table_accumulator mf ba sf /\ odd_table_accumulator_bounds sf /\
 fe_at mf bg 0 (words5 u) /\ fe_at mf bg 40 (words5 v) /\ Mem.load Mint32 mf bg 80=Some (Vint Int.zero) /\
 lef!_i=Some (Vint (Int.repr 8)) /\ (forall id,id<>_i -> lef!id=le!id) /\
 Mem.range_perm mf br 0 704 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 Mem.range_perm mf bg 0 88 Cur Freeable /\ Mem.range_perm mf bz 0 320 Cur Freeable /\
 keeps_permissions m mf /\ lframe (odd_table_loop_frame br ba bg bz) m mf /\ readonly_preserved m mf.
Proof.
 intros Distinct AI DG AddGlobal WriteGlobal Table Ratios IndexTemp Length Prefix PrefixBounds Acc Bounds BU BV U V Flag
  FreeT FreeA FreeG FreeR AccLiteral PrefixLiteral UL VL;cbv zeta.
 remember (odd_table_walk 7 1 s u v) as sf eqn:Walk.
 destruct (odd_table_walk_literal 7 1 ltac:(lia) ltac:(lia) e le m br ba bg bz s u v a b
   Distinct AI DG AddGlobal WriteGlobal Table Ratios IndexTemp Acc Bounds BU BV U V Flag
   FreeT FreeA FreeG FreeR AccLiteral PrefixLiteral UL VL) as [FinalAcc FinalPrefix].
 rewrite <-Walk in FinalAcc,FinalPrefix.
 pose proof (table_prefix_tree_literal _ a b FinalPrefix) as Tree.
 assert (ZLiteral:rescale_field_output (odd_table_z sf)=
   @canonical_fe_normalize Alg.CoreFunSem (snd (@literal_pass1_8 Alg.CoreFunSem (a,b)))).
 { rewrite literal_pass1_8_z;apply mixed_xy_output_normalize;exact (proj1 (proj2 (proj2 FinalAcc))). }
 destruct (exec_odd_table_loop 7 1 ltac:(lia) eq_refl e le m br ba bg bz s u v
   Distinct AI DG AddGlobal WriteGlobal Table Ratios IndexTemp Length Prefix PrefixBounds Acc Bounds BU BV U V Flag
   FreeT FreeA FreeG FreeR)
  as (lef & mf & Run & IndexF & Others & PrefixF & PrefixBoundsF & AccF & BoundsF & UF & VF & FlagF &
    FreeTF & FreeAF & FreeGF & FreeRF & Keep & Frame & Readonly).
 rewrite <-Walk in PrefixF,PrefixBoundsF,AccF,BoundsF.
 exists lef,mf;repeat (first [assumption|split]).
Qed.
