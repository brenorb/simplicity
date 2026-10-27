(** The original descending global-Z call against the fixed balanced pass2_8
    program. Field decoding accounts for its first skip and weak final Y. *)
From Coq Require Import ZArith List Lia FunctionalExtensionality.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_toZ C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_globalz_word_walk C.jet_secp_globalz_loop C.jet_secp_globalz_function
 C.jet_secp_globalz_factor_call C.jet_secp_ge_zinv_arithmetic
 C.jet_secp_scalar_table_pass2 C.jet_secp_scalar_table_literal C.jet_secp_odd_table_pass1_bridge
 C.jet_secp_table_field_equiv C.jet_secp_rescale_literal C.jet_secp_fe_math
 C.jet_secp_negate_literal_contract C.jet_secp_canonical_normalize C.jet_secp_literal_add_program
 C.jet_secp_literal_add_numeric C.jet_secp_multiply_literal_spec C.jet_secp_square_execution
 C.jet_secp_multiply_checkpoint_columns C.jet_secp_field_weak_loose
 C.jet_secp_square_columns C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_fe_multiply literal_fe_square literal_fe_cube literal_gej_zinv
 literal_fe_one256 canonical_fe_normalize rescale_field_output weak_loose_words.

Definition globalz_word_vector (ps:nat->Ty.tySem literal_table_ge) : Ty.tySem (literal_table_vector 3) :=
 (((ps 0,ps 1),(ps 2,ps 3)),((ps 4,ps 5),(ps 6,ps 7)))%nat.
Definition globalz_word_canonical (w:Ty.tySem (Word 8)) := @toZ (WordToZ 8) w mod feP=@toZ (WordToZ 8) w.
Lemma globalz_decoded_canonical w : globalz_word_canonical (rescale_field_output w).
Proof.
 unfold globalz_word_canonical;rewrite rescale_field_output_value,Z.mod_mod by (unfold feP,feR;discriminate);reflexivity.
Qed.

Lemma globalz_one_canonical : globalz_word_canonical (@literal_fe_one256 Alg.CoreFunSem tt).
Proof. unfold globalz_word_canonical;rewrite literal_fe_one256_value;apply Z.mod_small;unfold feP,feR;lia. Qed.
Lemma globalz_multiply_one w : globalz_word_canonical w ->
 @literal_fe_multiply Alg.CoreFunSem (w,@literal_fe_one256 Alg.CoreFunSem tt)=w.
Proof.
 intro Canonical;apply (toZ_injective (WordToZ 8));rewrite literal_multiply_numeric,literal_fe_one256_value,Z.mul_1_r;exact Canonical.
Qed.
Lemma globalz_zinv_one (p:Ty.tySem literal_table_ge) :
 globalz_word_canonical (fst p) -> globalz_word_canonical (snd p) ->
 @literal_gej_zinv Alg.CoreFunSem (p,@literal_fe_one256 Alg.CoreFunSem tt)=p.
Proof.
 intros X Y.
 assert (Square:@literal_fe_square Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)=
  @literal_fe_one256 Alg.CoreFunSem tt).
 { rewrite literal_square_step;apply globalz_multiply_one;exact globalz_one_canonical. }
 assert (Cube:@literal_fe_cube Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)=
  @literal_fe_one256 Alg.CoreFunSem tt).
 { rewrite table_cube_step,Square;apply globalz_multiply_one;exact globalz_one_canonical. }
 rewrite table_zinv_step,Square,Cube,!globalz_multiply_one by assumption.
 symmetry;apply surjective_pairing.
Qed.

(** Only the last ratio and the unchanged last point need canonical values.
    These premises follow from decoding C fields; other words are unrestricted. *)
Theorem globalz_word_walk_pass2 (ps:nat->Ty.tySem literal_table_ge) (rs:nat->Ty.tySem (Word 8)) :
 globalz_word_canonical (rs 7%nat) ->
 globalz_word_canonical (fst (ps 7%nat)) -> globalz_word_canonical (snd (ps 7%nat)) ->
 globalz_word_vector (fst (globalz_word_walk 7 ps rs (rs 7%nat)))=
 @literal_pass2_8 Alg.CoreFunSem
  (literal_table_flat (fun j=>fst (ps j)) (fun j=>snd (ps j)) rs).
Proof.
 intros R X Y.
 unfold literal_table_flat.
 rewrite literal_pass2_8_step;cbv zeta.
 rewrite !literal_pass2_4_step;cbv zeta.
 rewrite !literal_pass2_2_step;cbn [fst snd].
 rewrite (globalz_multiply_one (rs 7%nat) R).
 unfold globalz_word_vector.
 cbv [globalz_word_walk globalz_word_replace Nat.eqb Nat.eq_dec nat_rec nat_rect fst snd].
 let rec point_eta := lazymatch goal with
 | |- ps 7%nat=_=>symmetry;
   exact (eq_trans (globalz_zinv_one (fst (ps 7%nat),snd (ps 7%nat)) X Y)
    (eq_sym (@surjective_pairing _ _ (ps 7%nat))))
 | |- @literal_gej_zinv _ (?p,?s)=@literal_gej_zinv _ ((fst ?p,snd ?p),?s)=>
   exact (f_equal (fun q:Ty.tySem literal_table_ge=>@literal_gej_zinv Alg.CoreFunSem (q,s))
    (@surjective_pairing _ _ p))
 | |- (?a,?b)=(?c,?d)=>apply f_equal2;[point_eta|point_eta]
 | |- ?p=(fst ?p,snd ?p)=>apply surjective_pairing
 | |- _=>reflexivity end in point_eta.
Qed.

Lemma globalz_word_vector_congr ps qs : (forall k,(k<8)%nat -> ps k=qs k) ->
 globalz_word_vector ps=globalz_word_vector qs.
Proof.
 intro Points;unfold globalz_word_vector.
 let rec entries := lazymatch goal with
 | |- ps ?k=_=>exact (Points k ltac:(repeat constructor))
 | |- (?a,?b)=(?c,?d)=>apply f_equal2;[entries|entries] end in entries.
Qed.

Lemma globalz_start_decoded xs ys : globalz_table_bounds xs ys -> forall k,
 globalz_decoded_points xs (globalz_start_ys ys) k=globalz_decoded_points xs ys k.
Proof.
 intros Bounds k;unfold globalz_decoded_points,globalz_start_ys,globalz_replace.
 destruct (Nat.eq_dec k 7) as [->|Different];[|reflexivity].
 apply f_equal2;[reflexivity|];apply (toZ_injective (WordToZ 8));rewrite !rescale_field_output_value.
 exact (proj1 (weak_loose_numeric (ys 7%nat)
  (rescale_writer_bounds _ (proj2 (Bounds 7%nat ltac:(lia)))))).
Qed.
Lemma globalz_start_bounds xs ys : globalz_table_bounds xs ys ->
 globalz_table_bounds xs (globalz_start_ys ys).
Proof.
 intros Bounds k Range;split;[exact (proj1 (Bounds k Range))|].
 unfold globalz_start_ys,globalz_replace;destruct (Nat.eq_dec k 7) as [->|Different];
 [|exact (proj2 (Bounds k Range))].
 pose proof (proj2 (weak_loose_numeric (ys 7%nat)
  (rescale_writer_bounds _ (proj2 (Bounds 7%nat ltac:(lia)))))) as Tight.
 intros i Bound;specialize (Tight i Bound);destruct (Nat.eqb i 4);lia.
Qed.

Theorem globalz_eight_pass2 xs ys ratios : globalz_table_bounds xs ys -> globalz_ratios_bounds ratios ->
 let '((xf,yf),_):=globalz_walk 7 xs (globalz_start_ys ys) ratios (ratios 7%nat) in
 globalz_word_vector (globalz_decoded_points xf yf)=
 @literal_pass2_8 Alg.CoreFunSem
  (literal_table_flat (fun j=>rescale_field_output (xs j))
   (fun j=>rescale_field_output (ys j)) (fun j=>rescale_field_output (ratios j))).
Proof.
 intros Bounds Ratios.
 pose proof (globalz_walk_decoded 7 ltac:(lia) xs (globalz_start_ys ys) ratios (ratios 7%nat)
  (globalz_decoded_points xs ys) (fun j=>rescale_field_output (ratios j))
  (rescale_field_output (ratios 7%nat)) (globalz_start_bounds xs ys Bounds) Ratios
  (Ratios 7%nat ltac:(lia)) ltac:(intros;apply globalz_start_decoded;exact Bounds)
  ltac:(intros;reflexivity) eq_refl) as Decoded.
 pose proof (globalz_word_walk_pass2 (globalz_decoded_points xs ys)
  (fun j=>rescale_field_output (ratios j)) (globalz_decoded_canonical _)
  (globalz_decoded_canonical _) (globalz_decoded_canonical _)) as Balanced.
 destruct (globalz_walk 7 xs (globalz_start_ys ys) ratios (ratios 7%nat)) as [[xf yf] zf].
 destruct (globalz_word_walk 7 (globalz_decoded_points xs ys) (fun j=>rescale_field_output (ratios j))
  (rescale_field_output (ratios 7%nat))) as [pf sf].
 destruct Decoded as [Points Scale];cbn [fst] in Balanced.
 refine (eq_trans (globalz_word_vector_congr _ _ Points) Balanced).
Qed.

(** Actual function entry, allocations, seven iterations and frees are all
    supplied by the existing whole-call proof, now with the literal result. *)
Theorem eval_ge_table_set_globalz_pass2 xs ys ratios m br bz : br<>bz ->
 globalz_table_bounds xs ys -> globalz_ratios_bounds ratios ->
 globalz_table_rep m br xs ys -> globalz_ratios_rep m bz ratios ->
 Mem.range_perm m br 0 704 Cur Freeable -> Mem.range_perm m bz 0 320 Cur Freeable ->
 let '((xf,yf),_):=globalz_walk 7 xs (globalz_start_ys ys) ratios (ratios 7%nat) in exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_table_set_globalz)
  [Vlong (Int64.repr 8);Vptr br Ptrofs.zero;Vptr bz Ptrofs.zero] E0 mf Vundef /\
 globalz_word_vector (globalz_decoded_points xf yf)=
  @literal_pass2_8 Alg.CoreFunSem
   (literal_table_flat (fun j=>rescale_field_output (xs j))
    (fun j=>rescale_field_output (ys j)) (fun j=>rescale_field_output (ratios j))) /\
 globalz_table_rep mf br xf yf /\ globalz_ratios_rep mf bz ratios /\ globalz_table_bounds xf yf /\
 Mem.range_perm mf br 0 704 Cur Freeable /\ Mem.range_perm mf bz 0 320 Cur Freeable /\
 keeps_permissions m mf /\ lframe (fun b _=>b<>br /\ b<>bz) m mf /\ readonly_preserved m mf.
Proof.
 intros Separate Bounds RatioBounds Table Ratios FreeA FreeR.
 pose proof (eval_ge_table_set_globalz_eight xs ys ratios m br bz
  Separate Bounds RatioBounds Table Ratios FreeA FreeR) as Call.
 pose proof (globalz_eight_pass2 xs ys ratios Bounds RatioBounds) as Literal.
 destruct (globalz_walk 7 xs (globalz_start_ys ys) ratios (ratios 7%nat)) as [[xf yf] zf].
 destruct Call as (mf & Run & Rest);exists mf;split;[exact Run|];split;assumption.
Qed.
