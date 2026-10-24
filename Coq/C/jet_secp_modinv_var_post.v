(** Compose the actual inverse caller's zero-test and shortening control. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem C.jet_sx_u64_transport.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix C.jet_secp_modinv_var_entry.
Require Import C.jet_secp_modinv_var_zero C.jet_secp_modinv_var_shorten C.jet_secp_fe_nv C.jet_secp_local_regions.
Require Import C.jet_secp_u128_shift64_rep C.jet_secp_modinv_normalize62_words.
Require Import C.jet_secp_modinfo_fe_global C.jet_secp_modinv_var_copies C.jet_secp_multiply_normalize_bridge.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition inv_post_control := Ssequence inv_zero_test inv_shortening.
Definition inv_control_stops len rho := inv_g_is_zero len (inv_control_word rho true).
Definition inv_post_out len rho := if inv_control_stops len rho then Out_break else Out_normal.
Definition inv_post_regs len rho := if inv_control_stops len rho then inv_control_regs else inv_shortened_regs len rho.
Definition inv_post_length len rho := if inv_control_stops len rho then len else inv_shortened_length len rho.
Definition inv_post_word len rho high i := if inv_control_stops len rho
 then inv_control_word rho high i else inv_control_short_word len rho high i.
Definition inv_post_modified := inv_test_modified++inv_shorten_modified.
Definition inv_post_temp_frame (le lf : temp_env) := forall id,~In id inv_post_modified -> lf!id=le!id.
Lemma inv_post_source : inv_caller_loop_body=
 statement_sequence (firstn 4 (fst inv_caller_loop_parts)) inv_post_control.
Proof. exact inv_caller_control_source. Qed.
Lemma inv_post_out_value len rho : (0<len)%nat -> inv_active_low_bounds len (inv_control_word rho true) ->
 inv_post_out len rho=Out_break <-> inv_active_value len (inv_control_word rho true)=0.
Proof. intros Len Bounds;apply inv_zero_out_value;assumption. Qed.
Lemma inv_control_temps_from_length rho beta len le : le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 tmatch rho beta (inv_control_temps len) le.
Proof.
 intros Len id x Get;unfold inv_control_temps in Get;rewrite PTree.gsspec in Get.
 destruct (peq id _len) as [->|Ne];[injection Get as <-;exact Len|rewrite PTree.gempty in Get;discriminate].
Qed.
Lemma inv_post_test_frame le lf : inv_test_frame le lf -> inv_post_temp_frame le lf.
Proof.
 intros Frame id Outside;apply Frame;intro H;apply Outside;apply in_or_app;left;exact H.
Qed.
Lemma inv_post_frames le lm lf : inv_test_frame le lm -> inv_shorten_temp_frame lm lf -> inv_post_temp_frame le lf.
Proof.
 intros A B id Outside;rewrite (B id), (A id);try reflexivity;
  intro H;apply Outside;apply in_or_app;auto.
Qed.

Theorem exec_inv_post_control len rho beta e le m : (0<len<=5)%nat ->
 rep rho beta inv_control_regs m -> tmatch rho beta (inv_control_temps len) le ->
 ematch beta (snd inv_start_alloc) e -> exists lef mf,
 Clight2.exec_stmt secp_ge e le m inv_post_control E0 lef mf (inv_post_out len rho) /\
 rep rho beta (inv_post_regs len rho) mf /\
 lef!_len=Some (Vint (Int.repr (Z.of_nat (inv_post_length len rho)))) /\
 (0<inv_post_length len rho<=5)%nat /\ inv_post_temp_frame le lef /\
 lframe (fun b _=>b<>blk beta 4 /\ b<>blk beta 5) m mf.
Proof.
 intros Len Rep Temps Env;destruct (exec_inv_zero_test len rho beta e le m Len Rep Temps Env)
  as (lz & Zero & ZFrame & ZLen).
 change (Clight2.exec_stmt secp_ge e le m inv_zero_test E0 lz m (inv_post_out len rho)) in Zero.
 unfold inv_post_out in Zero|-*;unfold inv_post_regs,inv_post_length;destruct (inv_control_stops len rho) eqn:Stops.
 - exists lz,m;split.
   + unfold inv_post_control;eapply exec_Sseq_2;[exact Zero|discriminate].
   + split;[exact Rep|];split;[exact ZLen|];split;[exact Len|];split;
      [apply inv_post_test_frame;exact ZFrame|apply lframe_refl].
 - destruct (exec_inv_shortening len rho beta e lz m Len Rep
    (inv_control_temps_from_length rho beta len lz ZLen) Env)
    as (lef & mf & Short & Out & Length & Range & SFrame & MFrame).
   exists lef,mf;split.
   + unfold inv_post_control;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lz) (m1:=m);eassumption.
   + split;[exact Out|];split;[exact Length|];split;[exact Range|];split;
      [eapply inv_post_frames;eassumption|exact MFrame].
Qed.

Lemma inv_post_loads len rho beta m : (0<len<=5)%nat -> rep rho beta (inv_post_regs len rho) m ->
 forall high i,(i<5)%nat -> Mem.load Mint64 m (blk beta (inv_shorten_region high))
 (bas beta (inv_shorten_region high)+8*Z.of_nat i)=Some (Vlong (inv_post_word len rho high i)).
Proof.
 intros Len Rep high i I;unfold inv_post_regs in Rep;unfold inv_post_word;destruct (inv_control_stops len rho).
 - exact (xload_u64_defined_sound rho beta _ m _ _ _ Rep (inv_control_word_load high i I)).
 - apply inv_shortened_loads;assumption.
Qed.
Lemma inv_post_numeric len rho high : (0<len<=5)%nat -> inv_active_low_bounds len (inv_control_word rho high) ->
 inv_active_value (inv_post_length len rho) (inv_post_word len rho high)=
 inv_active_value len (inv_control_word rho high) /\
 inv_active_low_bounds (inv_post_length len rho) (inv_post_word len rho high).
Proof.
 intros Len Low;unfold inv_post_length,inv_post_word;destruct (inv_control_stops len rho);
  [split;[reflexivity|exact Low]|apply inv_shortened_numeric;assumption].
Qed.

Corollary exec_inv_post_control_numeric len rho beta e le m : (0<len<=5)%nat ->
 rep rho beta inv_control_regs m -> tmatch rho beta (inv_control_temps len) le ->
 ematch beta (snd inv_start_alloc) e ->
 (forall high,inv_active_low_bounds len (inv_control_word rho high)) -> exists lef mf out,
 Clight2.exec_stmt secp_ge e le m inv_post_control E0 lef mf out /\
 (out=Out_break <-> inv_active_value len (inv_control_word rho true)=0) /\
 (out=Out_break \/ out=Out_normal) /\
 rep rho beta (inv_post_regs len rho) mf /\
 (forall high i,(i<5)%nat -> Mem.load Mint64 mf (blk beta (inv_shorten_region high))
  (bas beta (inv_shorten_region high)+8*Z.of_nat i)=Some (Vlong (inv_post_word len rho high i))) /\
 (forall high,inv_active_value (inv_post_length len rho) (inv_post_word len rho high)=
  inv_active_value len (inv_control_word rho high) /\
  inv_active_low_bounds (inv_post_length len rho) (inv_post_word len rho high)) /\
 lef!_len=Some (Vint (Int.repr (Z.of_nat (inv_post_length len rho)))) /\
 (0<inv_post_length len rho<=5)%nat /\ inv_post_temp_frame le lef /\
 lframe (fun b _=>b<>blk beta 4 /\ b<>blk beta 5) m mf.
Proof.
 intros Len Rep Temps Env Bounds;destruct (exec_inv_post_control len rho beta e le m Len Rep Temps Env)
  as (lef & mf & Exec & Out & Length & Range & Frame & MFrame).
 exists lef,mf,(inv_post_out len rho);split;[exact Exec|];split.
 - apply inv_post_out_value;[lia|apply Bounds].
 - split;[unfold inv_post_out;destruct (inv_control_stops len rho);auto|];split;[exact Out|];split.
   + apply inv_post_loads;assumption.
   + split;[intro high;apply inv_post_numeric;[exact Len|apply Bounds]|].
     split;[exact Length|];split;[exact Range|];split;assumption.
Qed.

Definition inv_post_next_rho len (rho : nat->int64) n := match n with
 | 5%nat=>inv_post_word len rho false 0 | 6%nat=>inv_post_word len rho false 1
 | 7%nat=>inv_post_word len rho false 2 | 8%nat=>inv_post_word len rho false 3
 | 9%nat=>inv_post_word len rho false 4 | 10%nat=>inv_post_word len rho true 0
 | 11%nat=>inv_post_word len rho true 1 | 12%nat=>inv_post_word len rho true 2
 | 13%nat=>inv_post_word len rho true 3 | 14%nat=>inv_post_word len rho true 4
 | _=>rho n end.
Lemma inv_post_next_word len rho high i : (i<5)%nat ->
 inv_control_word (inv_post_next_rho len rho) high i=inv_post_word len rho high i.
Proof. destruct high;destruct i as [|[|[|[|[|i]]]]];intro I;try lia;reflexivity. Qed.
Lemma inv_post_regs_metadata len rho high : (0<len<=5)%nat ->
 length (inv_post_regs len rho)=7%nat /\
 rfree (nth (inv_shorten_region high) (inv_post_regs len rho) (mkreg [] true None))=Some 40.
Proof.
 intro Len;unfold inv_post_regs,inv_shortened_regs;destruct (inv_control_stops len rho);
  [destruct high;split;reflexivity|].
 destruct (inv_control_shrink len rho);[|destruct high;split;reflexivity].
 destruct high;destruct len as [|[|[|[|[|[|len]]]]]];try lia;split;reflexivity.
Qed.
Lemma inv_post_regs_shapes len rho : (0<len<=5)%nat ->
 map rshape (inv_post_regs len rho)=map rshape inv_control_regs.
Proof.
 intro Len;unfold inv_post_regs,inv_shortened_regs;destruct (inv_control_stops len rho);[reflexivity|].
 destruct (inv_control_shrink len rho);[|reflexivity].
 destruct len as [|[|[|[|[|[|len]]]]]];try lia;reflexivity.
Qed.
Lemma inv_post_untouched len rho r : (0<len<=5)%nat -> (r<7)%nat -> r<>4%nat -> r<>5%nat ->
 nth_error (inv_post_regs len rho) r=nth_error inv_control_regs r.
Proof.
 intros Len R N4 N5;unfold inv_post_regs,inv_shortened_regs;destruct (inv_control_stops len rho);[reflexivity|].
 destruct (inv_control_shrink len rho);[|reflexivity].
 destruct len as [|[|[|[|[|[|len]]]]]];try lia;
  destruct r as [|[|[|[|[|[|[|r]]]]]]];try lia;reflexivity.
Qed.

Lemma inv_region_rho_ext rho rho' beta m r reg :
 (forall c x,In c (rcells reg) -> cval c=Some x -> den rho' (lay beta) x=den rho (lay beta) x) ->
 region_ok rho beta m r reg -> region_ok rho' beta m r reg.
Proof.
 intros Same (B & V & S & Cells & Owned);split;[exact B|];split;[exact V|];split;[exact S|];split;[|exact Owned].
 apply Forall_forall;intros c Member;destruct (proj1 (Forall_forall _ _) Cells c Member) as (Max & Align & Perm & Value).
 split;[exact Max|];split;[exact Align|];split;[exact Perm|].
 intros x At;rewrite (Same c x Member At);apply Value;exact At.
Qed.
Lemma inv_region_undefined rho rho' beta m r reg : Forall (fun c=>cval c=None) (rcells reg) ->
 region_ok rho beta m r reg -> region_ok rho' beta m r reg.
Proof.
 intros Empty Region;eapply inv_region_rho_ext;[|exact Region].
 intros c x Member At;rewrite (proj1 (Forall_forall _ _) Empty c Member) in At;discriminate.
Qed.

Lemma inv_post_revalue_array len rho beta m high : (0<len<=5)%nat -> rep rho beta (inv_post_regs len rho) m ->
 region_ok (inv_post_next_rho len rho) beta m (inv_shorten_region high)
  (mkreg (u64_cells 0 (vars5 (inv_shorten_offset high))) true (Some 40)).
Proof.
 intros Len Rep;destruct (inv_post_regs_metadata len rho high Len) as (Size & Owned).
 destruct (rep_free_region rho beta _ m (inv_shorten_region high) 40 Rep
  ltac:(rewrite Size;destruct high;cbn [inv_shorten_region];lia) Owned) as (Base & Free).
 pose proof (inv_post_loads len rho beta m Len Rep high) as Loads;rewrite Base in Loads.
 assert (Storage : fe_at m (blk beta (inv_shorten_region high)) 0 (words5 (inv_post_word len rho high))).
 { split;[lia|];split;[exists 0;reflexivity|];split;
    [change (40<=18446744073709551615);lia|];split;[apply freeable_range_writable;exact Free|].
   intros i x At;assert (I : (i<5)%nat).
   { change (i<length (words5 (inv_post_word len rho high)))%nat;apply nth_error_Some;rewrite At;discriminate. }
   destruct i as [|[|[|[|[|i]]]]];try lia;injection At as <-;apply Loads;lia. }
 apply (inv_copy_region (inv_post_next_rho len rho) beta m (inv_shorten_region high)
  (vars5 (inv_shorten_offset high)) (inv_post_word len rho high)).
 - exact Base.
 - destruct high;reflexivity.
 - intros i x At;destruct high;destruct i as [|[|[|[|[|i]]]]];
    cbn [inv_shorten_offset vars5 nth_error] in At;try (destruct i;discriminate At);
    injection At as <-;split;reflexivity.
 - exact Storage.
 - exact Free.
Qed.

Lemma inv_post_revalue_other len rho beta m r reg : (r<7)%nat -> r<>4%nat -> r<>5%nat ->
 nth_error inv_control_regs r=Some reg -> region_ok rho beta m r reg ->
 region_ok (inv_post_next_rho len rho) beta m r reg.
Proof.
 intros R N4 N5 At Region;destruct r as [|[|[|[|[|[|[|r]]]]]]];try lia;
  cbn [inv_control_regs upd nth_error] in At;injection At as <-.
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=0%nat)
    (xs:=vars5 0) (ys:=vars5 0);try reflexivity;exact Region.
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=1%nat)
    (xs:=map XLc modinfo_fe_words) (ys:=map XLc modinfo_fe_words);try reflexivity;exact Region.
 - eapply inv_region_undefined;[repeat constructor|exact Region].
 - eapply inv_region_undefined;[repeat constructor|exact Region].
 - eapply inv_region_undefined;[repeat constructor|exact Region].
Qed.

Theorem inv_post_revalue len rho beta m : (0<len<=5)%nat -> rep rho beta (inv_post_regs len rho) m ->
 rep (inv_post_next_rho len rho) beta inv_control_regs m.
Proof.
 intros Len Rep;pose proof Rep as (Size & Sep & Regions);split.
 - rewrite (proj1 (inv_post_regs_metadata len rho false Len)) in Size;exact Size.
 - split.
   + eapply (rsep_shape beta (inv_post_regs len rho));[symmetry;apply inv_post_regs_shapes;exact Len|exact Sep].
   + intros r reg At;assert (R : (r<7)%nat).
     { change (r<length inv_control_regs)%nat;apply nth_error_Some;rewrite At;discriminate. }
     destruct (Nat.eq_dec r 4) as [->|N4];[cbn [inv_control_regs upd nth_error] in At;injection At as <-;
      exact (inv_post_revalue_array len rho beta m false Len Rep)|].
     destruct (Nat.eq_dec r 5) as [->|N5];[cbn [inv_control_regs upd nth_error] in At;injection At as <-;
      exact (inv_post_revalue_array len rho beta m true Len Rep)|].
     apply (inv_post_revalue_other len rho beta m r reg R N4 N5 At).
     apply Regions;rewrite inv_post_untouched by assumption;exact At.
Qed.

Lemma inv_post_next_value len rho high : (0<inv_post_length len rho<=5)%nat ->
 inv_active_value (inv_post_length len rho) (inv_control_word (inv_post_next_rho len rho) high)=
 inv_active_value (inv_post_length len rho) (inv_post_word len rho high).
Proof.
 intro Len;unfold inv_active_value;apply norm62_value_ext;intros i I.
 rewrite inv_post_next_word by lia;reflexivity.
Qed.
Lemma inv_post_next_bounds len rho high : (0<inv_post_length len rho<=5)%nat ->
 inv_active_low_bounds (inv_post_length len rho) (inv_post_word len rho high) ->
 inv_active_low_bounds (inv_post_length len rho) (inv_control_word (inv_post_next_rho len rho) high).
Proof. intros Len Bounds i I;rewrite inv_post_next_word by lia;apply Bounds;exact I. Qed.
Lemma inv_post_next_outside len rho n : ((n<5)%nat \/ (15<=n)%nat) -> inv_post_next_rho len rho n=rho n.
Proof. intro Outside;do 15 (destruct n as [|n];[try reflexivity;lia|]);reflexivity. Qed.

(** The next iteration receives the same owned layout, not a presumed
    post-state. This closes only the caller's post-transition control, not
    the preceding divstep/update calls or the complete inverse loop. *)
Theorem exec_inv_post_ready len rho beta e le m : (0<len<=5)%nat ->
 rep rho beta inv_control_regs m -> tmatch rho beta (inv_control_temps len) le ->
 ematch beta (snd inv_start_alloc) e ->
 (forall high,inv_active_low_bounds len (inv_control_word rho high)) -> exists lef mf out,
 Clight2.exec_stmt secp_ge e le m inv_post_control E0 lef mf out /\
 rep (inv_post_next_rho len rho) beta inv_control_regs mf /\
 tmatch (inv_post_next_rho len rho) beta (inv_control_temps (inv_post_length len rho)) lef /\
 (forall high,
  inv_active_value (inv_post_length len rho) (inv_control_word (inv_post_next_rho len rho) high)=
   inv_active_value len (inv_control_word rho high) /\
  inv_active_low_bounds (inv_post_length len rho) (inv_control_word (inv_post_next_rho len rho) high)) /\
 (out=Out_break <-> inv_active_value (inv_post_length len rho) (inv_control_word (inv_post_next_rho len rho) true)=0) /\
 (out=Out_normal -> inv_active_value (inv_post_length len rho) (inv_control_word (inv_post_next_rho len rho) true)<>0) /\
 (out=Out_break \/ out=Out_normal) /\ (0<inv_post_length len rho<=5)%nat /\
 inv_post_temp_frame le lef /\ lframe (fun b _=>b<>blk beta 4 /\ b<>blk beta 5) m mf.
Proof.
 intros Len Rep Temps Env Bounds;destruct (exec_inv_post_control_numeric len rho beta e le m Len Rep Temps Env Bounds)
  as (lef & mf & out & Exec & Stop & Outcomes & Out & Loads & Values & Length & Range & Frame & MFrame).
 assert (NextValues : forall high,
  inv_active_value (inv_post_length len rho) (inv_control_word (inv_post_next_rho len rho) high)=
    inv_active_value len (inv_control_word rho high) /\
  inv_active_low_bounds (inv_post_length len rho) (inv_control_word (inv_post_next_rho len rho) high)).
 { intro high;split.
   - rewrite inv_post_next_value by exact Range;exact (proj1 (Values high)).
   - apply inv_post_next_bounds;[exact Range|exact (proj2 (Values high))]. }
 assert (NextStop : out=Out_break <->
  inv_active_value (inv_post_length len rho) (inv_control_word (inv_post_next_rho len rho) true)=0).
 { rewrite (proj1 (NextValues true));exact Stop. }
 exists lef,mf,out;split;[exact Exec|];split;[apply inv_post_revalue;assumption|];split.
 - apply inv_control_temps_from_length;exact Length.
 - split;[exact NextValues|];split;[exact NextStop|];split.
   + intros Normal Zero;apply (proj2 NextStop) in Zero;congruence.
   + split;[exact Outcomes|];split;[exact Range|];split;assumption.
Qed.
