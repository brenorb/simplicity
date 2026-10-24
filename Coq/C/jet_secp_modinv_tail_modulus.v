(** Restore the complete inverse caller after the real stopping/shortening
    control, retaining arbitrary six-word modulus metadata and ownership. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem
 C.jet_sx_u64_transport C.jet_sx_region_lframe C.jet_secp_linkage C.jets_secp
 C.jet_secp_modinv_loop_modulus C.jet_secp_modinv_entry_modulus C.jet_secp_modinv_control_storage
 C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_zero C.jet_secp_modinv_var_shorten
 C.jet_secp_modinv_var_post C.jet_secp_modinv_var_tail C.jet_secp_modinv_var_de C.jet_secp_modinv_var_fg
 C.jet_secp_modinv_var_copies C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge C.jet_secp_local_regions
 C.jet_secp_u128_shift64_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma inv_mod_tail_load_expr mu (high : bool) i : (i<5)%nat ->
 xload (inv_mod_loop_regs mu) (if high then 5 else 4) (8*Z.of_nat i) tulong=
 Some(XLv((if high then 20 else 15)+i)%nat).
Proof. destruct high;destruct i as [|[|[|[|[|i]]]]];intro I;try lia;reflexivity. Qed.

Lemma inv_mod_tail_array len mu rho beta m mf (high : bool) :
 rep rho beta (inv_mod_loop_regs mu) m -> Mem.range_perm mf (blk beta (if high then 5 else 4)) 0 40 Cur Freeable ->
 (forall i,(i<5)%nat -> Mem.load Mint64 mf (blk beta (if high then 5 else 4)) (8*Z.of_nat i)=
  Some(Vlong(inv_post_word len (inv_control_view rho) high i))) ->
 region_ok (inv_tail_next_rho len rho) beta mf (if high then 5 else 4)
  (nth (if high then 5 else 4) (inv_mod_loop_regs mu) (mkreg [] false None)).
Proof.
 intros Rep Free Loads.
 assert(Base:bas beta (if high then 5 else 4)=0)
  by(apply(inv_mod_owned_base mu rho beta m _ Rep);destruct high;lia).
 assert(Field:fe_at mf (blk beta (if high then 5 else 4)) 0
  (words5(fun i=>inv_post_word len (inv_control_view rho) high i))).
 { split;[lia|];split;[exists 0;reflexivity|];split;[change(40<=18446744073709551615);lia|];split.
   - intros pos Range;eapply Mem.perm_implies;[apply Free;exact Range|constructor].
   - intros i v At;assert(I:(i<5)%nat) by(change(i<length(words5(fun i=>inv_post_word len (inv_control_view rho) high i)))%nat;apply nth_error_Some;rewrite At;discriminate).
     destruct i as [|[|[|[|[|i]]]]];try lia;injection At as <-;apply Loads;lia. }
 destruct high.
 - apply(inv_copy_region (inv_tail_next_rho len rho) beta mf 5 (vars5 20)
    (fun i=>inv_post_word len (inv_control_view rho) true i));[exact Base|reflexivity| |exact Field|exact Free].
   intros i x At;destruct i as [|[|[|[|[|i]]]]];cbn [vars5 nth_error] in At;
    try(destruct i;discriminate At);injection At as <-;split;reflexivity.
 - apply(inv_copy_region (inv_tail_next_rho len rho) beta mf 4 (vars5 15)
    (fun i=>inv_post_word len (inv_control_view rho) false i));[exact Base|reflexivity| |exact Field|exact Free].
   intros i x At;destruct i as [|[|[|[|[|i]]]]];cbn [vars5 nth_error] in At;
    try(destruct i;discriminate At);injection At as <-;split;reflexivity.
Qed.

Theorem inv_mod_tail_restore len mu rho beta m mf : rep rho beta (inv_mod_loop_regs mu) m ->
 (forall (high : bool),Mem.range_perm mf (blk beta (if high then 5 else 4)) 0 40 Cur Freeable) ->
 (forall (high : bool) i,(i<5)%nat -> Mem.load Mint64 mf (blk beta (if high then 5 else 4)) (8*Z.of_nat i)=
  Some(Vlong(inv_post_word len (inv_control_view rho) high i))) ->
 lframe(fun b _=>b<>blk beta 4 /\ b<>blk beta 5) m mf ->
 rep (inv_tail_next_rho len rho) beta (inv_mod_loop_regs mu) mf.
Proof.
 intros Rep Free Loads Frame;pose proof(inv_mod_loop_distinct mu rho beta m Rep) as Distinct.
 pose proof(inv_mod_tail_array len mu rho beta m mf false Rep (Free false) (Loads false)) as F.
 pose proof(inv_mod_tail_array len mu rho beta m mf true Rep (Free true) (Loads true)) as G.
 destruct Rep as(Size & Sep & Regions);split;[exact Size|];split;[exact Sep|].
 assert(Outside:forall r,(r<7)%nat -> r<>4%nat -> r<>5%nat ->
  forall pos:Z,blk beta r<>blk beta 4 /\ blk beta r<>blk beta 5).
 { intros r R N4 N5 pos;split;apply Distinct;lia. }
 intros r reg At;assert(R:(r<7)%nat) by(change(r<length(inv_mod_loop_regs mu))%nat;apply nth_error_Some;rewrite At;discriminate).
 destruct r as [|[|[|[|[|[|[|r]]]]]]];try lia;cbn [inv_mod_loop_regs nth_error] in At;injection At as <-.
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=0%nat) (xs:=vars5 0) (ys:=vars5 0);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply Outside;lia|exact(Regions 0%nat _ eq_refl)].
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=1%nat)
    (xs:=map XLc(inv_mod_words mu)) (ys:=map XLc(inv_mod_words mu));try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply Outside;lia|exact(Regions 1%nat _ eq_refl)].
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=2%nat) (xs:=vars5 5) (ys:=vars5 5);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply Outside;lia|exact(Regions 2%nat _ eq_refl)].
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=3%nat) (xs:=vars5 10) (ys:=vars5 10);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply Outside;lia|exact(Regions 3%nat _ eq_refl)].
 - exact F.
 - exact G.
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=6%nat)
    (xs:=[XLv 25;XLv 26;XLv 27;XLv 28]) (ys:=[XLv 25;XLv 26;XLv 27;XLv 28]);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply Outside;lia|exact(Regions 6%nat _ eq_refl)].
Qed.

Theorem exec_inv_mod_tail mu len rho beta e le m : (0<len<=5)%nat -> rep rho beta (inv_mod_loop_regs mu) m ->
 ematch beta (snd inv_start_alloc) e -> le!_len=Some(Vint(Int.repr(Z.of_nat len))) -> inv_tail_low_bounds len rho ->
 exists lef mf out,
 Clight2.exec_stmt secp_ge e le m inv_post_control E0 lef mf out /\
 rep (inv_tail_next_rho len rho) beta (inv_mod_loop_regs mu) mf /\
 lef!_len=Some(Vint(Int.repr(Z.of_nat(inv_tail_length len rho)))) /\
 (forall high,inv_fg_active_value (inv_tail_length len rho) (inv_tail_next_rho len rho) high=inv_fg_active_value len rho high) /\
 inv_tail_low_bounds (inv_tail_length len rho) (inv_tail_next_rho len rho) /\
 (out=Out_break <-> inv_fg_active_value (inv_tail_length len rho) (inv_tail_next_rho len rho) true=0) /\
 (out=Out_normal -> inv_fg_active_value (inv_tail_length len rho) (inv_tail_next_rho len rho) true<>0) /\
 (out=Out_break \/ out=Out_normal) /\ (0<inv_tail_length len rho<=5)%nat /\
 inv_post_temp_frame le lef /\ lframe(fun b _=>b<>blk beta 4 /\ b<>blk beta 5) m mf.
Proof.
 intros Len Rep Env Length Bounds.
 assert(Base:forall high:bool,bas beta (if high then 5 else 4)=0)
  by(intro high;apply(inv_mod_owned_base mu rho beta m _ Rep);destruct high;lia).
 assert(Loads:forall (high:bool) i,(i<5)%nat -> Mem.load Mint64 m (blk beta (if high then 5 else 4)) (8*Z.of_nat i)=
  Some(Vlong(inv_control_word(inv_control_view rho) high i))).
 { intros high i I;pose proof(xload_u64_defined_sound rho beta _ m _ _ _ Rep (inv_mod_tail_load_expr mu high i I)) as L.
   rewrite Base,Z.add_0_l in L;rewrite inv_control_view_word by exact I;exact L. }
 assert(Free:forall high:bool,Mem.range_perm m (blk beta (if high then 5 else 4)) 0 40 Cur Freeable).
 { intro high;destruct high.
   - exact(proj2(rep_free_region rho beta (inv_mod_loop_regs mu) m 5 40 Rep ltac:(change(5<7)%nat;lia) eq_refl)).
   - exact(proj2(rep_free_region rho beta (inv_mod_loop_regs mu) m 4 40 Rep ltac:(change(4<7)%nat;lia) eq_refl)). }
 pose proof(inv_mod_loop_distinct mu rho beta m Rep) as Distinct.
 destruct(exec_inv_post_storage len (inv_control_view rho) (blk beta 4) (blk beta 5) e le m Len
  (Distinct 4%nat 5%nat ltac:(lia) ltac:(lia) ltac:(lia)) (proj1(Env _f)) (proj1(Env _g)) Length
  (Free false) (Free true) ltac:(intros high i I;destruct high;[exact(Loads true i I)|exact(Loads false i I)]))
  as(lef & mf & Exec & Out & FF & FG & NewLength & Range & TFrame & Frame).
 change(0<inv_tail_length len rho<=5)%nat in Range.
 assert(NextValues:forall high,inv_fg_active_value (inv_tail_length len rho) (inv_tail_next_rho len rho) high=inv_fg_active_value len rho high).
 { intro high;rewrite inv_tail_next_value by exact Range.
   unfold inv_tail_length;rewrite inv_post_next_value by exact Range.
   rewrite(proj1(inv_post_numeric len (inv_control_view rho) high Len (inv_tail_view_bounds len rho Len Bounds high))).
   apply inv_control_view_value;exact Len. }
 assert(NextLow:inv_tail_low_bounds (inv_tail_length len rho) (inv_tail_next_rho len rho)).
 { intros high j J;rewrite inv_tail_next_word by lia;rewrite inv_post_next_word by lia.
   apply(proj2(inv_post_numeric len (inv_control_view rho) high Len (inv_tail_view_bounds len rho Len Bounds high)));exact J. }
 assert(NextStop:inv_post_out len (inv_control_view rho)=Out_break <->
  inv_fg_active_value (inv_tail_length len rho) (inv_tail_next_rho len rho) true=0).
 { rewrite NextValues,<-(inv_control_view_value len rho true Len).
   apply inv_post_out_value;[lia|exact(inv_tail_view_bounds len rho Len Bounds true)]. }
 exists lef,mf,(inv_post_out len (inv_control_view rho));split;[exact Exec|];split.
 - eapply inv_mod_tail_restore;[exact Rep|intro high;destruct high;assumption| |exact Frame].
   intros high i I;destruct high;[exact(Out true i I)|exact(Out false i I)].
 - split;[exact NewLength|];split;[exact NextValues|];split;[exact NextLow|];split;[exact NextStop|];split.
   + intros Normal Zero;apply(proj2 NextStop) in Zero;congruence.
   + split;[unfold inv_post_out;destruct(inv_control_stops len (inv_control_view rho));auto|].
     split;[exact Range|];split;assumption.
Qed.
