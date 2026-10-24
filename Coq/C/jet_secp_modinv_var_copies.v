(** Original variable-inverse struct copies; no external copy model. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Cop Clightdefs Clight ClightBigstep Maps Memory Values Events Errors.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem C.jet_sx_region_lframe.
Require Import C.jet_secp_modinv_var_entry C.jet_secp_statement_prefix C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_signed62_assign C.jet_secp_modinfo_fe_global C.jet_secp_modinfo_fe_copy.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_curve_statements C.jet_secp_fns C.jet_secp_modinv_fg_index.
Require Import C.jet_secp_u128_shift64_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge inv_init_state.

Lemma inv_rep_replace_owned rho beta regs m mf k old new :
 rep rho beta regs m -> nth_error regs k=Some old -> rfree old<>None ->
 rshape new=rshape old -> region_ok rho beta mf k new ->
 lframe (fun b _=>b<>blk beta k) m mf -> rep rho beta (upd regs k new) mf.
Proof.
 intros Rep At Owned Shape New Frame.
 destruct Rep as (Len & Sep & Regions);split;[rewrite upd_length;exact Len|];split.
 - apply (rsep_shape beta regs);[apply upd_map_id with (x:=old);assumption|exact Sep].
 - intros r reg Entry;destruct (Nat.eq_dec k r) as [<-|Other].
   + rewrite (upd_same _ _ _ _ At) in Entry;injection Entry as <-;exact New.
   + rewrite upd_other in Entry by exact Other.
     eapply region_ok_lframe;[exact Frame| |exact (Regions r reg Entry)].
     intros pos Same.
     destruct (Sep k r old reg Other At Entry) as [Different|[NoOwner _]];
      [congruence|contradiction].
Qed.

Definition inv_modulus_exprs := map XLc (firstn 5 modinfo_fe_words).
Definition inv_input_exprs := [XLv 0;XLv 1;XLv 2;XLv 3;XLv 4].
Definition inv_f_regs := upd (sregs inv_init_state) 4 (mkreg (u64_cells 0 inv_modulus_exprs) true (Some 40)).
Definition inv_fg_regs := upd inv_f_regs 5 (mkreg (u64_cells 0 inv_input_exprs) true (Some 40)).
Definition inv_copy_regs (g : bool) := if g then inv_f_regs else sregs inv_init_state.
Definition inv_copy_words (rho : nat->int64) (g : bool) i := if g then rho i else modinfo_fe_limb i.
Definition inv_copy_expr (g : bool) i := if g then XLv i else XLc (modinfo_fe_limb i).
Definition inv_copy_exprs (g : bool) := if g then inv_input_exprs else inv_modulus_exprs.
Definition inv_copy_target (g : bool) : nat := if g then 5 else 4.
Definition inv_copy_source (g : bool) : nat := if g then 0 else 1.
Lemma inv_copy_load (g : bool) i : (i<5)%nat ->
 xload (inv_copy_regs g) (inv_copy_source g) (8*Z.of_nat i) tulong=Some (inv_copy_expr g i).
Proof. destruct g;destruct i as [|[|[|[|[|i]]]]];intro I;try lia;reflexivity. Qed.
Lemma inv_copy_expr_den rho beta g i : den rho beta (inv_copy_expr g i)=Vlong (inv_copy_words rho g i).
Proof. destruct g;reflexivity. Qed.
Lemma inv_copy_values rho beta g i x : nth_error (inv_copy_exprs g) i=Some x ->
 den rho beta x=Vlong (inv_copy_words rho g i) /\ xp_le (inv_copy_target g) x=true.
Proof.
 destruct g;destruct i as [|[|[|[|[|i]]]]];cbn [inv_copy_exprs inv_input_exprs inv_modulus_exprs
  firstn modinfo_fe_words nth_error];intro E;try (destruct i;discriminate E);
  injection E as <-;split;reflexivity.
Qed.
Lemma inv_copy_owned g :
 rfree (nth (inv_copy_target g) (inv_copy_regs g) (mkreg [] true None))=Some 40.
Proof. destruct g;reflexivity. Qed.
Lemma inv_copy_lengths g : length (inv_copy_regs g)=7%nat /\ length (inv_copy_exprs g)=5%nat.
Proof. destruct g;split;reflexivity. Qed.
Lemma inv_copy_region_shape g :
 rshape (mkreg (u64_cells 0 (inv_copy_exprs g)) true (Some 40))=
 rshape (nth (inv_copy_target g) (inv_copy_regs g) (mkreg [] true None)).
Proof. destruct g;reflexivity. Qed.
Lemma inv_copy_result g :
 upd (inv_copy_regs g) (inv_copy_target g) (mkreg (u64_cells 0 (inv_copy_exprs g)) true (Some 40))=
 if g then inv_fg_regs else inv_f_regs.
Proof. destruct g;reflexivity. Qed.

Lemma inv_copy_separate rho beta m g : rep rho beta (inv_copy_regs g) m ->
 blk beta (inv_copy_target g)<>blk beta (inv_copy_source g).
Proof.
 intros (_ & Sep & _).
 assert (Different : inv_copy_target g<>inv_copy_source g) by (destruct g;discriminate).
 pose proof (nth_error_nth' (inv_copy_regs g) (mkreg [] true None) (n:=inv_copy_target g)
  ltac:(rewrite (proj1 (inv_copy_lengths g));destruct g;cbn [inv_copy_target];lia)) as Target.
 pose proof (nth_error_nth' (inv_copy_regs g) (mkreg [] true None) (n:=inv_copy_source g)
  ltac:(rewrite (proj1 (inv_copy_lengths g));destruct g;cbn [inv_copy_source];lia)) as Source.
 destruct (Sep _ _ _ _ Different Target Source) as [SepBlocks|[NoOwner _]];[exact SepBlocks|].
 rewrite inv_copy_owned in NoOwner;discriminate.
Qed.

Lemma inv_five_readable m b w :
 (forall i,(i<5)%nat -> Mem.load Mint64 m b (8*Z.of_nat i)=Some (Vlong (w i))) ->
 Mem.range_perm m b 0 40 Cur Readable.
Proof.
 intros Loads pos Range.
 assert (Cases : 0<=pos<8 \/ 8<=pos<16 \/ 16<=pos<24 \/ 24<=pos<32 \/ 32<=pos<40) by lia.
 destruct Cases as [Case|[Case|[Case|[Case|Case]]]];
  [pose proof (Loads 0%nat ltac:(lia)) as Load|pose proof (Loads 1%nat ltac:(lia)) as Load|
   pose proof (Loads 2%nat ltac:(lia)) as Load|pose proof (Loads 3%nat ltac:(lia)) as Load|
   pose proof (Loads 4%nat ltac:(lia)) as Load];
  apply Mem.load_valid_access in Load;apply (proj1 Load);exact Case.
Qed.

Lemma inv_copy_region rho beta m r xs w :
 bas beta r=0 -> length xs=5%nat ->
 (forall i x,nth_error xs i=Some x -> den rho (lay beta) x=Vlong (w i) /\ xp_le r x=true) ->
 fe_at m (blk beta r) 0 (words5 w) -> Mem.range_perm m (blk beta r) 0 40 Cur Freeable ->
 region_ok rho beta m r (mkreg (u64_cells 0 xs) true (Some 40)).
Proof.
 intros Base Len Values (Nonneg & Align & Max & Perm & Loads) Free.
 apply (region_with_freeable rho beta m r (mkreg (u64_cells 0 xs) true None) 40).
 - apply region_u64;try rewrite Base.
   + lia.
   + exact Align.
   + rewrite Len;exact Max.
   + eapply Mem.perm_valid_block;apply (Perm 0);lia.
   + rewrite Len;exact Perm.
   + intros i x At;destruct (Values i x At) as (Value & Bound);split;[|exact Bound].
     rewrite Value;apply Loads.
     assert (I : (i<5)%nat) by (rewrite <-Len;apply nth_error_Some;rewrite At;discriminate).
     destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity.
 - exact Base.
 - reflexivity.
 - exact Free.
 - apply Forall_forall;intros c InC;destruct (u64_cells_In xs 0 c InC) as (i & x & At & ->).
   assert (I : (i<5)%nat) by (rewrite <-Len;apply nth_error_Some;rewrite At;discriminate).
   cbn [cofs cchunk];change (0+8*Z.of_nat i+8<=40);lia.
Qed.

Lemma inv_init_temps : stemps inv_init_state=inv_start_temps.
Proof. reflexivity. Qed.
Lemma inv_init_regions_length : length (sregs inv_init_state)=7%nat.
Proof. reflexivity. Qed.
Lemma inv_f_shapes : map rshape inv_f_regs=map rshape (sregs inv_init_state).
Proof. reflexivity. Qed.
Lemma inv_fg_shapes : map rshape inv_fg_regs=map rshape (sregs inv_init_state).
Proof. reflexivity. Qed.

Definition inv_copy_stmt (g : bool) := nth (if g then 11 else 10) (fst inv_start_parts) Sskip.
Definition inv_copies := Ssequence (inv_copy_stmt false) (Ssequence (inv_copy_stmt true) Sskip).
Definition inv_copy_local id := Eaddrof (Evar id fg_s62_type) (tptr fg_s62_type).
Definition inv_copy_modulus := Eaddrof
 (Efield (Ederef (Etempvar _modinfo (tptr (Tstruct _secp256k1_modinv64_modinfo noattr)))
  (Tstruct _secp256k1_modinv64_modinfo noattr)) _modulus fg_s62_type) (tptr fg_s62_type).
Lemma inv_copy_f_source : inv_copy_stmt false=curve_call _secp256k1_modinv64_signed62_assign
 f_secp256k1_modinv64_signed62_assign None [inv_copy_local _f;inv_copy_modulus].
Proof. reflexivity. Qed.
Lemma inv_copy_g_source : inv_copy_stmt true=curve_call _secp256k1_modinv64_signed62_assign
 f_secp256k1_modinv64_signed62_assign None [inv_copy_local _g;Etempvar _x (tptr fg_s62_type)].
Proof. reflexivity. Qed.

Lemma inv_modinfo_layout : exists co,
 (genv_cenv secp_ge)!_secp256k1_modinv64_modinfo=Some co /\
 field_offset secp_ge _modulus (co_members co)=OK (0,Full).
Proof.
 assert (Members : option_map co_members ((genv_cenv secp_ge)!_secp256k1_modinv64_modinfo)=
  Some [Member_plain _modulus fg_s62_type;Member_plain _modulus_inv62 tulong]) by (vm_compute;reflexivity).
 destruct ((genv_cenv secp_ge)!_secp256k1_modinv64_modinfo) as [co|];[|discriminate].
 exists co;split;[reflexivity|];injection Members as Members;rewrite Members;reflexivity.
Qed.
Lemma eval_inv_modulus e le m b : le!_modinfo=Some (Vptr b Ptrofs.zero) ->
 eval_expr secp_ge e le m inv_copy_modulus (Vptr b Ptrofs.zero).
Proof.
 intro Ptr;destruct inv_modinfo_layout as (co & Composite & Offset).
 unfold inv_copy_modulus;apply eval_Eaddrof.
 change Ptrofs.zero with (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0)) at 1.
 eapply eval_Efield_struct with (co:=co) (delta:=0).
 - eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact Ptr|apply deref_loc_copy;reflexivity].
 - reflexivity.
 - exact Composite.
 - exact Offset.
Qed.

Lemma inv_copy_arguments rho e le m beta g :
 ematch beta (snd inv_start_alloc) e -> tmatch rho beta inv_start_temps le ->
 bas beta (inv_copy_source g)=0 ->
 eval_exprlist secp_ge e le m
  (if g then [inv_copy_local _g;Etempvar _x (tptr fg_s62_type)] else [inv_copy_local _f;inv_copy_modulus])
  (type_of_params (fn_params f_secp256k1_modinv64_signed62_assign))
  [Vptr (blk beta (inv_copy_target g)) Ptrofs.zero;Vptr (blk beta (inv_copy_source g)) Ptrofs.zero].
Proof.
 intros Env Temps Base.
 assert (X : le!_x=Some (Vptr (blk beta 0) (Ptrofs.repr (bas beta 0)))).
 { pose proof (Temps _x (XP 0 0) eq_refl) as T.
   change (le!_x=Some (Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0)))) in T.
   rewrite Z.add_0_r in T;exact T. }
 assert (Modinfo : le!_modinfo=Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1)))).
 { pose proof (Temps _modinfo (XP 1 0) eq_refl) as T.
   change (le!_modinfo=Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0)))) in T.
   rewrite Z.add_0_r in T;exact T. }
 destruct g;cbn [inv_copy_target inv_copy_source] in Base |- *.
 all: eapply eval_Econs.
 - apply eval_Eaddrof;apply eval_Evar_local;exact (proj1 (Env _g)).
 - reflexivity.
 - eapply eval_Econs;[apply eval_Etempvar;rewrite Base in X;exact X|reflexivity|constructor].
 - apply eval_Eaddrof;apply eval_Evar_local;exact (proj1 (Env _f)).
 - reflexivity.
 - eapply eval_Econs;[apply eval_inv_modulus;rewrite Base in Modinfo;exact Modinfo|reflexivity|constructor].
Qed.

Theorem exec_inv_copy rho beta e le m g :
 rep rho beta (inv_copy_regs g) m -> tmatch rho beta inv_start_temps le ->
 ematch beta (snd inv_start_alloc) e -> bas beta (inv_copy_source g)=0 -> exists mf,
 Clight2.exec_stmt secp_ge e le m (inv_copy_stmt g) E0 le mf Out_normal /\
 rep rho beta (if g then inv_fg_regs else inv_f_regs) mf /\
 lframe (fun b _=>b<>blk beta (inv_copy_target g)) m mf.
Proof.
 intros Rep Temps Env Base.
 assert (At : nth_error (inv_copy_regs g) (inv_copy_target g)=
   Some (nth (inv_copy_target g) (inv_copy_regs g) (mkreg [] true None))).
 { apply nth_error_nth';rewrite (proj1 (inv_copy_lengths g));destruct g;cbn [inv_copy_target];lia. }
 destruct (rep_free_region rho beta (inv_copy_regs g) m (inv_copy_target g) 40 Rep
   ltac:(rewrite (proj1 (inv_copy_lengths g));destruct g;cbn [inv_copy_target];lia) (inv_copy_owned g))
  as (DestBase & DestFree).
 assert (Loads : forall i,(i<5)%nat ->
  Mem.load Mint64 m (blk beta (inv_copy_source g)) (8*Z.of_nat i)=Some (Vlong (inv_copy_words rho g i))).
 { intros i I;pose proof (xload_u64_defined_sound rho beta _ m _ _ _ Rep (inv_copy_load g i I)) as L.
   rewrite Base,Z.add_0_l,inv_copy_expr_den in L;exact L. }
 assert (ByIndex : forall i v,nth_error (words5 (inv_copy_words rho g)) i=Some v ->
  Mem.load Mint64 m (blk beta (inv_copy_source g)) (8*Z.of_nat i)=Some (Vlong v)).
 { intros i v Entry;assert (I : (i<5)%nat).
   { change (i<length (words5 (inv_copy_words rho g)))%nat;apply nth_error_Some;rewrite Entry;discriminate. }
   destruct i as [|[|[|[|[|i]]]]];try lia;injection Entry as <-;apply Loads;lia. }
 destruct (eval_signed62_assign_readable (inv_copy_words rho g) m
  (blk beta (inv_copy_target g)) (blk beta (inv_copy_source g))
  (inv_copy_separate rho beta m g Rep) DestFree (inv_five_readable _ _ _ Loads) ByIndex)
  as (mf & Call & Out & Free & Frame).
 assert (New : region_ok rho beta mf (inv_copy_target g)
  (mkreg (u64_cells 0 (inv_copy_exprs g)) true (Some 40))).
 { apply (inv_copy_region rho beta mf (inv_copy_target g) (inv_copy_exprs g) (inv_copy_words rho g));
   [exact DestBase|exact (proj2 (inv_copy_lengths g))|
    intros i x H;exact (inv_copy_values rho (lay beta) g i x H)|exact Out|exact Free]. }
 assert (Post : rep rho beta (if g then inv_fg_regs else inv_f_regs) mf).
 { rewrite <-inv_copy_result;eapply inv_rep_replace_owned;
   [exact Rep|exact At|rewrite inv_copy_owned;discriminate|apply inv_copy_region_shape|exact New|exact Frame]. }
 exists mf;split;[|split;assumption].
 assert (Linked : In (_secp256k1_modinv64_signed62_assign,f_secp256k1_modinv64_signed62_assign) secp_pure).
 { unfold secp_pure;repeat (first [left;reflexivity|right]). }
 assert (NotLocal : e!_secp256k1_modinv64_signed62_assign=None)
  by exact (proj1 (Env _secp256k1_modinv64_signed62_assign)).
 pose proof (inv_copy_arguments rho e le m beta g Env Temps Base) as Args.
 destruct g;[rewrite inv_copy_g_source|rewrite inv_copy_f_source];
  eapply exec_curve_call with (result:=None) (v:=Vundef);eassumption.
Qed.

Theorem exec_inv_copies rho beta e le m :
 rep rho beta (sregs inv_init_state) m -> tmatch rho beta (stemps inv_init_state) le ->
 ematch beta (snd inv_start_alloc) e -> bas beta 1=0 -> exists mf,
 Clight2.exec_stmt secp_ge e le m inv_copies E0 le mf Out_normal /\
 rep rho beta inv_fg_regs mf /\ tmatch rho beta (stemps inv_init_state) le /\
 lframe (fun b _=>b<>blk beta 4 /\ b<>blk beta 5) m mf.
Proof.
 intros Rep Temps Env Metadata;pose proof Temps as Start;rewrite inv_init_temps in Start.
 destruct (exec_inv_copy rho beta e le m false Rep Start Env Metadata)
  as (m1 & CopyF & RepF & FrameF).
 assert (BaseX : bas beta 0=0).
 { eapply rep_owned_region_base_zero;[exact RepF|reflexivity|reflexivity]. }
 destruct (exec_inv_copy rho beta e le m1 true RepF Start Env BaseX)
  as (mf & CopyG & RepG & FrameG).
 exists mf;split.
 - unfold inv_copies;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m1);[exact CopyF|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mf);[exact CopyG|constructor].
 - split;[exact RepG|];split;[exact Temps|].
   eapply lframe_trans;[eapply lframe_implies;[exact FrameF|]|eapply lframe_implies;[exact FrameG|]];
    intros b pos [F G] Valid;assumption.
Qed.

Definition inv_copied_prefix := statement_sequence (firstn 12 (fst inv_start_parts)) Sskip.
Definition inv_after_copies := statement_sequence (skipn 12 (fst inv_start_parts)) (snd inv_start_parts).
Lemma inv_copied_prefix_source : inv_copied_prefix=
 statement_sequence (firstn 10 (fst inv_start_parts)) inv_copies.
Proof. reflexivity. Qed.
Lemma inv_after_copies_source : fn_body f_secp256k1_modinv64_var=
 statement_sequence (firstn 12 (fst inv_start_parts)) inv_after_copies.
Proof. reflexivity. Qed.

Lemma inv_copy_fresh beta betaN m : length beta=2%nat -> length betaN=5%nat ->
 Forall (fun p=>~Mem.valid_block m (fst p)) betaN ->
 forall r,(2<=r<7)%nat -> ~Mem.valid_block m (blk (beta++betaN) r).
Proof.
 intros OldLen NewLen Fresh r Range;unfold blk,lay;rewrite app_nth2 by lia;rewrite OldLen.
 apply (proj1 (Forall_forall _ _) Fresh).
 apply nth_In;rewrite NewLen;lia.
Qed.

(** This specialized entry uses modulus metadata at block offset zero,
    as in the actual constant global. No limb-value restriction is imposed
    on the inverse input. *)
Theorem inv_entry_and_copies rho beta m : rep rho beta inv_start_regs m -> bas beta 1=0 ->
 exists betaN e le mi lef mf,
 function_entry2 secp_ge f_secp256k1_modinv64_var (map (den rho (lay beta)) inv_start_args) m e le mi /\
 Clight2.exec_stmt secp_ge e le mi inv_copied_prefix E0 lef mf Out_normal /\
 rep rho (beta++betaN) inv_fg_regs mf /\
 tmatch rho (beta++betaN) (stemps inv_init_state) lef /\
 ematch (beta++betaN) (snd inv_start_alloc) e /\
 Forall (fun p=>~Mem.valid_block m (fst p)) betaN /\
 lframe (fun b ofs=>~foot (beta++betaN) (map rshape (sregs inv_start_state)) b ofs) m mf.
Proof.
 intros Rep Metadata;assert (Len : length beta=2%nat) by exact (proj1 Rep).
 destruct (inv_entry_and_initializers rho beta m Rep)
  as (betaN & e & le & mi & lef & m1 & Entry & Init & Rep1 & Temps & Env & Bounds & Fresh & Frame1).
 assert (MetadataN : bas (beta++betaN) 1=0).
 { unfold bas;rewrite lay_app_l by lia;exact Metadata. }
 destruct (exec_inv_copies rho (beta++betaN) e lef m1 Rep1 Temps Env MetadataN)
  as (mf & Copy & RepF & TempsF & Frame2).
 assert (LocalLen : length betaN=5%nat).
 { pose proof (proj1 Rep1) as L;rewrite app_length,inv_init_regions_length,Len in L;lia. }
 assert (CallerCopies : lframe
  (fun b pos=>Mem.valid_block m b /\ ~foot (beta++betaN) (map rshape (sregs inv_start_state)) b pos) m1 mf).
 { eapply lframe_implies;[exact Frame2|].
   intros b pos [Valid Outside] Valid1;split;intro Same;subst b.
   - exact (inv_copy_fresh beta betaN m Len LocalLen Fresh 4%nat ltac:(lia) Valid).
   - exact (inv_copy_fresh beta betaN m Len LocalLen Fresh 5%nat ltac:(lia) Valid). }
 exists betaN,e,le,mi,lef,mf;split;[exact Entry|];split.
 - rewrite inv_copied_prefix_source;eapply exec_statement_prefix_then_last;[exact Init|exact Copy].
 - split;[exact RepF|];split;[exact TempsF|];split;[exact Env|];split;[exact Fresh|].
   eapply lframe_implies with
    (P:=fun b pos=>Mem.valid_block m b /\ ~foot (beta++betaN) (map rshape (sregs inv_start_state)) b pos).
   + eapply lframe_trans;[|exact CallerCopies].
     eapply lframe_implies;[exact Frame1|];intros b pos [Valid Outside] V;exact Outside.
   + intros b pos Outside Valid;split;assumption.
Qed.

Definition inv_loop_setup := statement_sequence (firstn 2 (skipn 12 (fst inv_start_parts))) Sskip.
Definition inv_loop_start_temps := PTree.set _eta (XLc (Int64.repr (-1)))
 (PTree.set _len (XIc (Int.repr 5)) inv_start_temps).
Definition inv_loop_start_env le := PTree.set _eta (Vlong (Int64.repr (-1)))
 (PTree.set _len (Vint (Int.repr 5)) le).
Definition inv_ready_prefix := statement_sequence (firstn 14 (fst inv_start_parts)) Sskip.
Definition inv_after_ready := statement_sequence (skipn 14 (fst inv_start_parts)) (snd inv_start_parts).
Lemma inv_loop_setup_source : inv_loop_setup=
 Ssequence (Sset _len (Econst_int (Int.repr 5) tint))
 (Ssequence (Sset _eta (Ecast (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tlong)) Sskip).
Proof. reflexivity. Qed.
Lemma inv_ready_prefix_source : inv_ready_prefix=
 statement_sequence (firstn 12 (fst inv_start_parts)) inv_loop_setup.
Proof. reflexivity. Qed.
Lemma inv_after_ready_source : fn_body f_secp256k1_modinv64_var=
 statement_sequence (firstn 14 (fst inv_start_parts)) inv_after_ready.
Proof. reflexivity. Qed.
Lemma exec_inv_loop_setup rho beta e le m : tmatch rho beta inv_start_temps le ->
 Clight2.exec_stmt secp_ge e le m inv_loop_setup E0 (inv_loop_start_env le) m Out_normal /\
 tmatch rho beta inv_loop_start_temps (inv_loop_start_env le).
Proof.
 intro Temps;split.
 - rewrite inv_loop_setup_source;unfold inv_loop_start_env.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _len (Vint (Int.repr 5)) le).
   + apply exec_Sset;constructor.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
      (le1:=PTree.set _eta (Vlong (Int64.repr (-1))) (PTree.set _len (Vint (Int.repr 5)) le)).
     * apply exec_Sset;eapply eval_Ecast with (v1:=Vint (Int.repr (-1))).
       -- eapply eval_Eunop;[constructor|reflexivity].
       -- reflexivity.
     * constructor.
 - unfold inv_loop_start_temps,inv_loop_start_env;apply tmatch_set;apply tmatch_set;exact Temps.
Qed.

Theorem inv_entry_to_loop rho beta m : rep rho beta inv_start_regs m -> bas beta 1=0 ->
 exists betaN e le mi lef mf,
 function_entry2 secp_ge f_secp256k1_modinv64_var (map (den rho (lay beta)) inv_start_args) m e le mi /\
 Clight2.exec_stmt secp_ge e le mi inv_ready_prefix E0 lef mf Out_normal /\
 rep rho (beta++betaN) inv_fg_regs mf /\
 tmatch rho (beta++betaN) inv_loop_start_temps lef /\
 ematch (beta++betaN) (snd inv_start_alloc) e /\
 lef!_len=Some (Vint (Int.repr 5)) /\ lef!_eta=Some (Vlong (Int64.repr (-1))) /\
 Forall (fun p=>~Mem.valid_block m (fst p)) betaN /\
 lframe (fun b ofs=>~foot (beta++betaN) (map rshape (sregs inv_start_state)) b ofs) m mf.
Proof.
 intros Rep Metadata;destruct (inv_entry_and_copies rho beta m Rep Metadata)
  as (betaN & e & le & mi & lc & mf & Entry & Prefix & RepF & Temps & Env & Fresh & Frame).
 rewrite inv_init_temps in Temps.
 destruct (exec_inv_loop_setup rho (beta++betaN) e lc mf Temps) as (Setup & TFinal).
 exists betaN,e,le,mi,(inv_loop_start_env lc),mf;split;[exact Entry|];split.
 - rewrite inv_ready_prefix_source;eapply exec_statement_prefix_then_last;[exact Prefix|exact Setup].
 - split;[exact RepF|];split;[exact TFinal|];split;[exact Env|];split.
   + unfold inv_loop_start_env;rewrite PTree.gso by discriminate;apply PTree.gss.
   + split;[apply PTree.gss|];split;assumption.
Qed.
