(** Actual nine-local entry of the original point_verify_1 wrapper.
    The complete public theorem must still compose the readers and body. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Integers Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jets_secp C.jet_secp_linkage C.jet_clight_internal_preserve
 C.jet_sx_state C.jet_sx_expr C.jet_sx_exec C.jet_sx_mem.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition point_verify_public_env bl bax bbx ba bb bk bg br bz :=
 PTree.set _a0 (bz,Tstruct __6123 noattr)
 (PTree.set _r (br,Tstruct __6123 noattr)
 (PTree.set _ng__2 (bg,Tstruct __5826 noattr)
 (PTree.set _na__1 (bk,Tstruct __5826 noattr)
 (PTree.set _b (bb,Tstruct __6121 noattr)
 (PTree.set _a__1 (ba,Tstruct __6121 noattr)
 (PTree.set _bx (bbx,Tstruct __5467 noattr)
 (PTree.set _ax (bax,Tstruct __5467 noattr)
 (PTree.set _src (bl,Tstruct _frameItem noattr) empty_env)))))))).
Definition point_verify_public_temps v_env bd base bs sbase :=
 PTree.set _env v_env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
 (PTree.set _dst (Vptr bd (Ptrofs.repr base))
 (create_undef_temps (fn_temps f_simplicity_point_verify_1)))).
Definition point_verify_public_storage (bl bax bbx ba bb bk bg br bz:block) :=
 [(bl,16);(bax,40);(bbx,40);(ba,88);(bb,88);(bk,32);(bg,32);(br,128);(bz,128)].
Definition point_verify_public_locals (bl bax bbx ba bb bk bg br bz:block) := [bl;bax;bbx;ba;bb;bk;bg;br;bz].
Lemma point_verify_public_entry_ok : fn_okb f_simplicity_point_verify_1=true.
Proof. reflexivity. Qed.

Local Ltac allocated_valid := first [assumption |
 match goal with A:Mem.alloc _ _ _=(?mm,?bb) |- Mem.valid_block ?mm ?bb =>
  eapply Mem.valid_new_block;exact A end |
 match goal with A:Mem.alloc _ _ _=(?mm,_) |- Mem.valid_block ?mm _ =>
  eapply Mem.valid_block_alloc;[exact A|allocated_valid] end].
Local Ltac allocated_distinct := first [assumption |
 match goal with A:Mem.alloc _ _ _=(_,?bb) |- ?ba<>?bb =>
  let Eq:=fresh "Eq" in intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ A);
   rewrite <-Eq;allocated_valid end |
 match goal with A:Mem.alloc _ _ _=(_,?ba) |- ?ba<>?bb =>
  let Eq:=fresh "Eq" in intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ A);
   rewrite Eq;allocated_valid end].
Local Ltac allocated_perm Range := first [
 match goal with A:Mem.alloc _ _ _=(?mm,?bb) |- Mem.perm ?mm ?bb _ _ _ =>
  eapply Mem.perm_alloc_2;[exact A|exact Range] end |
 match goal with A:Mem.alloc _ _ _=(?mm,_) |- Mem.perm ?mm _ _ _ _ =>
  eapply Mem.perm_alloc_1;[exact A|allocated_perm Range] end].
Local Ltac allocated_frame := lazymatch goal with |- lframe _ ?ma ?mb =>
 tryif constr_eq ma mb then apply lframe_refl else
 match goal with A:Mem.alloc ma _ _=(?mi,_) |- _ =>
  eapply lframe_trans with (m2:=mi);
   [apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact A|allocated_frame] end end.

Theorem point_verify_public_entry v_env m bd base bs sbase : exists mi bl bax bbx ba bb bk bg br bz,
 function_entry2 secp_ge f_simplicity_point_verify_1
   [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m
   (point_verify_public_env bl bax bbx ba bb bk bg br bz)
   (point_verify_public_temps v_env bd base bs sbase) mi /\
 NoDup (point_verify_public_locals bl bax bbx ba bb bk bg br bz) /\
 (forall b,Mem.valid_block m b ->~In b (point_verify_public_locals bl bax bbx ba bb bk bg br bz)) /\
 (forall b hi,In (b,hi) (point_verify_public_storage bl bax bbx ba bb bk bg br bz) ->
   Mem.range_perm mi b 0 hi Cur Freeable) /\
 lframe (fun _ _=>True) m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 16) as (m1,bl) eqn:AL.
 destruct (Mem.alloc m1 0 40) as (m2,bax) eqn:AAX.
 destruct (Mem.alloc m2 0 40) as (m3,bbx) eqn:ABX.
 destruct (Mem.alloc m3 0 88) as (m4,ba) eqn:AA.
 destruct (Mem.alloc m4 0 88) as (m5,bb) eqn:AB.
 destruct (Mem.alloc m5 0 32) as (m6,bk) eqn:AK.
 destruct (Mem.alloc m6 0 32) as (m7,bg) eqn:AG.
 destruct (Mem.alloc m7 0 128) as (m8,br) eqn:AR.
 destruct (Mem.alloc m8 0 128) as (mi,bz) eqn:AZ.
 assert (Entry:function_entry2 secp_ge f_simplicity_point_verify_1
   [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m
   (point_verify_public_env bl bax bbx ba bb bk bg br bz)
   (point_verify_public_temps v_env bd base bs sbase) mi).
 { destruct (fn_okb_true _ point_verify_public_entry_ok) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons with (m1:=m1) (b1:=bl);[exact AL|].
   eapply alloc_variables_cons with (m1:=m2) (b1:=bax);[exact AAX|].
   eapply alloc_variables_cons with (m1:=m3) (b1:=bbx);[exact ABX|].
   eapply alloc_variables_cons with (m1:=m4) (b1:=ba);[exact AA|].
   eapply alloc_variables_cons with (m1:=m5) (b1:=bb);[exact AB|].
   eapply alloc_variables_cons with (m1:=m6) (b1:=bk);[exact AK|].
   eapply alloc_variables_cons with (m1:=m7) (b1:=bg);[exact AG|].
   eapply alloc_variables_cons with (m1:=m8) (b1:=br);[exact AR|].
   eapply alloc_variables_cons with (m1:=mi) (b1:=bz);[exact AZ|constructor]. }
 assert (Distinct:NoDup (point_verify_public_locals bl bax bbx ba bb bk bg br bz)).
 { unfold point_verify_public_locals;repeat rewrite NoDup_cons_iff;repeat rewrite not_in_cons;
   repeat split;try apply NoDup_nil;try apply in_nil;allocated_distinct. }
 assert (Old:forall b,Mem.valid_block m b ->~In b (point_verify_public_locals bl bax bbx ba bb bk bg br bz)).
 { intros b Valid;unfold point_verify_public_locals;repeat rewrite not_in_cons;
   repeat split;try apply in_nil;allocated_distinct. }
 exists mi,bl,bax,bbx,ba,bb,bk,bg,br,bz;split;[exact Entry|];split;[exact Distinct|];split;[exact Old|];split.
 - intros b hi Slot;cbn [point_verify_public_storage In] in Slot;
   repeat match goal with S:_ \/ _ |- _=>destruct S as [S|S] end;try contradiction;
   match goal with S:(_,_) = (_,_) |- _=>inversion S;subst b hi end;
   intros pos Range;allocated_perm Range.
 - split;[allocated_frame|eapply entry_preserved;exact Entry].
Qed.
Lemma point_verify_public_blocks bl bax bbx ba bb bk bg br bz :
 blocks_of_env secp_ge (point_verify_public_env bl bax bbx ba bb bk bg br bz)=
 [(bl,0,16);(bz,0,128);(ba,0,88);(bax,0,40);(bb,0,88);(bbx,0,40);(br,0,128);(bg,0,32);(bk,0,32)].
Proof. reflexivity. Qed.

Lemma point_verify_public_free m bl bax bbx ba bb bk bg br bz : NoDup (point_verify_public_locals bl bax bbx ba bb bk bg br bz) ->
 (forall b hi,In (b,hi) (point_verify_public_storage bl bax bbx ba bb bk bg br bz) ->
   Mem.range_perm m b 0 hi Cur Freeable) -> exists mf,
 Mem.free_list m (blocks_of_env secp_ge (point_verify_public_env bl bax bbx ba bb bk bg br bz))=Some mf /\
 lframe (fun b _=>~In b (point_verify_public_locals bl bax bbx ba bb bk bg br bz)) m mf /\ readonly_preserved m mf.
Proof.
 intros Distinct Free.
 destruct (free_list_exists [(bl,0,16);(bz,0,128);(ba,0,88);(bax,0,40);(bb,0,88);(bbx,0,40);(br,0,128);(bg,0,32);(bk,0,32)] m)
   as (mf & Freed & Frame).
 - cbn;unfold point_verify_public_locals in Distinct;repeat rewrite NoDup_cons_iff in Distinct;
   cbn in Distinct;repeat constructor;cbn;intuition congruence.
 - intros b lo hi Slot;cbn [In] in Slot;
   repeat match goal with S:_ \/ _ |- _=>destruct S as [S|S] end;try contradiction;
   match goal with S:(_,_,_) = (_,_,_) |- _=>inversion S;subst b lo hi end;
   apply Free;clear;cbn [point_verify_public_storage In];tauto.
 - exists mf;split;[rewrite point_verify_public_blocks;exact Freed|];split.
   + eapply lframe_implies;[apply lframe_unchanged;exact Frame|].
     intros b ofs Outside Valid;unfold point_verify_public_locals in Outside;cbn in *;intuition congruence.
   + eapply freelist_preserved;exact Freed.
Qed.


Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout C.jet_output_layout
 C.jet_frame_inv C.jet_encoding C.jet_secp_frame C.jet_secp_public_copy C.jet_secp_local_regions.
Definition point_verify_public_copy :=
 Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)).

Theorem point_verify_public_prepare v_env m0 bd base bs sbase bw edge cursor N bi inedge rc :
 write_frame_at m0 bd base bw edge cursor N ->
 frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi inedge rc ->
 exists mi md bl bax bbx ba bb bk bg br bz,
 function_entry2 secp_ge f_simplicity_point_verify_1
  [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m0
  (point_verify_public_env bl bax bbx ba bb bk bg br bz) (point_verify_public_temps v_env bd base bs sbase) mi /\
 Clight2.exec_stmt secp_ge (point_verify_public_env bl bax bbx ba bb bk bg br bz) (point_verify_public_temps v_env bd base bs sbase)
  mi point_verify_public_copy E0 (point_verify_public_temps v_env bd base bs sbase) md Out_normal /\
 (forall b hi,In (b,hi) (point_verify_public_storage bl bax bbx ba bb bk bg br bz) -> Mem.range_perm md b 0 hi Cur Freeable) /\
 frame_fields_at md bl 0 bi inedge rc /\
 NoDup (point_verify_public_locals bl bax bbx ba bb bk bg br bz) /\
 (forall b,Mem.valid_block m0 b -> ~In b (point_verify_public_locals bl bax bbx ba bb bk bg br bz)) /\
 xsep (extA m0 bd bw bi) [(bl,0);(bax,0);(bbx,0);(ba,0);(bb,0);(bk,0);(bg,0);(br,0);(bz,0)] /\
 finv m0 bd base bw edge cursor N bi md false [] /\ readonly_preserved m0 md /\
 lframe (fun b _=>~In b (point_verify_public_locals bl bax bbx ba bb bk bg br bz)) m0 md.
Proof.
 intros Output Base Align Source.
 destruct (point_verify_public_entry v_env m0 bd base bs sbase)
  as (mi & bl & bax & bbx & ba & bb & bk & bg & br & bz & Entry & Separate & Old & Owned & AllocFrame & AllocRead).
 assert (SourceI:frame_fields_at mi bs sbase bi inedge rc).
 { destruct Source as [SE SC];pose proof (load_valid m0 Mptr bs sbase _ SE) as Valid;
   split;rewrite (proj1 AllocFrame) by auto;assumption. }
 destruct SourceI as [Edge Cursor].
 destruct (frame_loadbytes_at mi bs sbase _ _ Edge Cursor) as (bytes & Load).
 pose proof (Mem.loadbytes_length _ _ _ _ _ Load) as Length.
 assert (FreeL:Mem.range_perm mi bl 0 16 Cur Freeable).
 { apply Owned;clear;cbn [point_verify_public_storage In];tauto. }
 assert (Writable:Mem.range_perm mi bl 0 (0+Z.of_nat (length bytes)) Cur Writable).
 { rewrite Length;apply freeable_range_writable;exact FreeL. }
 destruct (Mem.range_perm_storebytes mi bl 0 bytes Writable) as (md & Store).
 assert (Frame:lframe (fun b _=>~In b (point_verify_public_locals bl bax bbx ba bb bk bg br bz)) m0 md).
 { eapply lframe_trans;[eapply lframe_implies;[exact AllocFrame|intros;exact I]|].
   apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|].
   intros pos Range Outside;apply Outside;left;reflexivity. }
 assert (Ext:eqext m0 bd bw bi m0 md).
 { eapply lframe_implies;[exact Frame|].
   intros b pos [_ Valid] _;apply Old;exact Valid. }
 assert (Outside:bl<>bs).
 { intro Same;pose proof (Old bs (load_valid m0 Mptr bs sbase _ (proj1 Source))) as NotLocal.
   apply NotLocal;unfold point_verify_public_locals;left;exact Same. }
 assert (U:Ptrofs.unsigned (Ptrofs.repr sbase)=sbase) by
  (apply Ptrofs.unsigned_repr;unfold frame_base_valid in Base;lia).
 assert (Copy:Clight2.exec_stmt secp_ge (point_verify_public_env bl bax bbx ba bb bk bg br bz)
  (point_verify_public_temps v_env bd base bs sbase) mi point_verify_public_copy E0
  (point_verify_public_temps v_env bd base bs sbase) md Out_normal).
 { unfold point_verify_public_copy;eapply exec_Sassign_copy.
   - apply eval_Evar_local;reflexivity.
   - apply eval_Etempvar;unfold point_verify_public_temps;rewrite PTree.gso by discriminate;apply PTree.gss.
   - reflexivity.
   - eapply assign_loc_copy with (b':=bs) (ofs':=Ptrofs.repr sbase) (bytes:=bytes).
     + reflexivity.
     + intros _;change (8|Ptrofs.unsigned (Ptrofs.repr sbase));rewrite U;exact Align.
     + intros _;change (8|0);exists 0;reflexivity.
     + left;congruence.
     + change (Mem.loadbytes mi bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16=Some bytes);rewrite U;exact Load.
     + exact Store. }
 exists mi,md,bl,bax,bbx,ba,bb,bk,bg,br,bz;split;[exact Entry|];split;[exact Copy|];split.
 - intros b hi Slot pos Range;eapply Mem.perm_storebytes_1;[exact Store|apply (Owned b hi Slot);exact Range].
 - split;[exact (frame_copy_fields_at mi md bs sbase bl bytes _ _ Load Store Edge Cursor)|].
   split;[exact Separate|];split;[exact Old|];split.
   + intros r Index;assert (Local:In (blk [(bl,0);(bax,0);(bbx,0);(ba,0);(bb,0);(bk,0);(bg,0);(br,0);(bz,0)] r)
     (point_verify_public_locals bl bax bbx ba bb bk bg br bz)).
     { destruct r as [|[|[|[|[|[|[|[|[|r]]]]]]]]];cbn [length] in Index;try lia;clear;
       cbn [blk bas lay nth fst point_verify_public_locals In];tauto. }
     unfold extA,fext;intros [_ Valid];exact (Old _ Valid Local).
   + split;[eapply finv_stable;[exact Output|apply finv_init;exact Output|exact Ext]|];split;[|exact Frame].
     eapply preserved_trans;[exact AllocRead|eapply storebytes_preserved;exact Store].
Qed.

