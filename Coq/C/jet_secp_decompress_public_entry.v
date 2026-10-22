(** Original public decompression entry and local storage sizes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_exec C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition decompress_public_env (bl bx br : block) : env :=
 PTree.set _r (br,Tstruct __6121 noattr)
  (PTree.set _x (bx,Tstruct __5467 noattr)
   (PTree.set _src (bl,Tstruct _frameItem noattr) empty_env)).
Definition decompress_public_temps (v_env : val) bd base bs sbase : temp_env :=
 PTree.set _env v_env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
  (PTree.set _dst (Vptr bd (Ptrofs.repr base))
   (create_undef_temps (fn_temps f_simplicity_decompress)))).
Lemma decompress_public_ok : fn_okb f_simplicity_decompress=true.
Proof. reflexivity. Qed.
Lemma decompress_public_entry v_env m ma mb mc bl bx br bd base bs sbase :
 Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 40=(mb,bx) -> Mem.alloc mb 0 88=(mc,br) ->
 function_entry2 secp_ge f_simplicity_decompress
  [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m
  (decompress_public_env bl bx br) (decompress_public_temps v_env bd base bs sbase) mc.
Proof.
 intros HA HB HC;destruct (fn_okb_true _ decompress_public_ok) as (HN1 & HN2 & HD).
 constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
 eapply alloc_variables_cons with (m1:=ma) (b1:=bl);[exact HA|].
 eapply alloc_variables_cons with (m1:=mb) (b1:=bx);[exact HB|].
 eapply alloc_variables_cons with (m1:=mc) (b1:=br);[exact HC|constructor].
Qed.
Lemma decompress_public_blocks bl bx br :
 blocks_of_env secp_ge (decompress_public_env bl bx br)=[(bl,0,16);(bx,0,40);(br,0,88)].
Proof. reflexivity. Qed.
Lemma decompress_free_public_locals m bl bx br : bx<>bl -> br<>bl -> bx<>br ->
 Mem.range_perm m bl 0 16 Cur Freeable -> Mem.range_perm m bx 0 40 Cur Freeable ->
 Mem.range_perm m br 0 88 Cur Freeable -> exists mf,
 Mem.free_list m (blocks_of_env secp_ge (decompress_public_env bl bx br))=Some mf /\
 lframe (fun b _=>b<>bx /\ b<>br /\ b<>bl) m mf.
Proof.
 intros XL RL XR LF XF RF.
 destruct (free_list_exists [(bl,0,16);(bx,0,40);(br,0,88)] m) as (mf & Free & Frame).
 - cbn;repeat constructor;cbn;intuition congruence.
 - intros b lo hi [HE | [HE | [HE | HE]]];
    [inversion HE;subst;exact LF|inversion HE;subst;exact XF|inversion HE;subst;exact RF|contradiction].
 - exists mf;split;[rewrite decompress_public_blocks;exact Free|].
   eapply lframe_implies;[apply lframe_unchanged;exact Frame|].
   intros b pos [NX [NR NL]] VB;cbn;intuition congruence.
Qed.
Lemma decompress_public_allocations_fresh m ma mb mc bl bx br :
 Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 40=(mb,bx) -> Mem.alloc mb 0 88=(mc,br) ->
 ~Mem.valid_block m bl /\ ~Mem.valid_block m bx /\ ~Mem.valid_block m br /\ bx<>bl /\ br<>bl /\ bx<>br.
Proof.
 intros HA HB HC.
 pose proof (Mem.valid_new_block _ _ _ _ _ HA) as VL.
 pose proof (Mem.valid_new_block _ _ _ _ _ HB) as VX.
 pose proof (Mem.fresh_block_alloc _ _ _ _ _ HA) as NL.
 pose proof (Mem.fresh_block_alloc _ _ _ _ _ HB) as NX.
 pose proof (Mem.fresh_block_alloc _ _ _ _ _ HC) as NR.
 assert (VL' : Mem.valid_block mb bl) by (eapply Mem.valid_block_alloc;eassumption).
 repeat split;intros HE;try exact (NL HE).
 - apply NX;eapply Mem.valid_block_alloc;eassumption.
 - apply NR;eapply Mem.valid_block_alloc;[exact HB|];eapply Mem.valid_block_alloc;eassumption.
 - apply NX;rewrite HE;exact VL.
 - apply NR;rewrite HE;exact VL'.
 - apply NR;rewrite <-HE;exact VX.
Qed.
Lemma decompress_public_allocations_free m ma mb mc bl bx br :
 Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 40=(mb,bx) -> Mem.alloc mb 0 88=(mc,br) ->
 Mem.range_perm mc bl 0 16 Cur Freeable /\ Mem.range_perm mc bx 0 40 Cur Freeable /\
 Mem.range_perm mc br 0 88 Cur Freeable.
Proof.
 intros HA HB HC;repeat split;intros pos Pos.
 - eapply Mem.perm_alloc_1;[exact HC|];eapply Mem.perm_alloc_1;[exact HB|];eapply Mem.perm_alloc_2;eassumption.
 - eapply Mem.perm_alloc_1;[exact HC|];eapply Mem.perm_alloc_2;eassumption.
 - eapply Mem.perm_alloc_2;eassumption.
Qed.
Lemma decompress_public_allocations_frame P m ma mb mc bl bx br :
 Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 40=(mb,bx) -> Mem.alloc mb 0 88=(mc,br) -> lframe P m mc.
Proof.
 intros HA HB HC;eapply lframe_trans.
 - apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact HA.
 - eapply lframe_trans;apply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption.
Qed.
