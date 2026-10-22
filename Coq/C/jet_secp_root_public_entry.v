(** The original public square-root wrapper's three local allocations and frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_exec C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition root_public_env (bl br ba : block) : env :=
  PTree.set _a (ba,Tstruct __5467 noattr)
    (PTree.set _r (br,Tstruct __5467 noattr)
      (PTree.set _src (bl,Tstruct _frameItem noattr) empty_env)).
Definition root_public_temps (v_env : val) bd dbase bs sbase : temp_env :=
  PTree.set _env v_env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps (fn_temps f_simplicity_fe_square_root)))).

Lemma root_public_ok : fn_okb f_simplicity_fe_square_root=true.
Proof. reflexivity. Qed.

Lemma root_public_entry v_env m ma mb mc bl br ba bd dbase bs sbase :
  Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 40=(mb,br) -> Mem.alloc mb 0 40=(mc,ba) ->
  function_entry2 secp_ge f_simplicity_fe_square_root
    [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] m
    (root_public_env bl br ba) (root_public_temps v_env bd dbase bs sbase) mc.
Proof.
  intros HA HB HC;destruct (fn_okb_true _ root_public_ok) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
  eapply alloc_variables_cons with (m1:=ma) (b1:=bl);[exact HA|].
  eapply alloc_variables_cons with (m1:=mb) (b1:=br);[exact HB|].
  eapply alloc_variables_cons with (m1:=mc) (b1:=ba);[exact HC|constructor].
Qed.

Lemma root_public_blocks bl br ba :
  blocks_of_env secp_ge (root_public_env bl br ba)=[(bl,0,16);(ba,0,40);(br,0,40)].
Proof. reflexivity. Qed.

Lemma root_free_public_locals m bl br ba : br<>bl -> ba<>bl -> br<>ba ->
  Mem.range_perm m bl 0 16 Cur Freeable -> Mem.range_perm m br 0 40 Cur Freeable ->
  Mem.range_perm m ba 0 40 Cur Freeable -> exists mf,
  Mem.free_list m (blocks_of_env secp_ge (root_public_env bl br ba))=Some mf /\
  lframe (fun b _=>b<>br /\ b<>ba /\ b<>bl) m mf.
Proof.
  intros HRL HAL HRA HL HR HA.
  destruct (free_list_exists [(bl,0,16);(ba,0,40);(br,0,40)] m) as (mf & HF & HU).
  - cbn;repeat constructor;cbn;intuition congruence.
  - intros b lo hi [HE|[HE|[HE|HE]]];
      [inversion HE;subst;exact HL|inversion HE;subst;exact HA|inversion HE;subst;exact HR|contradiction].
  - exists mf;split;[rewrite root_public_blocks;exact HF|].
    eapply lframe_implies;[apply lframe_unchanged;exact HU|].
    intros b pos [HNR [HNA HNL]] HV;cbn;intuition congruence.
Qed.

Lemma root_public_allocations_fresh m ma mb mc bl br ba :
  Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 40=(mb,br) -> Mem.alloc mb 0 40=(mc,ba) ->
  ~Mem.valid_block m bl /\ ~Mem.valid_block m br /\ ~Mem.valid_block m ba /\
  br<>bl /\ ba<>bl /\ br<>ba.
Proof.
  intros HA HB HC.
  pose proof (Mem.valid_new_block _ _ _ _ _ HA) as VL.
  pose proof (Mem.valid_new_block _ _ _ _ _ HB) as VR.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HA) as NL.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HB) as NR.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HC) as NA.
  assert (VL' : Mem.valid_block mb bl) by (eapply Mem.valid_block_alloc;eassumption).
  repeat split;intros HE;try exact (NL HE).
  - apply NR;eapply Mem.valid_block_alloc;eassumption.
  - apply NA;eapply Mem.valid_block_alloc;[exact HB|];eapply Mem.valid_block_alloc;eassumption.
  - apply NR;rewrite HE;exact VL.
  - apply NA;rewrite HE;exact VL'.
  - apply NA;rewrite <-HE;exact VR.
Qed.

Lemma root_public_allocations_free m ma mb mc bl br ba :
  Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 40=(mb,br) -> Mem.alloc mb 0 40=(mc,ba) ->
  Mem.range_perm mc bl 0 16 Cur Freeable /\ Mem.range_perm mc br 0 40 Cur Freeable /\
  Mem.range_perm mc ba 0 40 Cur Freeable.
Proof.
  intros HA HB HC;repeat split;intros pos HPos.
  - eapply Mem.perm_alloc_1;[exact HC|];eapply Mem.perm_alloc_1;[exact HB|];
      eapply Mem.perm_alloc_2;eassumption.
  - eapply Mem.perm_alloc_1;[exact HC|];eapply Mem.perm_alloc_2;eassumption.
  - eapply Mem.perm_alloc_2;eassumption.
Qed.

Lemma root_public_allocations_frame P m ma mb mc bl br ba :
  Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 40=(mb,br) -> Mem.alloc mb 0 40=(mc,ba) ->
  lframe P m mc.
Proof.
  intros HA HB HC;eapply lframe_trans.
  - apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact HA.
  - eapply lframe_trans;apply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption.
Qed.
