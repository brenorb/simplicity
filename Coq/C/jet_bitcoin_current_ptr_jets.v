(** Actual Bitcoin current_prev_outpoint jet against the literal canonical
    [CurrentIndex >>> assert InputPrevOutpoint].  The payload helper reads the
    outpoint while writing, so the separated contract is used. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jet_frame_copy C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_wide C.jet_wide_spec.
Require Import C.jet_encoding C.jet_input_layout C.jet_uint32_array_init C.jets_bitcoin C.jet_bitcoin_linkage C.jet_exec.
Require C.jets.
Require Import C.jet_bitcoin_version_exec C.jet_bitcoin_field_eval C.jet_bitcoin_wrapper C.jet_bitcoin_effects.
Require Import C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_index_eval C.jet_bitcoin_indexed_exec.
Require Import C.jet_bitcoin_current_exec C.jet_bitcoin_current_spec C.jet_bitcoin_current_ptr.
Require Import C.jet_bitcoin_indexed_scalar C.jet_bitcoin_indexed_ptr C.jet_bitcoin_hash_write C.jet_bitcoin_hash_helpers.
Require Import C.jet_bitcoin_script_cmr_local C.jet_bitcoin_indexed_scalar_jets C.jet_bitcoin_indexed_ptr_jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge ge0.
Set Default Timeout 60.

Definition current_ptr_rep {A} (elems_of : Bitcoin.env -> list A) (elemrep : mem -> block -> Z -> A -> Prop)
    (sz poff adelta cdelta : Z) (m : mem) (env : val) (environment : Bitcoin.env)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt txbase bin inbase nI ixv,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    0 <= txbase /\ txbase + 488 <= Ptrofs.max_unsigned /\
    0 <= inbase /\ inbase + sz * Z.of_nat (length (elems_of environment)) <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) /\
    Mem.load Mptr m bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) /\
    Mem.load Mint64 m bt (txbase + cdelta) = Some (Vlong nI) /\
    Mem.load Mint64 m be (ebase + 48) = Some (Vlong ixv) /\
    Int64.unsigned nI = Z.of_nat (length (elems_of environment)) /\
    Int64.unsigned ixv = Z.of_nat (Bitcoin.envIx environment) /\
    (forall j x, nth_error (elems_of environment) j = Some x ->
      elemrep m bin (inbase + sz * Z.of_nat j + poff) x) /\
    fp = [(bin, inbase, inbase + sz * Z.of_nat (length (elems_of environment)))].

Theorem bitcoin_current_ptr_local {A} (elems_of : Bitcoin.env -> list A) (nbits : Z) (pcells : A -> list Cell)
    (elemrep : mem -> block -> Z -> A -> Prop) (Bpay : Ty)
    (t1 t2 t3 ta tb tc arrfield countfield sid cid : ident) (pt : type)
    (cdelta adelta sz poff psz : Z) (pexpr : expr) (cf f : function)
    (Ha : ta <> _env) (Hb : tb <> _env) (Hc : tc <> _env) (H1 : t1 <> _env) (H2 : t2 <> _env) (H3 : t3 <> _env)
    (H1d : t1 <> _dst) (H2d : t2 <> _dst) (H3d : t3 <> _dst) (Had : ta <> _dst) (Hbd : tb <> _dst)
    (Hcd : tc <> _dst) (Hcb : tc <> tb) (H32 : t3 <> t2)
    (Hnb : 1 <= nbits <= 1000) (Hpty : typeof pexpr = tptr pt)
    (Hnone : forall bl, (bitcoin_version_locals bl)!cid = None)
    (Hsym : Genv.find_symbol (Clight.genv_genv bitcoin_ge) cid = Some (bitcoin_symbol_block cid))
    (Hfun : Genv.find_funct (Clight.genv_genv bitcoin_ge) (Vptr (bitcoin_symbol_block cid) Ptrofs.zero) =
      Some (Internal cf))
    (Hty : type_of_fundef (Internal cf) =
      Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr pt) Tnil)) tvoid cc_default)
    (Hcf : bitcoin_field_at _bitcoinTransaction countfield cdelta)
    (Haf : bitcoin_field_at _bitcoinTransaction arrfield adelta)
    (Hcb' : 0 <= cdelta /\ cdelta + 8 <= 488) (Hab : 0 <= adelta /\ adelta + 8 <= 488)
    (Hsz : 0 < sz <= 1000) (Hpoff : 0 <= poff /\ poff + psz <= sz)
    (Hpres : forall m1 m2 b ofs x, elemrep m1 b ofs x ->
      (forall chunk o v, ofs <= o -> o + size_chunk chunk <= ofs + psz ->
        Mem.load chunk m1 b o = Some v -> Mem.load chunk m2 b o = Some v) -> elemrep m2 b ofs x)
    (Hpay : forall bd dbase bw outedge m' bin ofs x cur, elemrep m' bin ofs x -> 0 <= ofs ->
      ofs + psz <= Ptrofs.max_unsigned ->
      out_sep bd dbase bw outedge cur nbits bin ofs (ofs + psz) ->
      write_frame_at m' bd dbase bw outedge cur nbits ->
      exists me, Clight2.eval_funcall bitcoin_ge m' (Internal cf)
        [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr ofs)] E0 me Vundef /\
        write_effect m' me bd dbase bw outedge cur nbits (pcells x))
    (Hptr : forall e le' m' bin inbase ixv,
      le'!t2 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!t3 = Some (Vlong ixv) ->
      0 <= inbase -> inbase + sz * Int64.unsigned ixv + poff + psz <= Ptrofs.max_unsigned ->
      eval_expr bitcoin_ge e le' m' pexpr (Vptr bin (Ptrofs.repr (inbase + sz * Int64.unsigned ixv + poff))))
    (Hshape : bitcoin_wrapper_shape f
      (bitcoin_current_ptr_rest t1 t2 t3 ta tb tc arrfield countfield sid pexpr cid pt))
    (HB : Z.of_nat (bitSize Bpay) = nbits)
    (spec : Ty.tySem Ty.Unit -> Bitcoin.env -> option (Ty.tySem Bpay))
    (Hsem : forall environment, exists x V, nth_error (elems_of environment) (Bitcoin.envIx environment) = Some x /\
      spec tt environment = Some V /\ encode V = pcells x)
    (Hlen : forall x, Z.of_nat (length (pcells x)) = nbits) :
  application_jet_local_spec_sep f bitcoin_ge Bitcoin.env Ty.Unit Bpay
    (current_ptr_rep elems_of elemrep sz poff adelta cdelta) spec.
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor [] fp
    (be & ebase & bt & txbase & bin & inbase & nI & ixv & HEnvVal & He0 & He1 & Ht0 & Ht1 & Hi0 & Hi1 &
      HLtx & HLarr & HLcnt & HLix & HnI & Hixv & HLelem & HFp)
    HSep HBf HA [HSedge HSoff] HR0 HRmax Hin HFrame.
  subst env fp.
  pose proof Hnb as Hwb.
  rewrite HB in HSep, HFrame.
  rewrite Forall_forall in HSep.
  assert (S5 : out_sep bd dbase bw outedge cursor nbits bin inbase
    (inbase + sz * Z.of_nat (length (elems_of environment))))
    by exact (HSep (bin, inbase, inbase + sz * Z.of_nat (length (elems_of environment))) ltac:(simpl; auto)).
  destruct (Hsem environment) as (x & V & Hnth & HVs & HVenc).
  assert (Hix_lt : (Bitcoin.envIx environment < length (elems_of environment))%nat)
    by (apply nth_error_Some; rewrite Hnth; discriminate).
  assert (Hlt : Int64.ltu ixv nI = true).
  { unfold Int64.ltu. rewrite zlt_true; [reflexivity|]. rewrite Hixv, HnI. lia. }
  set (nn := Z.of_nat (length (elems_of environment))) in *.
  set (szn := sz * nn) in *.
  assert (Hm : sz * Int64.unsigned ixv + sz <= szn).
  { subst szn. rewrite Hixv. assert (sz * (Z.of_nat (Bitcoin.envIx environment) + 1) <= sz * nn)
      by (apply Z.mul_le_mono_nonneg_l; subst nn; lia). lia. }
  assert (Hs0 : 0 <= sz * Int64.unsigned ixv) by (apply Z.mul_nonneg_nonneg; [lia|apply Int64.unsigned_range]).
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  set (ofs := inbase + sz * Int64.unsigned ixv + poff).
  assert (Hrep : elemrep m bin ofs x).
  { pose proof (HLelem _ x Hnth) as H. rewrite <- Hixv in H. exact H. }
  assert (HMid : bitcoin_wrapper_mid f
    (bitcoin_current_ptr_rest t1 t2 t3 ta tb tc arrfield countfield sid pexpr cid pt)
    (pcells x) (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor nbits bytes).
  { unfold bitcoin_wrapper_mid. intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    assert (Hrepc : elemrep mc bin ofs x).
    { eapply Hpres; [exact Hrep|]. intros chunk o v Hlo Hhi Hl. exact (HLP _ _ _ _ Hl). }
    assert (HSp : out_sep bd dbase bw outedge cursor nbits bin ofs (ofs + psz)).
    { eapply out_sep_range with (lo := inbase) (hi := inbase + szn); [exact S5|slia|slia]. }
    destruct (Hpay bd dbase bw outedge mc bin ofs x cursor Hrepc ltac:(slia) ltac:(slia) HSp HFrameC)
      as (me & HCallP & E).
    destruct (exec_bitcoin_current_ptr_rest (bitcoin_version_locals bl)
      (bitcoin_wrapper_temps f (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase) t1 t2 t3 ta tb tc
      arrfield countfield sid pexpr cid pt cf ofs cdelta adelta mc me be ebase bt txbase bin inbase bd dbase
      nI ixv Ha Hb Hc H1 H2 H3 H1d H2d H3d Had Hbd Hcd Hcb H32 Hpty (Hnone bl) Hsym Hfun Hty
      ltac:(unfold bitcoin_wrapper_temps; apply PTree.gss)
      ltac:(unfold bitcoin_wrapper_temps; rewrite PTree.gso by discriminate;
        rewrite PTree.gso by discriminate; apply PTree.gss)
      He0 He1 Ht0 (proj1 Hcb') ltac:(slia) (proj1 Hab) ltac:(slia) Hcf Haf
      (HLP _ _ _ _ HLtx) (HLP _ _ _ _ HLcnt) (HLP _ _ _ _ HLix) (HLP _ _ _ _ HLarr) Hlt
      (fun le' H2' H3' => Hptr _ le' mc bin inbase ixv H2' H3' Hi0 ltac:(slia)) HCallP) as [le1 HExec].
    destruct E as (c & p & fl & l & pm & vv).
    exists le1, me.
    refine (conj HExec (conj c (conj p (conj fl (conj _ (conj pm vv)))))).
    intros chunk b ofs' _ H1' H2'. exact (l chunk b ofs' H1' H2'). }
  destruct (bitcoin_wrapper_layout f
    (bitcoin_current_ptr_rest t1 t2 t3 ta tb tc arrfield countfield sid pexpr cid pt)
    (pcells x) (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor nbits bytes
    Hshape HBf HA HBytes ltac:(slia) HFrame HMid)
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, V. split; [exact HVs|].
  split; [exact HCall|]. split; [rewrite HVenc; exact HCells|]. split; [exact HPrefix|].
  rewrite HB. split; [exact HFields|]. exact HMem.
Qed.

Lemma encode_prod_word256_word32 (w : Ty.tySem Word256) (ix : Ty.tySem Word32) :
  @encode (Ty.Prod Word256 Word32) (w, ix) = @encode Word256 w ++ @encode Word32 ix.
Proof. reflexivity. Qed.

Lemma bitcoin_current_ptr_disjoint :
  list_disjoint [_dst; _src; _env] [_t'6; _t'5; _t'4; _t'3; _t'2; _t'1].
Proof.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Definition bitcoin_current_prev_outpoint_pexpr : expr :=
  Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar _t'2 (tptr (Tstruct _sigInput noattr))) (Etempvar _t'3 tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr)) _prevOutpoint
    (Tstruct _outpoint noattr)) (tptr (Tstruct _outpoint noattr)).

Lemma bitcoin_current_prev_outpoint_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_current_prev_outpoint
    (bitcoin_current_ptr_rest _t'1 _t'2 _t'3 _t'4 _t'5 _t'6 _input _numInputs _sigInput
      bitcoin_current_prev_outpoint_pexpr _prevOutpoint (Tstruct _outpoint noattr)).
Proof. repeat split; try reflexivity. apply bitcoin_current_ptr_disjoint. Qed.

Theorem bitcoin_current_prev_outpoint_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_current_prev_outpoint bitcoin_ge Bitcoin.env Ty.Unit
    (Ty.Prod Word256 Word32)
    (current_ptr_rep (fun e => sigTxIn (Bitcoin.envTx e)) outpoint_rep 160 64 0 448)
    (fun a environment => @bitcoin_current_prev_outpoint_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (bitcoin_current_ptr_local (fun e => sigTxIn (Bitcoin.envTx e)) 288 outpoint_pcells outpoint_rep
    (Ty.Prod Word256 Word32) _t'1 _t'2 _t'3 _t'4 _t'5 _t'6 _input _numInputs _sigInput _prevOutpoint
    (Tstruct _outpoint noattr) 448 0 160 64 40 bitcoin_current_prev_outpoint_pexpr f_prevOutpoint
    f_simplicity_bitcoin_current_prev_outpoint
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) ltac:(reflexivity) ltac:(intros bl; reflexivity)
    bitcoin_prevOutpoint_symbol bitcoin_prevOutpoint_funct ltac:(reflexivity)
    bitcoin_bitcoinTransaction_numInputs bitcoin_bitcoinTransaction_input
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ _ bitcoin_current_prev_outpoint_shape ltac:(reflexivity) _ _ outpoint_pcells_length).
  - intros m1 m2 b ofs x [Hr Hix] Hl. split.
    + eapply uint32_array_at_mono; [unfold outpoint_words; exact (hash256_len _)|exact Hr|].
      intros chunk o v H1 H2. apply Hl; [exact H1|lia].
    + apply (Hl Mint64 (ofs + 32) _); [lia|change (size_chunk Mint64) with 8; lia|exact Hix].
  - intros bd dbase bw outedge m' bin ofs x cur [Hr Hix] H0 HM HSep HF.
    destruct (eval_bitcoin_prevOutpoint_layout m' bin ofs bd dbase bw outedge cur (outpoint_words x)
      (outpoint_ix (sigTxiPreviousOutpoint x))
      ltac:(unfold outpoint_words; exact (hash256_len _)) H0 ltac:(lia) HSep Hr Hix HF) as (me & HC & HE).
    exists me. split; [exact HC|exact HE].
  - intros e le' m' bin inbase ixv H2 H3 Hi0 HM. unfold bitcoin_current_prev_outpoint_pexpr.
    exact (eval_bitcoin_elem_field_addr e le' m' _t'2 _t'3 _sigInput 160 _prevOutpoint 64 _outpoint bin inbase ixv
      bitcoin_sizeof_sigInput bitcoin_sigInput_prevOutpoint H2 H3 Hi0 ltac:(split; lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
  - intros environment. destruct (bitcoin_current_prev_outpoint_sem environment) as (txi & Hn & Hs).
    exists txi. eexists. split; [exact Hn|]. split; [exact Hs|].
    unfold outpoint_pcells, bitcoin_outpoint_cells, outpoint_words, outpoint_ix.
    rewrite encode_prod_word256_word32. rewrite encode_from_hash256. f_equal.
    rewrite decode_wide32_unsigned.
    + reflexivity.
    + pose proof (Int.unsigned_range (opIndex (sigTxiPreviousOutpoint txi))) as H.
      change Int.modulus with 4294967296 in H. exact H.
Qed.
