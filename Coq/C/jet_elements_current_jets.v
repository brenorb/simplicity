(** Ported from [jet_bitcoin_current_jets] (generic scalar theorem and the
    sequence instance; Elements has no InputValue primitive).

    Actual Elements current_sequence jet against the literal
    canonical program [CurrentIndex >>> assert (InputSequence)].  All environment
    loads precede the single output write, so no footprint premise is needed
    and the plain application contract applies. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option C.jet_elements_prim.
Require Import C.jet_application_contract C.jet_frame_copy C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_wide C.jet_wide_spec.
Require Import C.jet_encoding C.jet_input_layout C.jets_elements C.jet_elements_linkage C.jet_exec.
Require C.jets.
Require Import C.jet_elements_version_exec C.jet_elements_field_eval C.jet_elements_wrapper.
Require Import C.jet_elements_effects C.jet_elements_transport C.jet_elements_call C.jet_elements_index_eval.
Require Import C.jet_elements_steps C.jet_elements_current_exec C.jet_elements_current_spec.
Require Import C.jet_elements_indexed_exec C.jet_elements_indexed_scalar_jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.

Lemma wide_bitsize s : Z.of_nat (bitSize (Word (wide_log s))) = wide_bits s.
Proof. destruct s; reflexivity. Qed.

Definition current_scalar_rep {A} (elems_of : Elements.env -> list A) (valz : A -> Z)
    (sz voff adelta cdelta : Z) (m : mem) (env : val) (environment : Elements.env) : Prop :=
  exists be ebase bt txbase bin inbase nI ixv,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
    0 <= txbase /\ txbase + 760 <= Ptrofs.max_unsigned /\
    0 <= inbase /\ inbase + sz * Z.of_nat (length (elems_of environment)) <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) /\
    Mem.load Mptr m bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) /\
    Mem.load Mint64 m bt (txbase + cdelta) = Some (Vlong nI) /\
    Mem.load Mint64 m be (ebase + 80) = Some (Vlong ixv) /\
    Int64.unsigned nI = Z.of_nat (length (elems_of environment)) /\
    Int64.unsigned ixv = Z.of_nat (Elements.envIx environment) /\
    (forall j x, nth_error (elems_of environment) j = Some x ->
      Mem.load Mint64 m bin (inbase + sz * Z.of_nat j + voff) = Some (Vlong (Int64.repr (valz x)))).

Ltac slia :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch type of T with
      | Prop =>
          lazymatch T with
          | @eq Z _ _ => fail
          | @eq nat _ _ => fail
          | le _ _ => fail
          | lt _ _ => fail
          | Z.le _ _ => fail
          | Z.lt _ _ => fail
          | Z.ge _ _ => fail
          | Z.gt _ _ => fail
          | not (Z.lt _ _) => fail
          | not (Z.le _ _) => fail
          | and (Z.le _ _) (Z.le _ _) => fail
          | and (Z.lt _ _) (Z.le _ _) => fail
          | and (Z.le _ _) (Z.lt _ _) => fail
          | _ => clear H
          end
      | _ => fail
      end
  end; lia.

Theorem elements_current_scalar_local {A} (s : wide_size) (elems_of : Elements.env -> list A) (valz : A -> Z)
    (specv : A -> Ty.tySem (Word (wide_log s)))
    (t1 t2 t3 t4 t5 t6 t7 arrfield countfield sid wid : ident) (cdelta adelta sz voff : Z) (ve : expr)
    (wf f : function)
    (H5 : t5 <> _env) (H6 : t6 <> _env) (H7 : t7 <> _env) (H1 : t1 <> _env) (H2 : t2 <> _env) (H3 : t3 <> _env)
    (H1d : t1 <> _dst) (H2d : t2 <> _dst) (H3d : t3 <> _dst) (H4d : t4 <> _dst) (H5d : t5 <> _dst)
    (H6d : t6 <> _dst) (H7d : t7 <> _dst) (H76 : t7 <> t6) (H32 : t3 <> t2)
    (Hwin : In (wid, wf) elements_core_helpers) (Hwty : type_of_fundef (Internal wf) =
      Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default)
    (Hwnone : forall bl, (elements_version_locals bl)!wid = None) (Hwf : wf = wide_writer s)
    (Hcf : elements_field_at _elementsTransaction countfield cdelta)
    (Haf : elements_field_at _elementsTransaction arrfield adelta)
    (Hcb : 0 <= cdelta /\ cdelta + 8 <= 760) (Hab : 0 <= adelta /\ adelta + 8 <= 760)
    (Hsz : 0 < sz <= 1000) (Hvoff : 0 <= voff /\ voff + 8 <= sz)
    (Hspec : forall x, decode_wide s (Int64.zero_ext (wide_bits s) (Int64.repr (valz x))) = specv x)
    (Hval : forall e le' m' bin inbase ixv v,
      le'!t2 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!t3 = Some (Vlong ixv) ->
      0 <= inbase -> inbase + sz * Int64.unsigned ixv + voff + 8 <= Ptrofs.max_unsigned ->
      Mem.load Mint64 m' bin (inbase + sz * Int64.unsigned ixv + voff) = Some (Vlong v) ->
      eval_expr elements_ge e le' m' ve (Vlong v))
    (Hshape : elements_wrapper_shape f (elements_current_rest t1 t2 t3 t4 t5 t6 t7 arrfield countfield sid ve wid))
    (spec : Ty.tySem Ty.Unit -> Elements.env -> option (Ty.tySem (Word (wide_log s))))
    (Hsem : forall environment, exists x, nth_error (elems_of environment) (Elements.envIx environment) = Some x /\
      spec tt environment = Some (specv x)) :
  application_jet_local_spec f elements_ge Elements.env Ty.Unit (Word (wide_log s))
    (current_scalar_rep elems_of valz sz voff adelta cdelta) spec.
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor []
    (be & ebase & bt & txbase & bin & inbase & nI & ixv & HEnvVal & He0 & He1 & Ht0 & Ht1 & Hi0 & Hi1 &
      HLtx & HLarr & HLcnt & HLix & HnI & Hixv & HLelem)
    HB HA [HSedge HSoff] HR0 HRmax Hin HFrame.
  subst env wf.
  pose proof (wide_bits_bounds s) as Hwb.
  assert (HC : Z.of_nat (bitSize (Word (wide_log s))) = wide_bits s) by apply wide_bitsize.
  rewrite HC in HFrame.
  destruct (Hsem environment) as (x & Hnth & Hspecx).
  assert (Hix_lt : (Elements.envIx environment < length (elems_of environment))%nat)
    by (apply nth_error_Some; rewrite Hnth; discriminate).
  assert (Hlt : Int64.ltu ixv nI = true).
  { unfold Int64.ltu. rewrite zlt_true; [reflexivity|]. rewrite Hixv, HnI. lia. }
  set (nn := Z.of_nat (length (elems_of environment))) in *.
  set (szn := sz * nn) in *.
  assert (Hm : sz * Int64.unsigned ixv + sz <= szn).
  { subst szn. rewrite Hixv. assert (sz * (Z.of_nat (Elements.envIx environment) + 1) <= sz * nn)
      by (apply Z.mul_le_mono_nonneg_l; subst nn; lia). lia. }
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  set (v := Int64.repr (valz x)).
  assert (Hv : Mem.load Mint64 m bin (inbase + sz * Int64.unsigned ixv + voff) = Some (Vlong v)).
  { rewrite Hixv. exact (HLelem _ x Hnth). }
  assert (HMid : elements_wrapper_mid f
    (elements_current_rest t1 t2 t3 t4 t5 t6 t7 arrfield countfield sid ve wid)
    (encode (specv x)) (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor (wide_bits s) bytes).
  { unfold elements_wrapper_mid. intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    destruct (elements_write_wide_step s mc bd dbase bw outedge cursor v HFrameC)
      as (me & HCallW & E).
    destruct (exec_elements_current_rest (elements_version_locals bl)
      (elements_wrapper_temps f (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase) t1 t2 t3 t4 t5 t6 t7
      arrfield countfield sid ve wid (wide_writer s) cdelta adelta mc me be ebase bt txbase bin inbase bd dbase
      nI ixv v H5 H6 H7 H1 H2 H3 H1d H2d H3d H4d H5d H6d H7d H76 H32 Hwin Hwty (Hwnone bl)
      ltac:(unfold elements_wrapper_temps; apply PTree.gss)
      ltac:(unfold elements_wrapper_temps; rewrite PTree.gso by discriminate;
        rewrite PTree.gso by discriminate; apply PTree.gss)
      He0 He1 Ht0 (proj1 Hcb) ltac:(slia) (proj1 Hab) ltac:(slia) Hcf Haf
      (HLP _ _ _ _ HLtx) (HLP _ _ _ _ HLcnt) (HLP _ _ _ _ HLix) (HLP _ _ _ _ HLarr) Hlt
      (fun le' H2' H3' => Hval _ le' mc bin inbase ixv v H2' H3' Hi0 ltac:(slia) (HLP _ _ _ _ Hv))
      HCallW) as [le1 HExec].
    destruct E as (c & p & fl & l & pm & vv).
    assert (Hd : decode_wide s (Int64.zero_ext (wide_bits s) v) = specv x) by (subst v; apply Hspec).
    rewrite Hd in c.
    exists le1, me.
    refine (conj HExec (conj c (conj p (conj fl (conj _ (conj pm vv)))))).
    intros chunk b ofs _ H1' H2'. exact (l chunk b ofs H1' H2'). }
  destruct (elements_wrapper_layout f
    (elements_current_rest t1 t2 t3 t4 t5 t6 t7 arrfield countfield sid ve wid)
    (encode (specv x)) (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor (wide_bits s) bytes
    Hshape HB HA HBytes ltac:(slia) HFrame HMid)
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (specv x). split; [exact Hspecx|].
  split; [exact HCall|]. split; [exact HCells|]. split; [exact HPrefix|].
  rewrite HC. split; [exact HFields|]. exact HMem.
Qed.

Lemma elements_current_disjoint :
  list_disjoint [_dst; _src; _env] [_t'7; _t'6; _t'5; _t'4; _t'3; _t'2; _t'1].
Proof.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Definition elements_current_sequence_elem : expr :=
  Efield (Ederef (Ebinop Oadd (Etempvar _t'2 (tptr (Tstruct _sigInput noattr))) (Etempvar _t'3 tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr)) _sequence tulong.

Lemma elements_current_sequence_shape :
  elements_wrapper_shape f_simplicity_current_sequence
    (elements_current_rest _t'1 _t'2 _t'3 _t'4 _t'5 _t'6 _t'7 _input _numInputs _sigInput
      elements_current_sequence_elem _simplicity_write32).
Proof. repeat split; try reflexivity. apply elements_current_disjoint. Qed.

Definition elements_current_sequence_spec {alg : Primitive.Algebra} : alg Ty.Unit Word32 :=
  elements_current_spec (@elements_input_sequence_spec alg).

Definition elements_current_sequence_specv (txi : sigTxInput) : Ty.tySem (Word (wide_log W32)) :=
  @fromZ (WordToZ 5) (Int.unsigned (sigTxiSequence txi)).

Theorem elements_current_sequence_local_spec :
  application_jet_local_spec f_simplicity_current_sequence elements_ge Elements.env Ty.Unit Word32
    (current_scalar_rep (fun e => sigTxIn (Elements.envTx e)) (fun txi => Int.unsigned (sigTxiSequence txi))
      544 248 0 696)
    (fun a environment => @elements_current_sequence_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_current_scalar_local W32 (fun e => sigTxIn (Elements.envTx e))
    (fun txi => Int.unsigned (sigTxiSequence txi)) elements_current_sequence_specv
    _t'1 _t'2 _t'3 _t'4 _t'5 _t'6 _t'7 _input _numInputs _sigInput _simplicity_write32 696 0 544 248
    elements_current_sequence_elem jets.f_simplicity_write32 f_simplicity_current_sequence
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(helper_in) ltac:(reflexivity) ltac:(intros bl; reflexivity) ltac:(reflexivity)
    elements_elementsTransaction_numInputs elements_elementsTransaction_input
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ elements_current_sequence_shape _ _).
  - intros x. unfold elements_current_sequence_specv. apply decode_wide32_unsigned.
    pose proof (Int.unsigned_range (sigTxiSequence x)) as H. change Int.modulus with 4294967296 in H. exact H.
  - intros e le' m' bin inbase ixv v H2 H3 Hi0 HM HL.
    exact (eval_elements_elem_field_at e le' m' _t'2 _t'3 _sigInput 544 _sequence 248 bin inbase ixv v
      elements_sizeof_sigInput elements_sigInput_sequence H2 H3 Hi0 ltac:(split; lia) ltac:(lia) HM HL).
  - intros environment.
    exact (elements_current_sem (fun a e => @elements_input_sequence_spec (PrimitivePrimSem option_Monad_Zero) a e)
      elements_current_sequence_specv (fun a e => elements_input_sequence_sem e a) environment).
Qed.
