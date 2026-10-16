(** Input-independent physical environment relation for output_null_datum.
    Only actual C fields/cache words and their footprints are constrained. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_prim.
Require Import C.jet_elements_null_data_loads C.jet_elements_null_data_small C.jet_elements_null_data_opcode.
Require Import C.jet_elements_null_data_output_guard C.jet_elements_null_data_index C.jet_elements_null_data_guard_compose.
Require Import C.jet_elements_null_data_layout C.jet_elements_null_data_bitmachine.
Require Import C.jet_application_sep C.jet_elements_indexed_ptr C.jet_uint32_array_init C.jet_bitmachine_rep.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Local Notation OpcodeTy := (Ty.Sum (Ty.Prod (Word 1) (Word 8)) (Ty.Sum (Ty.Sum Ty.Unit Ty.Unit) (Word 2))).

Definition elements_null_data_script_flag (s : script) : bool :=
  match txNullData s with Some _ => true | None => false end.

Definition elements_null_data_opcode_environment m bout outbase k
    (parsed : list (txNullDatumF (list byte))) (fp : list (block * Z * Z)) : Prop :=
  Z.of_nat (length parsed) <= Int64.max_unsigned /\
  Mem.load Mint64 m bout (outbase + 248 * Z.of_nat k + 232) = Some (Vlong (Int64.repr (Z.of_nat (length parsed)))) /\
  forall j d, nth_error parsed j = Some d ->
    exists bop opbase,
      0 <= opbase /\ opbase + 36 * Z.of_nat j + 36 <= Ptrofs.max_unsigned /\
      Mem.load Mptr m bout (outbase + 248 * Z.of_nat k + 224) = Some (Vptr bop (Ptrofs.repr opbase)) /\
      Mem.load Mint32 m bop (opbase + 36 * Z.of_nat j + 32) =
        Some (Vint (elements_datum_code (mapNullDatum byteStringHash d))) /\
      In (bop, opbase + 36 * Z.of_nat j + 32, opbase + 36 * Z.of_nat j + 36) fp /\
      (if elements_datum_push (mapNullDatum byteStringHash d) then
        uint32_array_at m bop (opbase + 36 * Z.of_nat j)
          (hash256_reg (elements_datum_hash (mapNullDatum byteStringHash d) (byteStringHash []))) /\
        In (bop, opbase + 36 * Z.of_nat j, opbase + 36 * Z.of_nat j + 32) fp
       else True).

Definition elements_null_data_output_environment m bt txbase bout outbase k
    (txo : txOutput) (fp : list (block * Z * Z)) : Prop :=
  0 <= outbase /\ outbase + 248 * Z.of_nat k + 241 <= Ptrofs.max_unsigned /\
  Mem.load Mptr m bt (txbase + 8) = Some (Vptr bout (Ptrofs.repr outbase)) /\
  Mem.load Mint8unsigned m bout (outbase + 248 * Z.of_nat k + 240) =
    Some (Vint (if elements_null_data_script_flag (txoScript txo) then Int.one else Int.zero)) /\
  In (bt, txbase + 8, txbase + 16) fp /\
  In (bout, outbase + 248 * Z.of_nat k + 224, outbase + 248 * Z.of_nat k + 241) fp /\
  match txNullData (txoScript txo) with
  | Some parsed => elements_null_data_opcode_environment m bout outbase k parsed fp
  | None => True
  end.

Definition elements_null_data_environment_rep m env (environment : Elements.env) fp : Prop :=
  exists be ebase bt txbase bout outbase,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 8 <= Ptrofs.max_unsigned /\
    0 <= txbase /\ txbase + 712 <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) /\
    Mem.load Mint64 m bt (txbase + 704) =
      Some (Vlong (Int64.repr (Z.of_nat (length (sigTxOut (Elements.envTx environment)))))) /\
    In (be, ebase, ebase + 8) fp /\ In (bt, txbase + 704, txbase + 712) fp /\
    forall k txo, nth_error (sigTxOut (Elements.envTx environment)) k = Some txo ->
      elements_null_data_output_environment m bt txbase bout outbase k txo fp.

Lemma elements_null_data_footprint_sub fp bd dbase bw edge cur b lo hi lo' hi' :
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 261 b lo hi) fp ->
  In (b, lo, hi) fp -> lo <= lo' -> hi' <= hi -> out_sep bd dbase bw edge cur 261 b lo' hi'.
Proof.
  intros HS HI HL HH. eapply out_sep_range; [|exact HL|exact HH].
  rewrite Forall_forall in HS. exact (HS _ HI).
Qed.

Lemma elements_null_data_output_count_bound environment :
  Z.of_nat (length (sigTxOut (Elements.envTx environment))) <= Int64.max_unsigned.
Proof.
  pose proof (sigTxOutBounds (Elements.envTx environment)) as H.
  rewrite Zlength_correct in H.
  change (0 <= Z.of_nat (length (sigTxOut (Elements.envTx environment))) < 4294967296) in H.
  change (Z.of_nat (length (sigTxOut (Elements.envTx environment))) <= 18446744073709551615). lia.
Qed.

Lemma elements_null_data_environment_specialize m env environment fp bd dbase bw edge cur (iw jw : Ty.tySem Word32) :
  elements_null_data_environment_rep m env environment fp ->
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 261 b lo hi) fp ->
  exists be ebase bt txbase bout outbase count flag parsed,
    env = Vptr be (Ptrofs.repr ebase) /\
    elements_null_data_output_rep m be ebase bt txbase bout outbase (Int64.repr (toZ iw)) count flag /\
    (andb (Int64.ltu (Int64.repr (toZ iw)) count) flag = true ->
      elements_null_data_bm_environment_case m bd dbase bw edge cur
        be ebase bt txbase bout outbase (Int64.repr (toZ iw)) jw parsed (byteStringHash [])) /\
    (match nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ iw)) with
     | Some txo => txNullData (txoScript txo)
     | None => None
     end) = (if andb (Int64.ltu (Int64.repr (toZ iw)) count) flag then Some parsed else None).
Proof.
  intros (be & ebase & bt & txbase & bout & outbase & Henv & He0 & HeM & Ht0 & HtM & LE & LC & IE & IC & HOutputs) HS.
  set (outputs := sigTxOut (Elements.envTx environment)) in *.
  set (count := Int64.repr (Z.of_nat (length outputs))) in *.
  set (i := Int64.repr (toZ iw)). set (k := Z.to_nat (toZ iw)).
  assert (HI : Int64.unsigned i = Z.of_nat k).
  { unfold i, k. rewrite word32_int64_unsigned, Z2Nat.id; [reflexivity|].
    pose proof (word32_int64_unsigned iw). pose proof (Int64.unsigned_range (Int64.repr (toZ iw))). lia. }
  pose proof (int64_index_below_list_length outputs i (elements_null_data_output_count_bound environment)) as Htest.
  fold count in Htest. unfold i in Htest. rewrite word32_int64_unsigned in Htest. fold k in Htest. fold i in Htest.
  exists be, ebase, bt, txbase, bout, outbase, count.
  destruct (nth_error outputs k) as [txo|] eqn:HO.
  - destruct (HOutputs k txo HO) as (Ho0 & HoM & LP & LF & IP & IF & HParsed).
    destruct (txNullData (txoScript txo)) as [parsed|] eqn:HN.
    + exists true, parsed. split; [exact Henv|]. split.
      * unfold elements_null_data_output_rep. do 4 (split; [assumption|]).
        split; [exact LE|]. split; [exact LC|]. intros _.
        split; [exact Ho0|]. split; [rewrite HI; exact HoM|]. split; [exact LP|].
        rewrite HI. unfold elements_null_data_script_flag in LF. rewrite HN in LF. exact LF.
      * split.
        -- intros _. destruct HParsed as (Hlen & LCount & HOpcode).
           unfold elements_null_data_bm_environment_case. split; [exact Hlen|]. split.
           ++ unfold elements_null_data_count_path. do 4 (split; [lia|]).
              split; [exact Ho0|]. split; [rewrite HI; lia|].
              split; [exact LE|]. split; [exact LP|]. rewrite HI. exact LCount.
           ++ split.
              ** unfold elements_null_data_count_footprint. rewrite HI.
                 constructor; [eapply elements_null_data_footprint_sub; [exact HS|exact IE|lia|lia]|].
                 constructor; [eapply elements_null_data_footprint_sub; [exact HS|exact IP|lia|lia]|].
                 constructor; [eapply elements_null_data_footprint_sub; [exact HS|exact IF|lia|lia]|constructor].
              ** intros d HD.
                 set (j := Int64.repr (toZ jw)) in *.
                 specialize (HOpcode (Z.to_nat (Int64.unsigned j)) d HD)
                   as (bop & opbase & Hp0 & HpM & LOp & LCode & ICode & HHash).
                 rewrite Z2Nat.id in HpM, LCode, ICode, HHash by (pose proof (Int64.unsigned_range j); lia).
                 exists bop, opbase. split.
                 --- unfold elements_null_data_path_valid. do 4 (split; [lia|]).
                     split; [exact Ho0|]. split; [rewrite HI; lia|]. split; [exact Hp0|]. split; [exact HpM|].
                     unfold elements_null_data_path_loads. rewrite HI. repeat split; assumption.
                 --- split.
                     +++ unfold elements_null_data_path_footprint. rewrite HI.
                         constructor; [eapply elements_null_data_footprint_sub; [exact HS|exact IE|lia|lia]|].
                         constructor; [eapply elements_null_data_footprint_sub; [exact HS|exact IP|lia|lia]|].
                         constructor; [eapply elements_null_data_footprint_sub; [exact HS|exact IF|lia|lia]|].
                         constructor; [eapply elements_null_data_footprint_sub; [exact HS|exact ICode|lia|lia]|constructor].
                     +++ destruct (elements_datum_push (mapNullDatum byteStringHash d)); [|exact I].
                         destruct HHash as [HA IH]. split; [exact HA|].
                         eapply elements_null_data_footprint_sub; [exact HS|exact IH|lia|lia].
        -- rewrite Htest. reflexivity.
    + exists false, []. split; [exact Henv|]. split.
      * unfold elements_null_data_output_rep. do 4 (split; [assumption|]).
        split; [exact LE|]. split; [exact LC|]. intros _.
        split; [exact Ho0|]. split; [rewrite HI; exact HoM|]. split; [exact LP|].
        rewrite HI. unfold elements_null_data_script_flag in LF. rewrite HN in LF. exact LF.
      * split; [intros HG; rewrite Htest in HG; discriminate|]. rewrite Htest. reflexivity.
  - exists false, []. split; [exact Henv|]. split.
    + eapply elements_null_data_output_rep_out_of_range; [exact Htest|eassumption..].
    + split; [intros HG; rewrite Htest in HG; discriminate|]. rewrite Htest. reflexivity.
Qed.

Theorem elements_output_null_datum_environment_bitmachine environment env fp (iw jw : Ty.tySem Word32) m L s tail :
  elements_null_data_environment_rep m env environment fp ->
  Forall (fun '(b, lo, hi) => out_sep (frames_blk L) (item_ofs (active_write_loc L))
    (cells_blk L) (edge_ofs (active_write_loc L)) (Z.of_nat (writeEmpty (activeWriteFrame s))) 261 b lo hi) fp ->
  bm_rep m L s -> bm_separated L s -> active_write_writable m L s ->
  nextData (activeReadFrame s) = @encode (Ty.Prod Word32 Word32) (iw, jw) ++ tail ->
  (261 <= writeEmpty (activeWriteFrame s))%nat ->
  exists mf value,
    @elements_output_null_datum_spec (PrimitivePrimSem option_Monad_Zero) (iw, jw) environment = Some value /\
    Clight2.eval_funcall elements_ge m (Internal f_simplicity_output_null_datum)
      (jet_args env L) E0 mf (Vint Int.one) /\
    bm_rep mf L (bm_state_after_output s (@encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit OpcodeTy)) value)).
Proof.
  intros HRep HEnvSep HBM HSep HWrite HNext HSpace.
  destruct (elements_null_data_environment_specialize m env environment fp
    (frames_blk L) (item_ofs (active_write_loc L)) (cells_blk L) (edge_ofs (active_write_loc L))
    (Z.of_nat (writeEmpty (activeWriteFrame s))) iw jw HRep HEnvSep)
    as (be & ebase & bt & txbase & bout & outbase & count & flag & parsed & HE & HOutput & HCase & HLogical).
  subst env. eapply elements_output_null_datum_bitmachine;
    [exact HBM|exact HSep|exact HWrite|exact HNext|exact HSpace|exact HOutput|exact HCase|exact HLogical].
Qed.
