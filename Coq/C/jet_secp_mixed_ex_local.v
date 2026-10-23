(** Full original public extended mixed-addition jet against the unchanged
    fixed literal Simplicity program.  Production C, the literal program and
    the full input type are all untouched.

    The reported equal-point ratio mismatch (JET_SECP_RATIO_MISMATCHES.md) is
    handled exactly, not excluded silently:
    - [gej_ge_add_ex_normalized_local_spec]: for EVERY input the jet's output is
      the literal output whose ratio is replaced by its field normalization;
    - [gej_ge_add_ex_literal_local_spec_off_mismatch]: the jet satisfies the
      literal specification on every input outside the mismatch set;
    - [gej_ge_add_ex_mismatch_domain]: the mismatch set is exactly the
      equal-point branch with a noncanonical input Y word. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_word_repr C.jet_frame_layout C.jet_input_layout C.jet_write_layout
 C.jet_output_layout C.jet_encoding C.jet_frame_inv C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage
 C.jets_secp C.jet_secp_normalize_local C.jet_secp_add_literal C.jet_secp_mixed_ex_call
 C.jet_secp_mixed_ex_rest C.jet_secp_mixed_ex_literal_bridge C.jet_secp_mixed_dispatch_literal
 C.jet_secp_canonical_normalize C.jet_secp_canonical_zero C.jet_secp_literal_gej_predicate
 C.jet_secp_literal_add_numeric C.jet_secp_curve_literal C.jet_secp_multiply_literal_spec
 C.jet_secp_mixed_ex_counterexample C.jet_secp_fe_math C.jet_secp_literal_add_program
 C.jet_secp_literal_infinity C.jet_secp_curve_literal C.jet_secp_rescale_literal
 C.jet_secp_negate_literal_contract.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma encode_output_cells (r x y z : Ty.tySem (Word 8)) :
  Simplicity.Translate.encode (X:=Ty.Prod (Word 8) (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))) (r,((x,y),z))=
  Simplicity.Translate.encode r++((Simplicity.Translate.encode x++Simplicity.Translate.encode y)++
    Simplicity.Translate.encode z).
Proof. reflexivity. Qed.
Local Opaque literal_gej_ge_add_ex literal_gej_add_ex canonical_fe_normalize canonical_fe_is_zero
  literal_gej_is_infinity mixed_literal_h mixed_literal_i literal_fe_multiply literal_fe_negate
  literal_fe_one256 literal_fe_zero256
  Simplicity.Translate.encode.

Definition gej_ge_add_ex_input :=
  Ty.Prod (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (Ty.Prod (Word 8) (Word 8)).
Definition gej_ge_add_ex_output :=
  Ty.Prod (Word 8) (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)).

(** The contract restricted to a set of inputs; with the full set it is
    exactly [secp_jet_local_spec]. *)
Definition secp_jet_local_spec_on (P : Ty.tySem gej_ge_add_ex_input -> Prop) (f : function)
    (spec : Ty.tySem gej_ge_add_ex_input -> Ty.tySem gej_ge_add_ex_output) : Prop :=
  forall env m bd dbase bs sbase bi bw edge outedge cursor read_cursor
      (a : Ty.tySem gej_ge_add_ex_input),
    P a ->
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize gej_ge_add_ex_input) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize gej_ge_add_ex_output)) ->
    exists mf,
      Clight2.eval_funcall secp_ge m (Internal f)
        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
        E0 mf (Vint Int.one) /\
      frame_output_cells_at mf bw outedge cursor (encode (spec a)) /\
      write_prefix_at m mf bw outedge cursor /\
      frame_fields_at mf bd dbase bw outedge (cursor - Z.of_nat (bitSize gej_ge_add_ex_output)) /\
      (forall chunk b ofs, Mem.valid_block m b ->
        (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
        (b <> bw \/
          ofs + size_chunk chunk <= outedge + 8 * ((cursor - Z.of_nat (bitSize gej_ge_add_ex_output)) / 64) \/
          write_word_address outedge cursor + 8 <= ofs) ->
        Mem.load chunk mf b ofs = Mem.load chunk m b ofs).

Lemma secp_jet_local_spec_on_full f spec :
  secp_jet_local_spec f gej_ge_add_ex_input gej_ge_add_ex_output spec <->
  secp_jet_local_spec_on (fun _ => True) f spec.
Proof.
  unfold secp_jet_local_spec,secp_jet_local_spec_on;split.
  - intros H env m bd dbase bs sbase bi bw edge outedge cursor rc a _;apply H.
  - intros H env m bd dbase bs sbase bi bw edge outedge cursor rc a;apply H;exact I.
Qed.

Definition gej_ge_add_ex_literal (a : Ty.tySem gej_ge_add_ex_input) :=
  @literal_gej_ge_add_ex Alg.CoreFunSem a.

(** The reported mismatch set: the literal ratio word is not a reduced field
    element.  This is a decidable condition on the literal program's own output. *)
Definition gej_ge_add_ex_ratio_mismatch (a : Ty.tySem gej_ge_add_ex_input) : Prop :=
  feP <= @toZ (WordToZ 8) (fst (gej_ge_add_ex_literal a)).

(** The literal output with its ratio replaced by the ratio's normalization. *)
Definition gej_ge_add_ex_normalized (a : Ty.tySem gej_ge_add_ex_input) : Ty.tySem gej_ge_add_ex_output :=
  (@canonical_fe_normalize Alg.CoreFunSem (fst (gej_ge_add_ex_literal a)), snd (gej_ge_add_ex_literal a)).

Lemma gej_ge_add_ex_normalized_literal a :
  ~gej_ge_add_ex_ratio_mismatch a -> gej_ge_add_ex_normalized a=gej_ge_add_ex_literal a.
Proof.
  intro HN;unfold gej_ge_add_ex_normalized.
  rewrite canonical_fe_normalize_reduced by (unfold gej_ge_add_ex_ratio_mismatch in HN;lia).
  destruct (gej_ge_add_ex_literal a);reflexivity.
Qed.

Lemma mixed_ex_output_normalized (x y z u v : Ty.tySem (Word 8)) :
  mixed_ex_output x y z u v=encode (gej_ge_add_ex_normalized (((x,y),z),(u,v))).
Proof.
  unfold mixed_ex_output.
  pose proof (mixed_ex_reader_outputs_literal x y z u v) as H;cbv zeta in H.
  match type of H with (?r,((?x1,?y1),?z1))=_ =>
    rewrite <-(encode_output_cells r x1 y1 z1);
    exact (f_equal (Simplicity.Translate.encode (X:=Ty.Prod (Word 8) (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)))) H) end.
Qed.

Theorem gej_ge_add_ex_normalized_local_spec :
  secp_jet_local_spec f_simplicity_gej_ge_add_ex gej_ge_add_ex_input gej_ge_add_ex_output
    gej_ge_add_ex_normalized.
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HBase HAlign HSource HCursor HMax HInput HOutput.
  destruct a as [[[x y] z] [u v]].
  change (rc+1280<=Int64.max_unsigned) in HMax.
  change (write_frame_at m bd dbase bw outedge cursor 1024) in HOutput.
  change (frame_input_cells_at m bi edge rc (((encode x++encode y)++encode z)++(encode u++encode v))) in HInput.
  rewrite !frame_input_cells_at_app,!app_length,!encode_word_length in HInput.
  destruct HInput as [[[HX HY] HZ] [HU HV]].
  change (frame_input_cells_at m bi edge (rc+256) (encode y)) in HY.
  change (frame_input_cells_at m bi edge (rc+512) (encode z)) in HZ.
  change (frame_input_cells_at m bi edge (rc+768) (encode u)) in HU.
  change (frame_input_cells_at m bi edge (rc+768+256) (encode v)) in HV.
  replace (rc+768+256) with (rc+1024) in HV by lia.
  rewrite encode_word in HX,HY,HZ,HU,HV.
  destruct (eval_gej_ge_add_ex_public env m bd dbase bs sbase bw outedge cursor 1024 bi edge rc
    x y z u v HOutput ltac:(lia) HBase HAlign HSource HX HY HZ HU HV HCursor HMax)
    as (mf & HCall & HFinal & HFrame).
  rewrite mixed_ex_output_normalized in HFinal.
  destruct HFinal as (HValid & HF & HN & (HCells & HPrefix & HFields & HLoads & HPerms) & Hw).
  rewrite encode_length in HFields,HLoads.
  exists mf;split;[exact HCall|];split;[exact HCells|];split;[exact HPrefix|];split;[exact HFields|].
  intros chunk b ofs HValidB HFrameOther HOutputOther.
  destruct (Pos.eq_dec b bd) as [HD|HD];
    [apply HLoads;[split;[left;exact HD|exact HValidB]|assumption|assumption]|].
  destruct (Pos.eq_dec b bw) as [HW|HW];
    [apply HLoads;[split;[right;left;exact HW|exact HValidB]|assumption|assumption]|].
  destruct (Pos.eq_dec b bi) as [HI|HI];
    [apply HLoads;[split;[right;right;exact HI|exact HValidB]|assumption|assumption]|].
  apply (proj1 HFrame);[exact HValidB|];intros pos HPos.
  unfold extA,fext;intros [[H|[H|H]] _];contradiction.
Qed.

Theorem gej_ge_add_ex_literal_local_spec_off_mismatch :
  secp_jet_local_spec_on (fun a=>~gej_ge_add_ex_ratio_mismatch a) f_simplicity_gej_ge_add_ex
    gej_ge_add_ex_literal.
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc a HOff HBase HAlign HSource HCursor HMax HInput HOutput.
  destruct (gej_ge_add_ex_normalized_local_spec env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HBase HAlign HSource HCursor HMax HInput HOutput)
    as (mf & HCall & HCells & Rest).
  rewrite (gej_ge_add_ex_normalized_literal a HOff) in HCells.
  exists mf;split;[exact HCall|];split;[exact HCells|exact Rest].
Qed.

(** Exactly which inputs are reported: the equal-point branch (finite incoming
    point, H and I both zero modulo p) whose input Y word is not reduced. *)
Theorem gej_ge_add_ex_mismatch_domain (ax ay az bx byword : Ty.tySem (Word 8)) :
  gej_ge_add_ex_ratio_mismatch (((ax,ay),az),(bx,byword)) <->
  ((@literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt) /\
   (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)=inr tt) /\
   (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i ay az byword)=inr tt) /\
   (feP <= @toZ (WordToZ 8) ay)).
Proof.
  unfold gej_ge_add_ex_ratio_mismatch,gej_ge_add_ex_literal.
  change (@literal_gej_ge_add_ex Alg.CoreFunSem (((ax,ay),az),(bx,byword))) with
    (@literal_gej_add_ex Alg.CoreFunSem (((ax,ay),az),((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt))).
  assert (HB : @literal_gej_is_infinity Alg.CoreFunSem ((bx,byword),@literal_fe_one256 Alg.CoreFunSem tt)=inl tt)
    by (rewrite literal_gej_is_infinity_value;exact mixed_literal_one_finite).
  assert (Small : forall w : Ty.tySem (Word 8), @toZ (WordToZ 8) w < feP ->
    ~feP <= @toZ (WordToZ 8) w) by (intros w Hw;lia).
  destruct (@literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)) as [[]|[]] eqn:HA.
  - destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_h ax az bx)) as [[]|[]] eqn:HZH.
    + rewrite (literal_gej_add_ex_fst_nonzero_h ax ay az bx byword HA HZH).
      rewrite literal_multiply_numeric.
      pose proof (Z.mod_pos_bound (@toZ (WordToZ 8) (mixed_literal_h ax az bx)*@toZ (WordToZ 8)
        (@literal_fe_negate Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt))) feP
        ltac:(unfold feP,feR;lia)) as HBd.
      split;[intro Hm;lia|intros (Hc & Hh & _);discriminate Hh].
    + destruct (@canonical_fe_is_zero Alg.CoreFunSem (mixed_literal_i ay az byword)) as [[]|[]] eqn:HZI.
      * rewrite (literal_gej_add_ex_fst_zero_h_nonzero_i ax ay az bx byword HA HZH HZI).
        assert (Z0 : @toZ (WordToZ 8) (@literal_fe_zero256 Alg.CoreFunSem tt)=0)
          by (change (@toZ (WordToZ 8) (@Word.zero 8 Alg.CoreFunSem tt)=0);rewrite Word.zero_correct;reflexivity).
        rewrite Z0;split;[intro Hm;unfold feP,feR in Hm;lia|intros (_ & _ & Hi & _);discriminate Hi].
      * rewrite (literal_gej_add_ex_fst_equal_point ax ay az bx byword HA HZH HZI).
        split;[intro Hm;split;[reflexivity|split;[reflexivity|split;[reflexivity|exact Hm]]]|intros (_ & _ & _ & Hy);exact Hy].
  - assert (Z0 : @toZ (WordToZ 8) (@literal_fe_zero256 Alg.CoreFunSem tt)=0)
      by (change (@toZ (WordToZ 8) (@Word.zero 8 Alg.CoreFunSem tt)=0);rewrite Word.zero_correct;reflexivity).
    rewrite literal_gej_add_ex_fst_infinite by exact HA.
    rewrite Z0;split;[intro Hm;unfold feP,feR in Hm;lia|intros (Hc & _);discriminate Hc].
Qed.

(** The reported witness lies in the mismatch set. *)
Theorem gej_ge_add_ex_witness_is_mismatch :
  gej_ge_add_ex_ratio_mismatch extended_ratio_input.
Proof.
  pose proof extended_ratio_p_witness as W.
  rewrite canonical_field_order_matches_limb_model in W.
  unfold gej_ge_add_ex_ratio_mismatch.
  match goal with |- feP <= ?t => enough (E : t=feP) by lia;exact W end.
Qed.
