(** Readers on an already-initialized local frame, without a second allocation/copy. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Maps Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jets_elements C.jet_elements_linkage C.jet_exec C.jet_elements_transport C.jet_elements_call.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_wide C.jet_complement_wide_layout.
Require Import C.jet_elements_read_step C.jet_elements_indexed_exec C.jet_elements_null_data_small.
Require C.jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge ge0.
Set Default Timeout 10.

Theorem eval_elements_current_reader s m bf base bi edge rc (x : Ty.tySem (Word (wide_log s))) :
  frame_base_valid base -> 0 <= rc <= Int64.max_unsigned - wide_bits s ->
  frame_fields_at m bf base bi edge rc -> frame_input_word_at m bi edge rc x ->
  Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bi ->
  exists mr r,
    Clight2.eval_funcall elements_ge m (Internal (wide_reader s)) [Vptr bf (Ptrofs.repr base)] E0 mr (Vlong r) /\
    Int64.unsigned r = @toZ (WordToZ (wide_log s)) x /\
    frame_fields_at mr bf base bi edge (rc + wide_bits s) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mr b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mr b).
Proof.
  intros HB Hrc HF HI HP HD.
  destruct (eval_read_wide_word_at s m bf base bi edge rc x HB Hrc HF HI HP HD)
    as (mr & r & HC & HR & HFields & HLoads & HPerm & HValid).
  exists mr, r. split.
  - destruct (wide_reader_helper s) as (id & Hhelper). eapply elements_transport_call; eauto.
  - exact (conj HR (conj HFields (conj HLoads (conj HPerm HValid)))).
Qed.

Definition elements_read32_current_stmt (ret target : ident) : statement :=
  Ssequence
    (Scall (Some ret)
      (Evar _simplicity_read32 (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil) tulong cc_default))
      [Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))])
    (Sset target (Etempvar ret tulong)).

Theorem exec_elements_read32_current ret target e le m bl bi edge rc (x : Ty.tySem Word32) :
  e!_simplicity_read32 = None -> e!_src = Some (bl, Tstruct _frameItem noattr) ->
  0 <= rc <= Int64.max_unsigned - 32 ->
  frame_fields_at m bl 0 bi edge rc -> frame_input_word_at m bi edge rc x ->
  Mem.valid_access m Mint64 bl 8 Writable -> bl <> bi ->
  exists mr r,
    Clight2.exec_stmt elements_ge e le m (elements_read32_current_stmt ret target) E0
      (PTree.set target (Vlong r) (PTree.set ret (Vlong r) le)) mr Out_normal /\
    Int64.unsigned r = @toZ (WordToZ 5) x /\ frame_fields_at mr bl 0 bi edge (rc + 32) /\
    (forall chunk b ofs, b <> bl \/ ofs + size_chunk chunk <= 8 \/ 16 <= ofs ->
      Mem.load chunk mr b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mr b).
Proof.
  intros HRd HSrc Hrc HF HI HP HD.
  assert (HB : frame_base_valid 0) by (split; [lia|change (16 <= 18446744073709551615); lia]).
  destruct (eval_elements_current_reader W32 m bl 0 bi edge rc x HB Hrc HF HI HP HD)
    as (mr & r & HC & HV & HF' & HM & HPerm & HValid).
  exists mr, r. split.
  - unfold elements_read32_current_stmt.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := PTree.set ret (Vlong r) le).
    + eapply exec_elements_helper_call with (id := _simplicity_read32) (f := jets.f_simplicity_read32)
        (vargs := [Vptr bl Ptrofs.zero]) (vres := Vlong r).
      * unfold elements_core_helpers; simpl; tauto.
      * exact HRd.
      * eapply eval_Econs; [apply eval_Eaddrof; apply eval_Evar_local; exact HSrc|reflexivity|apply eval_Enil].
      * reflexivity.
      * exact HC.
    + apply exec_set, eval_Etempvar, PTree.gss.
  - exact (conj HV (conj HF' (conj HM (conj HPerm HValid)))).
Qed.

Lemma elements_first_read32_source : elements_read32_current_stmt _t'1 _i = elements_indexed_head.
Proof. reflexivity. Qed.

Fixpoint elements_find_read32_prefix (ret : ident) (s : statement) : option statement :=
  match s with
  | Ssequence a b =>
      match a with
      | Scall (Some id) (Evar fn _) _ =>
          if Pos.eqb ret id && Pos.eqb fn _simplicity_read32 then Some s else
            elements_stmt_first (elements_find_read32_prefix ret a) (elements_find_read32_prefix ret b)
      | _ => elements_stmt_first (elements_find_read32_prefix ret a) (elements_find_read32_prefix ret b)
      end
  | Sifthenelse _ a b | Sloop a b =>
      elements_stmt_first (elements_find_read32_prefix ret a) (elements_find_read32_prefix ret b)
  | _ => None
  end.

Lemma elements_second_read32_source :
  elements_find_read32_prefix _t'2 (fn_body f_simplicity_output_null_datum) =
    Some (elements_read32_current_stmt _t'2 _j).
Proof. reflexivity. Qed.
