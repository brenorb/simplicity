(** Actual issuanceTokenAmt pointer selection: tokenAmt in the new-issuance
    union, or the initialized local explicit-zero object for reissuance. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Memory Events Globalenvs ClightBigstep.
Require Import C.jet_exec C.jets_elements C.jet_elements_linkage C.jet_elements_prim.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_elements_field_eval C.jet_elements_amt_helper C.jet_elements_amount_jets.
Require Import C.jet_elements_issuance_jets C.jet_elements_token_zero_init.
Require Import C.jet_elements_effects C.jet_elements_indexed_ptr.
Require Import C.jet_application_sep.
Require Import C.jet_elements_hash_helpers C.jet_elements_issuance_helper C.jet_elements_version_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition token_new_addr := Eaddrof
  (Efield (Efield (Efield
    (Ederef (Etempvar _issuance (tptr (Tstruct _assetIssuance noattr))) (Tstruct _assetIssuance noattr))
    _anon_union (Tunion __4839 noattr)) _anon_union (Tstruct __4840 noattr))
    _tokenAmt (Tstruct _confAmount noattr)) (tptr (Tstruct _confAmount noattr)).
Definition token_new_select := Sset _t'1 (Ecast token_new_addr (tptr (Tstruct _confAmount noattr))).
Definition token_local_select := Sset _t'1
  (Ecast (Eaddrof token_zero_object (tptr (Tstruct _confAmount noattr))) (tptr (Tstruct _confAmount noattr))).
Definition token_select_stmt := Sifthenelse
  (Ebinop Oeq (Econst_int Int.one tint) (Etempvar _t'3 tint) tint)
  token_new_select (Ssequence token_zero_init_stmt token_local_select).

Lemma token_select_shape :
  match fn_body f_issuanceTokenAmt with
  | Ssequence _ (Sifthenelse _ (Ssequence (Ssequence _ select) _) _) => select = token_select_stmt
  | _ => False
  end.
Proof. reflexivity. Qed.

Lemma elements_new_issuance_tokenAmt : elements_field_at __4840 _tokenAmt 32.
Proof. vm_compute; reflexivity. Qed.

Lemma token_new_addr_eval e le m bi ibase :
  0 <= ibase -> ibase + 32 <= Ptrofs.max_unsigned ->
  le!_issuance = Some (Vptr bi (Ptrofs.repr ibase)) ->
  eval_expr elements_ge e le m token_new_addr (Vptr bi (Ptrofs.repr (ibase + 32))).
Proof.
  intros H0 HM HI. unfold token_new_addr. apply eval_Eaddrof.
  rewrite <- (elements_ptr_add_repr ibase 32) by lia.
  eapply eval_elements_field_lvalue; [reflexivity|exact elements_new_issuance_tokenAmt|].
  rewrite <- (ptrofs_add0 (Ptrofs.repr ibase)).
  eapply eval_Elvalue; [|apply deref_loc_copy; reflexivity].
  eapply eval_elements_union_field_lvalue; [reflexivity|exact elements_issuance_union_new|].
  rewrite <- (ptrofs_add0 (Ptrofs.repr ibase)).
  eapply eval_Elvalue; [|apply deref_loc_copy; reflexivity].
  eapply eval_elements_field_lvalue;
    [reflexivity|exact elements_assetIssuance_union|apply eval_elements_deref_struct; exact HI].
Qed.

Definition token_get_tag := Sset _t'3 (Efield
  (Ederef (Etempvar _issuance (tptr (Tstruct _assetIssuance noattr))) (Tstruct _assetIssuance noattr)) _type tint).
Definition token_amt_call := Scall None
  (Evar _amt (Tfunction (Tcons (tptr (Tstruct _frameItem noattr))
    (Tcons (tptr (Tstruct _confAmount noattr)) Tnil)) tvoid cc_default))
  [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _t'1 (tptr (Tstruct _confAmount noattr))].
Definition token_armed_stmt := Ssequence (Ssequence token_get_tag token_select_stmt) token_amt_call.

Lemma token_armed_shape :
  match fn_body f_issuanceTokenAmt with
  | Ssequence _ (Sifthenelse _ armed _) => armed = token_armed_stmt
  | _ => False
  end.
Proof. reflexivity. Qed.

Definition token_selected_block (i : issuance) (bi bc : block) := match i with inl _ => bi | inr _ => bc end.
Definition token_selected_base (i : issuance) (ibase : Z) := match i with inl _ => ibase + 32 | inr _ => 0 end.
Definition token_selected_amount (i : issuance) : amountWith unit :=
  match i with inl new => clearPrf (newIssuanceTokenAmount new) | inr _ => Explicit Int64.zero end.
Definition token_selected_temps le i bi ibase bc := PTree.set _t'1
  (Vptr (token_selected_block i bi bc) (Ptrofs.repr (token_selected_base i ibase))) le.

Theorem exec_token_select e le m i bi ibase bc bf base bw edge cursor :
  e!___compound = Some (bc, Tstruct _confAmount noattr) ->
  le!_issuance = Some (Vptr bi (Ptrofs.repr ibase)) ->
  le!_t'3 = Some (Vint (issuance_tag (Some i))) ->
  0 <= ibase -> ibase + 72 <= Ptrofs.max_unsigned ->
  (forall new, i = inl new -> amount_rep m bi (ibase + 32) (clearPrf (newIssuanceTokenAmount new))) ->
  Mem.range_perm m bc 0 40 Cur Writable -> bc <> bf -> bc <> bw ->
  write_frame_at m bf base bw edge cursor 258 ->
  exists mi,
    Clight2.exec_stmt elements_ge e le m token_select_stmt E0 (token_selected_temps le i bi ibase bc) mi Out_normal /\
    amount_rep mi (token_selected_block i bi bc) (token_selected_base i ibase) (token_selected_amount i) /\
    write_frame_at mi bf base bw edge cursor 258 /\
    (forall chunk bb ofs, bb <> bc \/ ofs + size_chunk chunk <= 0 \/ 40 <= ofs ->
       Mem.load chunk mi bb ofs = Mem.load chunk m bb ofs) /\
    (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mi bb ofs kind p) /\
    (forall bb, Mem.valid_block m bb -> Mem.valid_block mi bb).
Proof.
  intros HE HI HT H0 HM HAmount HP Hcd Hcw HF.
  destruct i as [new|re].
  - exists m. split.
    + unfold token_select_stmt, token_selected_temps, token_selected_block, token_selected_base.
      eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
      * eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vint Int.one);
          [constructor|apply eval_Etempvar; exact HT|reflexivity].
      * reflexivity.
      * unfold token_new_select. apply exec_set. eapply eval_Ecast;
          [apply token_new_addr_eval; [exact H0|lia|exact HI]|reflexivity].
    + split; [apply HAmount; reflexivity|]. split; [exact HF|].
      split; [intros; reflexivity|]. split; auto.
  - destruct (exec_token_zero_init e le m bc HE HP) as (mi & EX & HA & HL & HPerm & HV).
    exists mi. split.
    + unfold token_select_stmt, token_selected_temps, token_selected_block, token_selected_base.
      eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
      * eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vint (Int.repr 2));
          [constructor|apply eval_Etempvar; exact HT|reflexivity].
      * reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi) (le1 := le); [exact EX|].
        unfold token_local_select. apply exec_set. eapply eval_Ecast;
          [apply eval_Eaddrof, eval_Evar_local; exact HE|reflexivity].
    + split; [exact HA|]. split.
      * eapply write_frame_at_preserved with (m := m); [|exact HPerm|exact HF].
        intros chunk bb ofs v [Hd|Hw] HLoad; rewrite HL; [exact HLoad|left; congruence|exact HLoad|left; congruence].
      * split; [exact HL|]. split; assumption.
Qed.

Lemma exec_token_amt_call e le m me bf base ba abase :
  e!_amt = None -> le!_dst = Some (Vptr bf (Ptrofs.repr base)) ->
  le!_t'1 = Some (Vptr ba (Ptrofs.repr abase)) ->
  Clight2.eval_funcall elements_ge m (Internal f_amt)
    [Vptr bf (Ptrofs.repr base); Vptr ba (Ptrofs.repr abase)] E0 me Vundef ->
  Clight2.exec_stmt elements_ge e le m token_amt_call E0 le me Out_normal.
Proof.
  intros HGlobal HD HA HC. unfold token_amt_call.
  change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (elements_symbol_block _amt) Ptrofs.zero)
    (f := Internal f_amt)
    (vargs := [Vptr bf (Ptrofs.repr base); Vptr ba (Ptrofs.repr abase)]) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact HGlobal|exact elements_amt_symbol]|
      apply deref_loc_reference; reflexivity].
  - eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
    eapply eval_Econs; [apply eval_Etempvar; exact HA|reflexivity|apply eval_Enil].
  - exact elements_amt_funct.
  - reflexivity.
  - exact HC.
Qed.

Theorem exec_token_armed e le m i bi ibase bc bf base bw edge cursor :
  e!___compound = Some (bc, Tstruct _confAmount noattr) -> e!_amt = None ->
  le!_issuance = Some (Vptr bi (Ptrofs.repr ibase)) ->
  le!_dst = Some (Vptr bf (Ptrofs.repr base)) ->
  0 <= ibase -> ibase + 280 <= Ptrofs.max_unsigned ->
  Mem.load Mint32 m bi (ibase + 272) = Some (Vint (issuance_tag (Some i))) ->
  (forall new, i = inl new -> amount_rep m bi (ibase + 32) (clearPrf (newIssuanceTokenAmount new))) ->
  Mem.range_perm m bc 0 40 Cur Writable -> bc <> bf -> bc <> bw ->
  out_sep bf base bw edge cursor 258 bi ibase (ibase + 280) ->
  write_frame_at m bf base bw edge cursor 258 ->
  exists mi me,
    Clight2.exec_stmt elements_ge e le m token_armed_stmt E0
      (token_selected_temps (PTree.set _t'3 (Vint (issuance_tag (Some i))) le) i bi ibase bc) me Out_normal /\
    write_effect mi me bf base bw edge cursor 258 (amount_pcells (token_selected_amount i)) /\
    (forall chunk bb ofs, bb <> bc \/ ofs + size_chunk chunk <= 0 \/ 40 <= ofs ->
       Mem.load chunk mi bb ofs = Mem.load chunk m bb ofs) /\
    (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mi bb ofs kind p) /\
    (forall bb, Mem.valid_block m bb -> Mem.valid_block mi bb).
Proof.
  intros HE HG HI HD H0 HM HT HA HP Hcd Hcw HSep HF.
  set (le3 := PTree.set _t'3 (Vint (issuance_tag (Some i))) le).
  assert (ET : Clight2.exec_stmt elements_ge e le m token_get_tag E0 le3 m Out_normal).
  { unfold token_get_tag, le3. apply exec_set.
    eapply eval_elements_field_value with (sid := _assetIssuance) (delta := 272) (chunk := Mint32).
    - reflexivity.
    - exact elements_assetIssuance_type.
    - reflexivity.
    - apply eval_elements_deref_struct; exact HI.
    - rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HT]. }
  destruct (exec_token_select e le3 m i bi ibase bc bf base bw edge cursor HE
    ltac:(unfold le3; rewrite PTree.gso by discriminate; exact HI)
    ltac:(unfold le3; apply PTree.gss) H0 ltac:(lia) HA HP Hcd Hcw HF)
    as (mi & ES & HR & HFi & HL & HPerm & HV).
  assert (HS : out_sep bf base bw edge cursor 258 (token_selected_block i bi bc)
    (token_selected_base i ibase) (token_selected_base i ibase + 40)).
  { destruct i as [new|re]; cbn [token_selected_block token_selected_base].
    - eapply out_sep_range; [exact HSep|lia|lia].
    - split; left; assumption. }
  assert (HB : 0 <= token_selected_base i ibase /\ token_selected_base i ibase + 40 <= Ptrofs.max_unsigned).
  { destruct i; cbn [token_selected_base]; [split; lia|].
    change (0 <= 0 /\ 0 + 40 <= 18446744073709551615); lia. }
  destruct (amount_rep_runs bf base bw edge mi (token_selected_block i bi bc) (token_selected_base i ibase)
    (token_selected_amount i) cursor HR (proj1 HB) (proj2 HB) HS HFi) as (me & HC & WE).
  exists mi, me. split.
  - unfold token_armed_stmt.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi)
      (le1 := token_selected_temps le3 i bi ibase bc).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le3); eauto.
    + eapply exec_token_amt_call; [exact HG| | |exact HC].
      * unfold token_selected_temps, le3. rewrite !PTree.gso by discriminate. exact HD.
      * unfold token_selected_temps. apply PTree.gss.
  - split; [exact WE|]. split; [exact HL|]. split; assumption.
Qed.
