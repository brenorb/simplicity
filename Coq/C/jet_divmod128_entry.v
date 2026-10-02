(** Actual four-local LP64 function entry, source copy, readers and static
    helper-call boundaries. Initial-only public jet execution remains separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_wide C.jet_binary_wide_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition divmod128_env bl bqh bql br :=
  PTree.set _r (br,tulong) (PTree.set _ql (bql,tulong) (PTree.set _qh (bqh,tulong) (e_one8 bl))).
Definition divmod128_temps env bd dbase bs sbase :=
  le_arith8_layout env f_simplicity_div_mod_128_64 bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase).

Lemma divmod128_entry env m ma mb mc md bl bqh bql br bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma, bl) -> Mem.alloc ma 0 8 = (mb, bqh) ->
  Mem.alloc mb 0 8 = (mc, bql) -> Mem.alloc mc 0 8 = (md, br) ->
  function_entry2 ge0 f_simplicity_div_mod_128_64
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
    m (divmod128_env bl bqh bql br) (divmod128_temps env bd dbase bs sbase) md.
Proof.
  intros HA HB HC HD. constructor.
  - change (list_norepet [_src; _qh; _ql; _r]). vm_compute.
    repeat (apply list_norepet_cons; [simpl; intuition discriminate|]). constructor.
  - change (list_norepet [_dst; _src; _env]). unfold _dst, _src, _env.
    repeat constructor; simpl; intuition discriminate.
  - intros i j HI HJ Heq. cbn in HI, HJ. subst j.
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
      vm_compute in *; congruence.
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma, bl)); exact HA.
    + eapply alloc_variables_cons with (m1 := mb) (b1 := bqh).
      * change (Mem.alloc ma 0 8 = (mb, bqh)); exact HB.
      * eapply alloc_variables_cons with (m1 := mc) (b1 := bql).
        -- change (Mem.alloc mb 0 8 = (mc, bql)); exact HC.
        -- eapply alloc_variables_cons with (m1 := md) (b1 := br).
           ++ change (Mem.alloc mc 0 8 = (md, br)); exact HD.
           ++ constructor.
  - reflexivity.
Qed.

Lemma exec_divmod128_source_copy m mc bl bqh bql br bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt ge0 (divmod128_env bl bqh bql br) le m
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    E0 le mc Out_normal.
Proof.
  intros HB HS HD HL Hload Hstore.
  assert (HA : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr. unfold frame_base_valid in HB; lia. }
  eapply exec_Sassign_copy.
  - apply eval_Evar_local. unfold divmod128_env. rewrite !PTree.gso by discriminate. reflexivity.
  - apply eval_Etempvar; exact HL.
  - reflexivity.
  - eapply assign_frameItem_copy.
    + reflexivity.
    + intros _. rewrite HA; exact HS.
    + intros _. exists 0; reflexivity.
    + left; exact HD.
    + rewrite HA; exact Hload.
    + exact Hstore.
Qed.

Lemma call_divmod128_read s result le m mr bl bqh bql br w :
  Clight2.eval_funcall ge0 m (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr (Vlong w) ->
  Clight2.exec_stmt ge0 (divmod128_env bl bqh bql br) le m (wide_binary_read s result)
    E0 (PTree.set result (Vlong w) le) mr Out_normal.
Proof.
  intros Hread. eapply exec_Scall with (vf := Vptr (jet_symbol_block (wide_reader_id s)) Ptrofs.zero)
    (vargs := [Vptr bl Ptrofs.zero]) (f := Internal (wide_reader s)) (vres := Vlong w).
  - reflexivity.
  - eapply eval_Elvalue.
    + apply eval_Evar_global; [destruct s; reflexivity|apply wide_reader_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof. apply eval_Evar_local.
      unfold divmod128_env. rewrite !PTree.gso by discriminate. reflexivity.
    + reflexivity.
    + apply eval_Enil.
  - apply wide_reader_funct.
  - destruct s; reflexivity.
  - exact Hread.
Qed.

Definition divmod128_helper_call idq idah idal := Scall None
  (Evar _div_mod_96_64 (Tfunction
    (Tcons (tptr tulong) (Tcons (tptr tulong) (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))))
    tvoid cc_default))
  [Eaddrof (Evar idq tulong) (tptr tulong); Eaddrof (Evar _r tulong) (tptr tulong);
    Etempvar idah tulong; Etempvar idal tulong; Etempvar _b tulong].

Lemma divmod96_symbol : Genv.find_symbol (Clight.genv_genv ge0) _div_mod_96_64 =
  Some (jet_symbol_block _div_mod_96_64).
Proof. vm_compute; reflexivity. Qed.
Lemma divmod96_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _div_mod_96_64) Ptrofs.zero) = Some (Internal f_div_mod_96_64).
Proof. vm_compute; reflexivity. Qed.

Lemma call_divmod128_helper e le m mf idq idah idal bq br ah al b :
  e!_div_mod_96_64 = None -> e!idq = Some (bq,tulong) -> e!_r = Some (br,tulong) ->
  le!idah = Some (Vlong ah) -> le!idal = Some (Vlong al) -> le!_b = Some (Vlong b) ->
  Clight2.eval_funcall ge0 m (Internal f_div_mod_96_64)
    [Vptr bq Ptrofs.zero; Vptr br Ptrofs.zero; Vlong ah; Vlong al; Vlong b] E0 mf Vundef ->
  Clight2.exec_stmt ge0 e le m (divmod128_helper_call idq idah idal) E0 le mf Out_normal.
Proof.
  intros HE HQ HR HA HAL HB Hcall.
  eapply exec_Scall with (vf := Vptr (jet_symbol_block _div_mod_96_64) Ptrofs.zero)
    (vargs := [Vptr bq Ptrofs.zero; Vptr br Ptrofs.zero; Vlong ah; Vlong al; Vlong b])
    (f := Internal f_div_mod_96_64) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + apply eval_Evar_global; [exact HE|apply divmod96_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof, eval_Evar_local; exact HQ.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof, eval_Evar_local; exact HR.
      * reflexivity.
      * eapply eval_Econs.
        -- apply eval_Etempvar; exact HA.
        -- reflexivity.
        -- eapply eval_Econs.
           ++ apply eval_Etempvar; exact HAL.
           ++ reflexivity.
           ++ eapply eval_Econs; [apply eval_Etempvar; exact HB|reflexivity|apply eval_Enil].
  - apply divmod96_funct.
  - reflexivity.
  - exact Hcall.
Qed.

Lemma eval_divmod128_local e le m id bb w : e!id = Some (bb,tulong) ->
  Mem.load Mint64 m bb 0 = Some (Vlong w) ->
  eval_expr ge0 e le m (Evar id tulong) (Vlong w).
Proof.
  intros HE HL. eapply eval_Elvalue.
  - apply eval_Evar_local; exact HE.
  - apply deref_loc_value with (chunk := Mint64); [reflexivity|exact HL].
Qed.
