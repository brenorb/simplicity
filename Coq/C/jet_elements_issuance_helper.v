(** The tag-dispatched static Elements issuance helpers (reissuanceBlinding,
    newIssuanceContract, reissuanceEntropy, issuanceAssetAmt): a bit testing
    the issuance type, then a helper on a field of the issuance or padding. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_uint32_array_init C.jet_application_sep.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval C.jet_elements_effects.
Require Import C.jet_output_layout_step C.jet_wide C.jet_wide_spec C.jet_elements_steps C.jet_elements_env_load C.jet_elements_write32s_layout C.jet_elements_hash_write C.jet_elements_call.
Require C.jets.
Require Import C.jet_elements_transport C.jet_elements_indexed_exec C.jet_elements_hash_helpers C.jet_elements_indexed_ptr C.jet_elements_asset_helper C.jet_elements_amt_helper.
Require Import C.jet_elements_indexed_scalar.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.



Lemma elements_assetIssuance_type : elements_field_at _assetIssuance _type 272.
Proof. vm_compute; reflexivity. Qed.

(** [t'2 = issuance->type; t'1 = writeBit(dst, K op t'2);
     if (t'1) HELPER(dst, PEXPR) else skipBits(dst, N)] *)
Definition issuance_tagged_fun (op : binary_operation) (k : int) (pexpr : expr) (cid : ident) (pt : type)
    (n : Z) : function :=
  {| fn_return := tvoid;
     fn_callconv := cc_default;
     fn_params := ((_dst, (tptr (Tstruct _frameItem noattr))) ::
                   (_issuance, (tptr (Tstruct _assetIssuance noattr))) :: nil);
     fn_vars := nil;
     fn_temps := ((_t'1, tbool) :: (_t'2, tint) :: nil);
     fn_body :=
       Ssequence
         (Ssequence
           (Sset _t'2
             (Efield (Ederef (Etempvar _issuance (tptr (Tstruct _assetIssuance noattr)))
               (Tstruct _assetIssuance noattr)) _type tint))
           (Scall (Some _t'1)
             (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default))
             ((Etempvar _dst (tptr (Tstruct _frameItem noattr))) ::
              (Ebinop op (Econst_int k tint) (Etempvar _t'2 tint) tint) :: nil)))
         (Sifthenelse (Etempvar _t'1 tbool)
           (Scall None
             (Evar cid (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr pt) Tnil)) tvoid cc_default))
             ((Etempvar _dst (tptr (Tstruct _frameItem noattr))) :: pexpr :: nil))
           (elements_skip_stmt n)) |}.

Definition issuance_tagged_cells (b : bool) (n : Z) (pcells : list Cell) : list Cell :=
  [Some b] ++ (if b then pcells else repeat None (Z.to_nat n)).

Theorem eval_elements_issuance_tagged (op : binary_operation) (k : int) (pexpr : expr) (cid : ident)
    (pt : type) (cf : function) (n : Z) (b : int -> bool) (pcells : list Cell)
    m bi ibase bf base bw edge cursor ty pofs :
  (forall t mm, sem_binary_operation elements_ge op (Vint k) tint (Vint t) tint mm = Some (Val.of_bool (b t))) ->
  typeof pexpr = tptr pt ->
  Genv.find_symbol (Clight.genv_genv elements_ge) cid = Some (elements_symbol_block cid) ->
  Genv.find_funct (Clight.genv_genv elements_ge) (Vptr (elements_symbol_block cid) Ptrofs.zero) =
    Some (Internal cf) ->
  type_of_fundef (Internal cf) =
    Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr pt) Tnil)) tvoid cc_default ->
  1 <= n <= 1000 ->
  0 <= ibase -> ibase + 280 <= Ptrofs.max_unsigned ->
  out_sep bf base bw edge cursor (1 + n) bi ibase (ibase + 280) ->
  Mem.load Mint32 m bi (ibase + 272) = Some (Vint ty) ->
  write_frame_at m bf base bw edge cursor (1 + n) ->
  (forall e le m', le!_issuance = Some (Vptr bi (Ptrofs.repr ibase)) ->
    eval_expr elements_ge e le m' pexpr (Vptr bi (Ptrofs.repr pofs))) ->
  (b ty = true -> forall mb,
    (forall chunk o, ibase <= o -> o + size_chunk chunk <= ibase + 280 ->
      Mem.load chunk mb bi o = Mem.load chunk m bi o) ->
    write_frame_at mb bf base bw edge (cursor - 1) n ->
    exists me, Clight2.eval_funcall elements_ge mb (Internal cf)
      [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr pofs)] E0 me Vundef /\
      write_effect mb me bf base bw edge (cursor - 1) n pcells) ->
  exists mf,
    Clight2.eval_funcall elements_ge m (Internal (issuance_tagged_fun op k pexpr cid pt n))
      [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr ibase)] E0 mf Vundef /\
    write_effect m mf bf base bw edge cursor (1 + n) (issuance_tagged_cells (b ty) n pcells).
Proof.
  intros Hcmp Hpty Hsym Hfun Hty Hn H0 HM HSep HT HF Hpexpr Hthen.
  pose proof HF as [_ [_ [_ [HCur _]]]].
  set (b0 := b ty) in *.
  assert (HF1 : write_frame_at m bf base bw edge cursor 1).
  { eapply write_frame_at_shorter; [|exact HF]. lia. }
  destruct (elements_writeBit_step m bf base bw edge cursor b0 HF1) as (mb & HCallB & E1).
  assert (HFb : write_frame_at mb bf base bw edge (cursor - 1) n).
  { eapply write_frame_at_after_effect with (cells := [Some b0]); [reflexivity|lia|exact HF|exact E1]. }
  assert (HLoadB : forall chunk o, ibase <= o -> o + size_chunk chunk <= ibase + 280 ->
    Mem.load chunk mb bi o = Mem.load chunk m bi o).
  { intros chunk o Hlo Hhi.
    eapply write_effect_env_load with (bf := bf) (base := base) (bw := bw) (edge := edge)
      (cursor := cursor) (cursor0 := cursor) (count0 := 1 + n) (n := 1) (cells := [Some b0])
      (lo := ibase) (hi := ibase + 280); [lia|lia|lia|lia|exact E1|exact HSep|exact Hlo|exact Hhi]. }
  set (f := issuance_tagged_fun op k pexpr cid pt n).
  set (le0 := PTree.set _issuance (Vptr bi (Ptrofs.repr ibase))
    (PTree.set _dst (Vptr bf (Ptrofs.repr base)) (create_undef_temps (fn_temps f)))).
  set (le1 := PTree.set _t'2 (Vint ty) le0).
  set (le2 := PTree.set _t'1 (Vint (conf_bit_int b0)) le1).
  assert (HD2 : le2!_dst = Some (Vptr bf (Ptrofs.repr base))).
  { unfold le2, le1, le0. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate. apply PTree.gss. }
  assert (HI2 : le2!_issuance = Some (Vptr bi (Ptrofs.repr ibase))).
  { unfold le2, le1, le0. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate. apply PTree.gss. }
  assert (HTail : exists mf,
    Clight2.exec_stmt elements_ge empty_env le2 mb
      (if b0 then
         Scall None
           (Evar cid (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr pt) Tnil)) tvoid cc_default))
           ((Etempvar _dst (tptr (Tstruct _frameItem noattr))) :: pexpr :: nil)
       else elements_skip_stmt n) E0 le2 mf Out_normal /\
    write_effect mb mf bf base bw edge (cursor - 1) n (if b0 then pcells else repeat None (Z.to_nat n))).
  { destruct b0 eqn:Hb0.
    - destruct (Hthen eq_refl mb HLoadB HFb) as (me & HC & E2).
      exists me. split; [|exact E2].
      change le2 with (set_opttemp None Vundef le2) at 2.
      eapply exec_Scall with (vf := Vptr (elements_symbol_block cid) Ptrofs.zero) (f := Internal cf)
        (vargs := [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr pofs)]) (vres := Vundef).
      + reflexivity.
      + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact Hsym]|
          apply deref_loc_reference; reflexivity].
      + eapply eval_Econs; [apply eval_Etempvar; exact HD2|reflexivity|].
        eapply eval_Econs; [exact (Hpexpr empty_env le2 mb HI2)|rewrite Hpty; reflexivity|apply eval_Enil].
      + exact Hfun.
      + exact Hty.
      + exact HC.
    - assert (HFb' : write_frame_at mb bf base bw edge (cursor - 1) (Z.of_nat (Z.to_nat n))).
      { rewrite Z2Nat.id by lia. exact HFb. }
      destruct (elements_skipBits_step mb bf base bw edge (cursor - 1) (Z.to_nat n) HFb') as (me & HCallS & E2).
      exists me. split.
      + unfold elements_skip_stmt.
        assert (Hargs : eval_exprlist elements_ge empty_env le2 mb
          [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr n) tint]
          (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil))
          [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr (Z.of_nat (Z.to_nat n)))]).
        { eapply eval_Econs; [apply eval_Etempvar; exact HD2|reflexivity|].
          eapply eval_Econs; [apply eval_Econst_int| |apply eval_Enil].
          rewrite Z2Nat.id by lia. apply elements_cast_const'; lia. }
        exact (exec_elements_helper_call empty_env le2 mb None _skipBits jets.f_skipBits
          _ _ _ _ _ _ me ltac:(unfold elements_core_helpers; simpl; tauto) ltac:(reflexivity) Hargs
          ltac:(reflexivity) HCallS).
      + rewrite <- (Z2Nat.id n) at 1 by lia. exact E2. }
  destruct HTail as (mf & HT' & E2).
  exists mf. split.
  - eapply eval_funcall_internal with (e := empty_env)
      (le1 := le0) (le2 := le2) (m1 := m) (m2 := mf) (out := Out_normal).
    + constructor.
      * constructor.
      * change (list_norepet [_dst; _issuance]). unfold _dst, _issuance.
        repeat constructor; simpl; intuition discriminate.
      * intros i j HI HJ Hij. cbn in HI, HJ.
        repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
          first [contradiction | vm_compute in Hij; discriminate | congruence].
      * constructor.
      * reflexivity.
    + unfold f, issuance_tagged_fun; cbn [fn_body].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le2).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le1).
        -- apply exec_set.
           eapply eval_elements_field_value with (sid := _assetIssuance) (delta := 272) (chunk := Mint32).
           ++ reflexivity.
           ++ exact elements_assetIssuance_type.
           ++ reflexivity.
           ++ apply eval_elements_deref_struct. unfold le0. apply PTree.gss.
           ++ rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HT].
        -- change le2 with (set_opttemp (Some _t'1) (Vint (conf_bit_int b0)) le1).
           eapply exec_elements_helper_call with (id := _writeBit) (f := jets.f_writeBit)
             (vargs := [Vptr bf (Ptrofs.repr base); Vint (conf_bit_int b0)]) (vres := Vint (conf_bit_int b0)).
           ++ unfold elements_core_helpers. simpl. tauto.
           ++ reflexivity.
           ++ eapply eval_Econs.
              ** apply eval_Etempvar. unfold le1, le0. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate. apply PTree.gss.
              ** reflexivity.
              ** eapply eval_Econs with (v1 := Val.of_bool b0).
                 --- eapply eval_Ebinop with (v1 := Vint k) (v2 := Vint ty).
                     +++ apply eval_Econst_int.
                     +++ apply eval_Etempvar. unfold le1. apply PTree.gss.
                     +++ apply Hcmp.
                 --- apply elements_bool_cast.
                 --- apply eval_Enil.
           ++ reflexivity.
           ++ exact HCallB.
      * eapply exec_Sifthenelse with (v1 := Vint (conf_bit_int b0)) (b := b0).
        -- apply eval_Etempvar. unfold le2. apply PTree.gss.
        -- destruct b0; reflexivity.
        -- destruct b0; exact HT'.
    + reflexivity.
    + reflexivity.
  - unfold issuance_tagged_cells.
    assert (HLt : Z.of_nat (length (if b0 then pcells else repeat None (Z.to_nat n))) = n -> True) by auto.
    exact (write_effect_seq m mb mf bf base bw edge cursor 1 n [Some b0] _ eq_refl ltac:(lia) HF E1 E2).
Qed.
