(** Execute the actual secp256k1_u128_mul wrapper from its writable lo/hi
    fields, deriving the umul128 call and final low-word store. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_u128_fields C.jet_umul128_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition u128_mul_temps br base a b := PTree.set _b (Vlong b) (PTree.set _a (Vlong a)
  (PTree.set _r (Vptr br (Ptrofs.repr base)) (create_undef_temps f_secp256k1_u128_mul.(fn_temps)))).

Lemma umul128_symbol : Genv.find_symbol (Clight.genv_genv ge0) _secp256k1_umul128 =
  Some (jet_symbol_block _secp256k1_umul128).
Proof. vm_compute; reflexivity. Qed.
Lemma umul128_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _secp256k1_umul128) Ptrofs.zero) = Some (Internal f_secp256k1_umul128).
Proof. vm_compute; reflexivity. Qed.

Theorem eval_u128_mul_layout m br base a b : frame_base_valid base ->
  Mem.valid_access m Mint64 br base Writable -> Mem.valid_access m Mint64 br (base + 8) Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_secp256k1_u128_mul)
      [Vptr br (Ptrofs.repr base); Vlong a; Vlong b] E0 mf Vundef /\
    Mem.load Mint64 mf br base = Some (Vlong (umul128_result_lo a b)) /\
    Mem.load Mint64 mf br (base + 8) = Some (Vlong (umul128_result_hi a b)) /\
    Int64.unsigned (umul128_result_hi a b) = (Int64.unsigned a * Int64.unsigned b) / Int64.modulus /\
    Int64.unsigned (umul128_result_lo a b) = (Int64.unsigned a * Int64.unsigned b) mod Int64.modulus /\
    (forall chunk bb addr, bb <> br \/ addr + size_chunk chunk <= base \/ base + 16 <= addr ->
      Mem.load chunk mf bb addr = Mem.load chunk m bb addr) /\
    (forall bb addr kind p, Mem.perm m bb addr kind p -> Mem.perm mf bb addr kind p) /\
    Mem.nextblock mf = Mem.nextblock m.
Proof.
  intros HB PL PH.
  set (hiPtr := Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 8)).
  assert (HPHi : Ptrofs.unsigned hiPtr = base + 8).
  { unfold hiPtr. apply frame_field_address; [exact HB|lia]. }
  destruct (eval_umul128_layout m br hiPtr a b ltac:(rewrite HPHi; exact PH))
    as (mi & HC & HH & Hhi & Hlo & Hmem & Hperm & Hnext).
  assert (PLi : Mem.valid_access mi Mint64 br base Writable).
  { destruct PL as [P A]. split; [|exact A]. intros addr Haddr. apply Hperm, P; exact Haddr. }
  destruct (Mem.valid_access_store mi Mint64 br base (Vlong (umul128_result_lo a b)) PLi) as [mf HS].
  set (le0 := u128_mul_temps br base a b).
  set (le1 := PTree.set _t'1 (Vlong (umul128_result_lo a b)) le0).
  exists mf. split.
  - eapply eval_funcall_internal with (e := PTree.empty _) (le1 := le0) (le2 := le1)
      (m1 := m) (m2 := mf) (out := Out_normal).
    + constructor.
      * constructor.
      * change (list_norepet [_r; _a; _b]). vm_compute.
        repeat (apply list_norepet_cons; [simpl; intuition discriminate|]). constructor.
      * change (list_disjoint [_r; _a; _b] [_t'1]). vm_compute; intuition congruence.
      * constructor.
      * reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mi).
      * eapply exec_Scall with (vf := Vptr (jet_symbol_block _secp256k1_umul128) Ptrofs.zero)
          (vargs := [Vlong a; Vlong b; Vptr br hiPtr]) (f := Internal f_secp256k1_umul128)
          (vres := Vlong (umul128_result_lo a b)).
        -- reflexivity.
        -- eapply eval_Elvalue.
           ++ apply eval_Evar_global; [reflexivity|exact umul128_symbol].
           ++ apply deref_loc_reference; reflexivity.
        -- eapply eval_Econs.
           ++ apply eval_Etempvar. unfold le0, u128_mul_temps. umul128_lookup.
           ++ reflexivity.
           ++ eapply eval_Econs.
              ** apply eval_Etempvar. unfold le0, u128_mul_temps. umul128_lookup.
              ** reflexivity.
              ** eapply eval_Econs.
                 --- apply eval_Eaddrof. apply (eval_u128_field_lvalue Datatypes.true _r).
                     unfold le0, u128_mul_temps. umul128_lookup.
                 --- reflexivity.
                 --- apply eval_Enil.
        -- exact umul128_funct.
        -- reflexivity.
        -- exact HC.
      * eapply exec_Sassign with (loc := br) (ofs := Ptrofs.add (Ptrofs.repr base) Ptrofs.zero)
          (bf := Full) (v2 := Vlong (umul128_result_lo a b)) (v := Vlong (umul128_result_lo a b)).
        -- apply (eval_u128_field_lvalue Datatypes.false _r). unfold le1, le0, u128_mul_temps. umul128_lookup.
        -- apply eval_Etempvar. unfold le1; apply PTree.gss.
        -- reflexivity.
        -- apply assign_loc_value with (chunk := Mint64); [reflexivity|].
           unfold Mem.storev. change Ptrofs.zero with (Ptrofs.repr 0).
           rewrite (frame_field_address base 0 HB ltac:(lia)), Z.add_0_r. exact HS.
    + reflexivity.
    + reflexivity.
  - split.
    + exact (Mem.load_store_same Mint64 mi br base (Vlong (umul128_result_lo a b)) mf HS).
    + split.
      * erewrite Mem.load_store_other; [rewrite <- HPHi; exact HH|exact HS|right; right; cbn; lia].
      * split; [exact Hhi|]. split; [exact Hlo|]. split.
        -- intros chunk bb addr Hout. erewrite Mem.load_store_other; [apply Hmem|exact HS|].
           ++ rewrite HPHi. destruct Hout as [N|[L|R]];
                [left; exact N|right; left; lia|right; right; lia].
           ++ destruct Hout as [N|[L|R]];
                [left; exact N|right; left; exact L|right; right; cbn; lia].
        -- split.
           ++ intros bb addr kind p HP. eapply Mem.perm_store_1; [exact HS|apply Hperm; exact HP].
           ++ rewrite (Mem.nextblock_store _ _ _ _ _ _ HS). exact Hnext.
Qed.
