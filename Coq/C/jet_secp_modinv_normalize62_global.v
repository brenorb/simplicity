(** Apply original normalize_62 to caller-owned storage using the actual
    readonly field-modulus global. Preserve its complete 48-byte readiness
    predicate, including the sixth inverse-coefficient word. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_secp_modinv_normalize62_exec C.jet_secp_modinfo_fe_global.
Require Import C.jet_secp_linkage C.jets_secp C.jet_sx_mem C.jet_secp_fe_nv.
Require Import C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_modinfo_fe_copy.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge modinfo_fe_block.

Definition field_norm62_rho (w : nat -> int64) (sign : int64) n :=
 if Nat.ltb n 5 then w n else
 if Nat.ltb n 10 then modinfo_fe_limb (n-5)%nat else sign.

Lemma field_norm62_input_words w sign : words5 (field_norm62_rho w sign) = words5 w.
Proof. reflexivity. Qed.
Lemma field_norm62_output_words w sign :
 words5 (norm62_machine (field_norm62_rho w sign)
   (fun i => field_norm62_rho w sign (5+i)%nat) (field_norm62_rho w sign 10%nat)) =
 words5 (norm62_machine w modinfo_fe_limb sign).
Proof. reflexivity. Qed.

Lemma field_norm62_initial_modulus w sign m : modinfo_fe_global_rep m ->
 norm62_modulus_at m modinfo_fe_block (fun i => field_norm62_rho w sign (5+i)%nat).
Proof.
 intros (Valid & Read & Loads). split.
 - intros pos Range; apply Read;lia.
 - intros i I. destruct i as [|[|[|[|[|i]]]]]; try lia; apply Loads; reflexivity.
Qed.

Theorem eval_field_norm62_with_global w sign m br : br <> modinfo_fe_block ->
 fe_at m br 0 (words5 w) -> Mem.range_perm m br 0 40 Cur Freeable ->
 modinfo_fe_global_rep m -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_normalize_62)
   [Vptr br Ptrofs.zero; Vlong sign; Vptr modinfo_fe_block Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 (norm62_machine w modinfo_fe_limb sign)) /\
 Mem.range_perm mf br 0 40 Cur Freeable /\ modinfo_fe_global_rep mf /\
 lframe (norm62_outside br modinfo_fe_block) m mf.
Proof.
 intros NE Field Free Global.
 destruct (eval_norm62_from_storage (field_norm62_rho w sign) m br modinfo_fe_block NE
   ltac:(rewrite field_norm62_input_words; exact Field) Free
   (field_norm62_initial_modulus w sign m Global)) as (mf & Call & FieldF & FreeF & ModulusF & Frame).
 rewrite field_norm62_output_words in FieldF.
 destruct Global as (Valid & Read & Loads).
 destruct ModulusF as (ReadF & WordsF).
 assert (Outside : forall pos, 40 <= pos -> norm62_outside br modinfo_fe_block modinfo_fe_block pos).
 { intros pos P. split; [left;congruence|right;right;exact P]. }
 assert (Metadata : modinfo_fe_global_rep mf).
 { split; [exact ((proj2 (proj2 Frame)) _ Valid)|]. split.
   - intros pos Range. destruct (Z_lt_dec pos 40).
     + apply ReadF;lia.
     + eapply (proj1 (proj2 Frame)); [exact Valid|apply Outside;lia|apply Read;exact Range].
   - intros i v At. destruct i as [|[|[|[|[|[|i]]]]]];
       try (destruct i; discriminate At).
     + injection At as <-. exact (WordsF 0%nat ltac:(lia)).
     + injection At as <-. exact (WordsF 1%nat ltac:(lia)).
     + injection At as <-. exact (WordsF 2%nat ltac:(lia)).
     + injection At as <-. exact (WordsF 3%nat ltac:(lia)).
     + injection At as <-. exact (WordsF 4%nat ltac:(lia)).
     + change (Mem.load Mint64 mf modinfo_fe_block 40 = Some (Vlong v)).
       rewrite (proj1 Frame Mint64 modinfo_fe_block 40 Valid).
       * exact (Loads 5%nat v At).
       * intros pos Range;apply Outside. change (size_chunk Mint64) with 8 in Range;lia. }
 exists mf. exact (conj Call (conj FieldF (conj FreeF (conj Metadata Frame)))).
Qed.
