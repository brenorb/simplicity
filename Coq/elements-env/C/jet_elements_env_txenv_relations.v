(** The [txEnv]-level relations of the Elements application jets
    ([genesis_block_hash], [current_index]) hold for the structure written
    by the real [simplicity_elements_build_txEnv] ([eval_build_txEnv]),
    when it is called with the genesis hash and input index of the logical
    environment. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Values Memory.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import C.jet_uint32_array_init C.jet_sha_add_n_calls C.jet_elements_prim.
Require Import C.jet_elements_genesis_hash_local C.jet_elements_current_index_local.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

Section Ready.
Variables (m : mem) (bD : block) (oD : Z) (e : Elements.env).
Hypothesis HoD : 0 <= oD /\ oD + 88 <= Ptrofs.max_unsigned.

Theorem el_ready_genesis_block_hash (G : list int) :
  G = hash256_reg (Elements.envGenesisBlock e) ->
  (forall j, (j < 8)%nat -> Mem.load Mint32 m bD (oD + 16 + 4 * Z.of_nat j) = Some (Vint (nth j G Int.zero))) ->
  elements_genesis_hash_env_rep m (Vptr bD (Ptrofs.repr oD)) e [(bD, oD + 16, oD + 48)].
Proof.
  intros -> HL. exists bD, oD. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [|reflexivity].
  apply u32_of_nth. intros i Hi. rewrite hash256_len in Hi. apply HL, Hi.
Qed.

Theorem el_ready_current_index :
  Z.of_nat (Elements.envIx e) <= 4294967295 ->
  Mem.load Mint64 m bD (oD + 80) = Some (Vlong (Int64.repr (Z.of_nat (Elements.envIx e)))) ->
  elements_current_index_env_rep m (Vptr bD (Ptrofs.repr oD)) e.
Proof.
  intros HIx HL. exists bD, oD, (Int64.repr (Z.of_nat (Elements.envIx e))).
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact HL|].
  apply Int64.unsigned_repr. change Int64.max_unsigned with 18446744073709551615. lia.
Qed.
End Ready.
