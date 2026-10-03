(** Actual Bitcoin-program calls writing a 256-bit hash: the direct write32s
    call used by script_cmr / transaction_id and the static helper writeHash
    used by the remaining hash getters.  Layout facts are derived from the
    initial memory, with the hash words separated from the written output. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_uint32_array_init C.jet_application_sep.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_field_eval C.jet_bitcoin_effects.
Require Import C.jet_bitcoin_write32s_exec C.jet_bitcoin_write32s_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge.
Set Default Timeout 10.

Lemma bitcoin_write32s_symbol :
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) _write32s = Some (bitcoin_symbol_block _write32s).
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_write32s_funct :
  Genv.find_funct (Clight.genv_genv bitcoin_ge)
    (Vptr (bitcoin_symbol_block _write32s) Ptrofs.zero) = Some (Internal f_write32s).
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_writeHash_symbol :
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) _writeHash = Some (bitcoin_symbol_block _writeHash).
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_writeHash_funct :
  Genv.find_funct (Clight.genv_genv bitcoin_ge)
    (Vptr (bitcoin_symbol_block _writeHash) Ptrofs.zero) = Some (Internal f_writeHash).
Proof. vm_compute; reflexivity. Qed.

(** The 256 cells of a hash given as eight uint32 words. *)
Definition hash_cells (xs : list int) : list Cell := uint32_word_cells xs.

Lemma hash_cells_length xs : length (hash_cells xs) = (32 * length xs)%nat.
Proof. apply uint32_word_cells_length. Qed.

Lemma hash_cells_length_Z xs : length xs = 8%nat -> Z.of_nat (length (hash_cells xs)) = 256.
Proof. intros H. rewrite hash_cells_length, H. reflexivity. Qed.

(** An interval separated from the whole write is separated from every word. *)
Lemma out_sep_words bf base bw edge cursor count b lo n j :
  (j < n)%nat ->
  out_sep bf base bw edge cursor count b lo (lo + 4 * Z.of_nat n) ->
  out_sep bf base bw edge cursor count b (lo + 4 * Z.of_nat j) (lo + 4 * Z.of_nat j + 4).
Proof.
  intros Hj [Hf Hw]. split.
  - destruct Hf as [H|[H|H]]; [left; exact H|right; left|right; right]; lia.
  - destruct Hw as [H|[H|H]]; [left; exact H|right; left|right; right]; lia.
Qed.

(** write32s itself, called with the eight words of a hash. *)
Theorem eval_bitcoin_write_hash_array m bi input bf base bw edge cursor xs :
  length xs = 8%nat ->
  0 <= input -> input + 32 <= Ptrofs.max_unsigned ->
  out_sep bf base bw edge cursor 256 bi input (input + 32) ->
  uint32_array_at m bi input xs ->
  write_frame_at m bf base bw edge cursor 256 ->
  exists mf,
    Clight2.eval_funcall bitcoin_ge m (Internal f_write32s)
      [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr input); Vlong (Int64.repr 8)]
      E0 mf Vundef /\
    write_effect m mf bf base bw edge cursor 256 (hash_cells xs).
Proof.
  intros HL HI HM HSep HA HF.
  assert (HN : Z.of_nat (length xs) = 8) by (rewrite HL; reflexivity).
  assert (Hcount : 32 * Z.of_nat (length xs) = 256) by lia.
  assert (HSep' : out_sep bf base bw edge cursor (32 * Z.of_nat (length xs)) bi input
    (input + 4 * Z.of_nat (length xs))).
  { rewrite Hcount. replace (input + 4 * Z.of_nat (length xs)) with (input + 32) by lia. exact HSep. }
  rewrite <- Hcount in HF.
  destruct (eval_write32s_layout m bi input bf base bw edge cursor xs
      HI ltac:(rewrite HN; lia)
      (fun j Hj => out_sep_words bf base bw edge cursor (32 * Z.of_nat (length xs)) bi input
        (length xs) j Hj HSep')
      HA HF)
    as (mf & HCall & HCells & HPrefix & HFields & HLoads & HPerm & HValid).
  exists mf. rewrite HN in HCall. split; [exact HCall|].
  assert (HE : write_effect m mf bf base bw edge cursor (32 * Z.of_nat (length xs)) (hash_cells xs)).
  { exact (conj HCells (conj HPrefix (conj HFields (conj HLoads (conj HPerm HValid))))). }
  rewrite Hcount in HE. exact HE.
Qed.
