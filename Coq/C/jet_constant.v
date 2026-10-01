(** The actual constant jet bodies and their canonical Simplicity programs.
    [false] selects LowN, [true] selects HighN in CoreJets.hs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Globalenvs.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_spec C.jet_wide C.jet_wide_spec.
Import Values Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Inductive constant_size := C1 | C8 | C16 | C32 | C64.
Definition constant_log s : nat :=
  match s with C1 => 0%nat | C8 => 3%nat | C16 => 4%nat | C32 => 5%nat | C64 => 6%nat end.
Definition constant_bits s : Z :=
  match s with C1 => 1 | C8 => 8 | C16 => 16 | C32 => 32 | C64 => 64 end.
Definition constant_jet s (high : bool) :=
  match s, high with
  | C1, Datatypes.false => f_simplicity_low_1 | C1, Datatypes.true => f_simplicity_high_1
  | C8, Datatypes.false => f_simplicity_low_8 | C8, Datatypes.true => f_simplicity_high_8
  | C16, Datatypes.false => f_simplicity_low_16 | C16, Datatypes.true => f_simplicity_high_16
  | C32, Datatypes.false => f_simplicity_low_32 | C32, Datatypes.true => f_simplicity_high_32
  | C64, Datatypes.false => f_simplicity_low_64 | C64, Datatypes.true => f_simplicity_high_64
  end.
Definition constant_spec s (high : bool) {term : Alg.Core.Algebra} :
    @Alg.Core.domain term Ty.Unit (Word (constant_log s)) :=
  if high then @Word.fill Ty.Unit Bit (constant_log s) term (@Bit.true Ty.Unit term)
  else @Word.zero (constant_log s) term.
Definition constant_writer s := match s with
  | C1 => f_writeBit | C8 => f_simplicity_write8
  | C16 => wide_writer W16 | C32 => wide_writer W32 | C64 => wide_writer W64 end.
Definition constant_writer_id s := match s with
  | C1 => _writeBit | C8 => _simplicity_write8
  | C16 => wide_writer_id W16 | C32 => wide_writer_id W32 | C64 => wide_writer_id W64 end.
Definition constant_arg_type s := match s with C1 => tbool | C8 => tuchar | _ => tulong end.
Definition constant_return_type s := match s with C1 => tbool | _ => tvoid end.
Definition constant_unsigned s (high : bool) : Z := if high then 2 ^ constant_bits s - 1 else 0.
Definition constant_value s high := match s with
  | C1 | C8 => Vint (Int.repr (constant_unsigned s high))
  | _ => Vlong (Int64.repr (constant_unsigned s high)) end.
Definition constant_return s high := match s with C1 => constant_value s high | _ => Vundef end.
Definition constant_expr s (high : bool) := if high then match s with
  | C1 => Econst_int Int.one tint
  | C8 => Econst_int (Int.repr 255) tint
  | C16 => Econst_int (Int.repr 65535) tint
  | C32 => Econst_int (Int.repr (-1)) tuint
  | C64 => Econst_long (Int64.repr (-1)) tulong end
  else Econst_int Int.zero tint.
Definition constant_raw s (high : bool) := if high then match s with
  | C1 => Vint Int.one | C8 => Vint (Int.repr 255)
  | C16 => Vint (Int.repr 65535) | C32 => Vint (Int.repr (-1))
  | C64 => Vlong (Int64.repr (-1)) end else Vint Int.zero.

Lemma constant_bits_bounds s : 1 <= constant_bits s <= 64.
Proof. destruct s; cbn; lia. Qed.
Lemma constant_bitSize s : Z.of_nat (Translate.bitSize (Word (constant_log s))) = constant_bits s.
Proof. destruct s; reflexivity. Qed.
Lemma constant_spec_parametric s high : Alg.Core.Parametric (@constant_spec s high).
Proof.
  intros alg1 alg2 R. unfold constant_spec. destruct high.
  - apply Word.fill_Parametric. apply Bit.true_Parametric.
  - apply Word.zero_Parametric.
Qed.
Lemma constant_writer_symbol s : Genv.find_symbol (Clight.genv_genv ge0) (constant_writer_id s) =
  Some (jet_symbol_block (constant_writer_id s)).
Proof. destruct s; vm_compute; reflexivity. Qed.
Lemma constant_writer_funct s : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block (constant_writer_id s)) Ptrofs.zero) = Some (Internal (constant_writer s)).
Proof. destruct s; vm_compute; reflexivity. Qed.
Lemma constant_cast s high m :
  sem_cast (constant_raw s high) (typeof (constant_expr s high)) (constant_arg_type s) m =
    Some (constant_value s high).
Proof.
  destruct s, high; try reflexivity.
  change (Some (Vlong (Int64.repr (-1))) = Some (Vlong (Int64.repr 18446744073709551615))).
  f_equal. f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity.
Qed.

(** These are closed representation bridges, not exhaustive input enumeration. *)
Lemma constant_decode8 high :
  decode_word8 (Int64.repr (Int.unsigned (Int.repr (constant_unsigned C8 high)))) =
    @constant_spec C8 high Alg.CoreFunSem tt.
Proof. destruct high; vm_compute; reflexivity. Qed.
Lemma constant_decode16 high :
  decode_wide W16 (Int64.zero_ext 16 (Int64.repr (constant_unsigned C16 high))) =
    @constant_spec C16 high Alg.CoreFunSem tt.
Proof. destruct high; vm_compute; reflexivity. Qed.
Lemma constant_decode32 high :
  decode_wide W32 (Int64.zero_ext 32 (Int64.repr (constant_unsigned C32 high))) =
    @constant_spec C32 high Alg.CoreFunSem tt.
Proof. destruct high; vm_compute; reflexivity. Qed.
Lemma constant_decode64 high :
  decode_wide W64 (Int64.zero_ext 64 (Int64.repr (constant_unsigned C64 high))) =
    @constant_spec C64 high Alg.CoreFunSem tt.
Proof. destruct high; vm_compute; reflexivity. Qed.
